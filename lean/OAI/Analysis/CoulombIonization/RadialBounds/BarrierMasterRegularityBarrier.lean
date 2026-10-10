import Mathlib
import OAI.Analysis.CoulombIonization.Variational.BoundedDensityPotential
import OAI.Analysis.CoulombIonization.Ionization.MasterJointPosterior
import OAI.Analysis.CoulombIonization.RadialBounds.Average

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierMasterRegularity_barrier_scope

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators ContDiff Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation

lemma masterKernel_global_bound {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) {g : Space → ℝ}
    (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖masterKernel c₁ r₀ s g x y‖ ≤ C := by
  have hc2 : HasCompactSupport (fun x => (g x)^2) := hcg.mul_left
  obtain ⟨z,hz⟩ := (hg.pow 2).norm.exists_forall_ge_of_hasCompactSupport hc2.norm
  let δ := c₁*r₀^(1+masterExponent)
  have hδ : 0 < δ := mul_pos hc (Real.rpow_pos_of_pos hr _)
  refine ⟨δ⁻¹^3*‖(g z)^2‖,by positivity,fun x y => ?_⟩
  have hi : (masterWidth c₁ r₀ s x)⁻¹ ≤ δ⁻¹ := by
    apply inv_anti₀ hδ
    exact masterWidth_lower hc.le hr hrs x
  rw [masterKernel,scaledRealPacket_sq (masterWidth_pos hc hr hs x),norm_mul,
    Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (masterWidth_pos hc hr hs x).le) 3)]
  exact mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr (masterWidth_pos hc hr hs x).le) hi 3)
    (hz _) (norm_nonneg _) (by positivity)

attribute [local irreducible] masterKernel masterWidth scaledRealPacket

def masterConfigurationDensity {N : ℕ} (c₁ r₀ s : ℝ) (g : Space → ℝ)
    (z : Configuration N) (y : Space) : ℝ := ∑ i, masterKernel c₁ r₀ s g (z i) y

lemma masterConfigurationDensity_measurable {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry (masterConfigurationDensity (N := N) c₁ r₀ s g)) := by
  have hm (i : Fin N) : Measurable (fun p : Configuration N × Space =>
      masterKernel c₁ r₀ s g (p.1 i) p.2) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.comp
      (f := fun p : Configuration N × Space => (p.1 i,p.2))
      (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)
  exact Finset.measurable_sum Finset.univ (fun i _ => hm i)

lemma masterConfigurationDensity_continuous {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g)
    (z : Configuration N) : Continuous (masterConfigurationDensity c₁ r₀ s g z) := by
  have ht (i : Fin N) : Continuous (fun y : Space => masterKernel c₁ r₀ s g (z i) y) :=
    (masterKernel_joint_continuous hc hr hs hg).comp
      (f := fun y : Space => (z i,y)) (continuous_const.prodMk continuous_id)
  exact continuous_finsetSum Finset.univ (fun i _ => ht i)

lemma masterConfigurationDensity_bound {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z y, ‖masterConfigurationDensity (N := N) c₁ r₀ s g z y‖ ≤ C := by
  obtain ⟨C,hCn,hC⟩ := masterKernel_global_bound hc hr hs hrs hg hcg
  refine ⟨N*C,by positivity,fun z y => ?_⟩
  calc
    _ ≤ ∑ i : Fin N, ‖masterKernel c₁ r₀ s g (z i) y‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ => hC (z i) y)
    _ = N*C := by simp

lemma masterConfigurationDensity_deterministicBound {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    DeterministicLocalBound (masterConfigurationDensity (N := N) c₁ r₀ s g) := by
  obtain ⟨C,_,hC⟩ := masterConfigurationDensity_bound (N := N) hc hr hs hrs hg hcg
  exact fun _ _ => ⟨C,fun z y _ => hC z y⟩

lemma jointMasterPosterior_continuous {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (d : OriginalDatum N K ell j) :
    Continuous (jointMasterPosterior μ ell j c₁ r₀ s g d) := by
  exact average_continuous (masterConfigurationDensity_measurable hc hr hs hg)
    (masterConfigurationDensity_deterministicBound hc hr hs hrs hg hcg)
    (Eventually.of_forall (masterConfigurationDensity_continuous hc hr hs hg))

lemma jointMasterPosterior_global_bound {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d y, ‖jointMasterPosterior μ ell j c₁ r₀ s g d y‖ ≤ C := by
  obtain ⟨C,hCn,hC⟩ := masterConfigurationDensity_bound (N := N) hc hr hs hrs hg hcg
  refine ⟨C,hCn,fun d y => ?_⟩
  calc
    _ ≤ ∫ _ : Configuration N, C ∂originalRawKernel μ ell j d :=
      norm_integral_le_of_norm_le (integrable_const C) (Eventually.of_forall fun z => hC z y)
    _ = C := by simp

lemma jointMasterPosterior_deterministicBound {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    DeterministicLocalBound (jointMasterPosterior μ ell j c₁ r₀ s g) := by
  obtain ⟨C,_,hC⟩ := jointMasterPosterior_global_bound μ ell j hc hr hs hrs hg hcg
  exact fun _ _ => ⟨C,fun d y _ => hC d y⟩

end CoulombBarrier

end Work_BarrierMasterRegularity_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma masterKernel_scale_bound {c₁ r₀ s G : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) {g : Space → ℝ} (hG : ∀ z, (g z)^2 ≤ G)
    (x y : Space) :
    masterKernel c₁ r₀ s g x y ≤ (c₁*r₀^(1+masterExponent))⁻¹^3*G := by
  have hδ : 0 < c₁*r₀^(1+masterExponent) := mul_pos hc (Real.rpow_pos_of_pos hr _)
  have hi : (masterWidth c₁ r₀ s x)⁻¹ ≤ (c₁*r₀^(1+masterExponent))⁻¹ :=
    inv_anti₀ hδ (masterWidth_lower hc.le hr hrs x)
  rw [masterKernel,scaledRealPacket_sq (masterWidth_pos hc hr hs x)]
  exact mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr (masterWidth_pos hc hr hs x).le) hi 3)
    (hG _) (sq_nonneg _) (by positivity)

lemma jointMasterPosterior_scale_bound {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s G : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) {g : Space → ℝ}
    (hG : ∀ z, (g z)^2 ≤ G) (z : OriginalDatum N K ell j) (y : Space) :
    jointMasterPosterior μ ell j c₁ r₀ s g z y ≤ (N:ℝ)*(c₁*r₀^(1+masterExponent))⁻¹^3*G := by
  have hGn : 0 ≤ G := (sq_nonneg (g 0)).trans (hG 0)
  have hb (x : Configuration N) :
      ‖∑ i, masterKernel c₁ r₀ s g (x i) y‖ ≤ (N:ℝ)*(c₁*r₀^(1+masterExponent))⁻¹^3*G := by
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => masterKernel_nonneg c₁ r₀ s g (x i) y))]
    calc
      _ ≤ ∑ _i : Fin N, (c₁*r₀^(1+masterExponent))⁻¹^3*G :=
        Finset.sum_le_sum (fun i _ => masterKernel_scale_bound hc hr hs hrs hG (x i) y)
      _ = _ := by simp [mul_assoc]
  change (∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) y ∂originalRawKernel μ ell j z) ≤ _
  calc
    _ ≤ ‖∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) y ∂originalRawKernel μ ell j z‖ := by simpa only [Real.norm_eq_abs] using le_abs_self _
    _ ≤ ∫ _x : Configuration N, (N:ℝ)*(c₁*r₀^(1+masterExponent))⁻¹^3*G ∂originalRawKernel μ ell j z :=
      norm_integral_le_of_norm_le (integrable_const _) (ae_of_all _ hb)
    _ = _ := by simp

lemma initial_radius_factor {c r : ℝ} (hr : 0 < r) :
    (c*r^(1+masterExponent))⁻¹^3*r = c⁻¹^3*r^(-2-3*masterExponent) := by
  rw [mul_inv_rev,mul_pow]
  have hp : (r^(1+masterExponent))⁻¹^3*r = r^(-2-3*masterExponent) := by
    rw [←Real.rpow_neg hr.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = r^(-(1+masterExponent)*(3:ℝ))*r^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hr]; congr 1; ring
  calc
    _ = c⁻¹^3*((r^(1+masterExponent))⁻¹^3*r) := by ring
    _ = _ := by rw [hp]

theorem jointMasterPosterior_inner_difference {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s G : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) {g : Space → ℝ} (hg : Continuous g)
    (hG : ∀ z, (g z)^2 ≤ G) (z : OriginalDatum N K ell j) (x y : Space)
    (hx : ‖x‖ ≤ (11/10)*r₀) (hy : ‖y‖ ≤ (11/10)*r₀) :
    |innerPotential r₀ (jointMasterPosterior μ ell j c₁ r₀ s g z) x-
      innerPotential r₀ (jointMasterPosterior μ ell j c₁ r₀ s g z) y| ≤
      (16*Real.pi*(N:ℝ)*G*c₁⁻¹^3)*r₀^(-2-3*masterExponent)*‖x-y‖ := by
  let ρ := (ball (0:Space) r₀).indicator (jointMasterPosterior μ ell j c₁ r₀ s g z)
  have hGn : 0 ≤ G := (sq_nonneg (g 0)).trans (hG 0)
  have hM : 0 ≤ (N:ℝ)*(c₁*r₀^(1+masterExponent))⁻¹^3*G := by positivity
  have hm : Measurable ρ := ((jointMasterPosterior_measurable μ ell j hc hr hs hg).comp
    (measurable_const.prodMk measurable_id)).indicator measurableSet_ball
  have hn : ∀ y, 0 ≤ ρ y := indicator_nonneg (fun y _ => jointMasterPosterior_nonneg μ ell j c₁ r₀ s g z y)
  have hb : ∀ y, ρ y ≤ (N:ℝ)*(c₁*r₀^(1+masterExponent))⁻¹^3*G :=
    fun y => by
      by_cases hy : y ∈ ball (0:Space) r₀
      · simpa only [ρ,indicator_of_mem hy] using jointMasterPosterior_scale_bound μ ell j hc hr hs hrs hG z y
      · simpa only [ρ,indicator_of_notMem hy] using hM
  have hsup : Function.support ρ ⊆ ball (0:Space) (2*r₀) :=
    (support_indicator_subset).trans (ball_subset_ball (by linarith))
  have hh := bounded_density_potential_difference hm hM (by positivity : 0 < 2*r₀) hn hb hsup x y
    (by linarith) (by linarith)
  rw [innerPotential_eq_tfPotential,innerPotential_eq_tfPotential]
  apply hh.trans_eq
  calc
    _ = (16*Real.pi*(N:ℝ)*G)*((c₁*r₀^(1+masterExponent))⁻¹^3*r₀)*‖x-y‖ := by ring
    _ = _ := by rw [initial_radius_factor hr]; ring

end CoulombAtom

end

end OAI
