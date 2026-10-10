import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.BarrierActualMeanFieldBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierOriginalForgettingBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierQuantitativeStep_barrier_scope

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

lemma IsNuclearBarrier.mono_budget {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ a p : Ω → TFSpace → ℝ} {Z k B C r T η η' : ℝ}
    (old : IsNuclearBarrier P μ Z k B C r T η a p) (hη : η ≤ η') :
    IsNuclearBarrier P μ Z k B C r T η' a p :=
  { old with mass := old.mass.trans hη }

lemma IsNuclearBarrier.mono_cap {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ a p : Ω → TFSpace → ℝ} {Z k B C C' r T η : ℝ}
    (old : IsNuclearBarrier P μ Z k B C r T η a p) (hC : C ≤ C') :
    IsNuclearBarrier P μ Z k B C' r T η a p := by
  refine { old with upper := fun sample x hx => (old.upper sample x hx).trans ?_ }
  exact div_le_div_of_nonneg_right hC (pow_nonneg (norm_nonneg _) _)

lemma IsNuclearBarrier.mono_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ a p : Ω → TFSpace → ℝ} {Z k B C r T T' η : ℝ}
    (old : IsNuclearBarrier P μ Z k B C r T η a p) (hr : 0 ≤ r) (hT : T ≤ T') :
    IsNuclearBarrier P μ Z k B C r T' η a p := by
  refine { old with tail := fun sample x hx => old.tail sample x ?_ }
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hT hr) hx

theorem original_quantitative_barrier_step {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1)
    {Z κ B C r M lam1 lam2 e ξ Cinv hl hh T η A Q lam : ℝ}
    (cal : OutwardCalibration κ B C M lam1 lam2 e ξ hl hh) (hr : 0 < r)
    (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (good : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → Prop)
    [DecidablePred good] (hgood : MeasurableSet {sample | good sample})
    {a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ}
    (old : IsNuclearBarrier (physicalObservationLaw μ K)
      (originalMasterField μ ell j c₁ r₀ s g) Z κ B C r T η a p)
    (hcap : ∀ sample, good sample → ∀ x, r ≤ ‖x‖ → ‖x‖ < 4*M*r →
      nuclearField Z x+meanFieldOffset lam (originalMasterField μ ell j c₁ r₀ s g sample) x ≤ C/‖x‖^4)
    (hinv : ∀ sample, good sample → ∀ x, r ≤ ‖x‖ → ‖x‖ < 4*M*r →
      InverseComparisonAt ‖x‖
        (nuclearField Z x+meanFieldOffset lam (originalMasterField μ ell j c₁ r₀ s g sample) x)
        (originalMasterField μ ell j c₁ r₀ s g sample x) κ hl hh ξ Cinv)
    (hprob : (physicalObservationLaw μ K).real {sample | ¬good sample} ≤ A*r^25)
    (hmoment : ∀ x, r ≤ ‖x‖ → ‖x‖ < 2*r →
      (∫ sample, (originalMasterField μ ell j c₁ r₀ s g sample x)^2 ∂physicalObservationLaw μ K) ≤
        Q*r^(-12-6*masterExponent)) :
    ∃ a' p', IsNuclearBarrier (physicalObservationLaw μ K)
      (originalMasterField μ ell (j+1) c₁ r₀ s g) Z κ B C (2*r) M
      (η+(32*Real.pi/3*Real.sqrt A*Real.sqrt Q)*r^barrierErrorExponent) a' p' := by
  obtain ⟨hm,hlip,hbound,hρm,hρn,⟨D,hD,hρb⟩,hweak⟩ :=
    original_meanField_admissible μ ell j hc hr₀ hs hrs hg hcg hgn Z lam
  have hstep := outward_barrier_invariant good hgood cal (by positivity : 0 < 2*r)
    (by simpa only [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] using old)
    hm hlip hbound hρm hρn hD hρb
    (fun sample hg x hx hx' => hcap sample hg x (by linarith) (by nlinarith))
    (fun sample hg x hx hx' => hinv sample hg x (by linarith) (by nlinarith))
    (ae_of_all _ fun sample _ => hweak sample)
  have hmass := addedError_expected_mass_power good hgood hρm hD hr hA hQ hρn hρb hprob hmoment
  have hstep' := hstep.mono_budget
    (η' := η+(32*Real.pi/3*Real.sqrt A*Real.sqrt Q)*r^barrierErrorExponent)
    (by linarith only [hmass])
  have hnew := hstep'.forget_original
    μ ell (Nat.le_succ j) hc hr₀ hs hrs hg hcg (by positivity) cal.k_nonneg
  exact ⟨_,_,hnew⟩

end Work_BarrierQuantitativeStep_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom CoulombAnalysis

theorem monotone_reaction_comparison_ball {u v L χ : TFSpace → ℝ}
    {f : ℝ → ℝ} {R c lam : ℝ} (hR : 0 < R) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (hL : ∀ x, 0 ≤ L x) (hχ : ∀ x, 0 ≤ χ x) (hf : Monotone f)
    (hcont : ContinuousOn (fun x => u x-v x-L x) (closedBall 0 R))
    (hb : ∀ x : TFSpace, ‖x‖ = R → u x-v x-L x ≤ c)
    (hw : WeakLaplacianLowerOn (ball 0 R) (fun x => u x-v x-L x)
      (fun x => χ x*(f (u x)-f (v x-lam)))) :
    ∀ x ∈ closedBall (0 : TFSpace) R, u x-v x-L x ≤ c := by
  have hcmp := weak_subharmonic_positive_ball hR (hcont.sub continuousOn_const)
    (fun x hx => sub_nonpos.mpr (hb x hx)) (fun g hg hcg hs hn => ?_)
  · intro x hx
    exact sub_nonpos.mp (hcmp x hx)
  · have hs' : tsupport g ⊆ ball (0 : TFSpace) R := hs.trans inter_subset_left
    have hu := continuousOn_mul_integrable_support (isCompact_closedBall (0 : TFSpace) R)
      hcont (tfLaplacian_continuous hg)
      ((tfLaplacian_support hg).trans (hs'.trans ball_subset_closedBall))
    have hgi : Integrable (Δ g) :=
      (tfLaplacian_continuous hg).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg)
    have he : (∫ x, (u x-v x-L x-c)*Δ g x) = ∫ x, (u x-v x-L x)*Δ g x := by
      calc
        _ = ∫ x, (u x-v x-L x)*Δ g x-c*Δ g x := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by ring
        _ = _ := by
          rw [integral_sub hu (hgi.const_mul c),integral_const_mul,compact_laplacian_mass hg hcg,mul_zero,sub_zero]
    change 0 ≤ ∫ x, (u x-v x-L x-c)*Δ g x
    rw [he]
    apply le_trans _ (hw g hg hcg hs' hn)
    apply integral_nonneg
    intro x
    by_cases hx : g x = 0
    · simp only [hx,mul_zero,Pi.zero_apply,le_refl]
    · have hpos := (hs (subset_tsupport g hx)).2
      have hvu : v x-lam ≤ u x := by
        change 0 < u x-v x-L x-c at hpos
        linarith [hL x]
      exact mul_nonneg (mul_nonneg (hχ x) (sub_nonneg.mpr (hf hvu))) (hn x)

theorem WeakLaplacianLowerOn.add_bounded_L1_potential
    {U : Set TFSpace} {u h ρ : TFSpace → ℝ}
    (hu : LocallyIntegrable u) (hh : LocallyIntegrable h)
    (hw : WeakLaplacianLowerOn U u h) (hm : Measurable ρ) (hi : Integrable ρ)
    {M : ℝ} (hM : 0 ≤ M) (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M) (b : ℝ) :
    WeakLaplacianLowerOn U (fun x => u x+b*tfPotential ρ x)
      (fun x => h x-b*(4*Real.pi)*ρ x) := by
  intro g hg hcg hs hgn
  have hΔ := tfLaplacian_continuous hg
  have hcΔ := tfLaplacian_compact hg hcg
  have hui := locallyIntegrable_mul_test hu hΔ hcΔ
  have hhi := locallyIntegrable_mul_test hh hg.continuous hcg
  have hρi := locallyIntegrable_mul_test hi.locallyIntegrable hg.continuous hcg
  have hpi := locallyIntegrable_mul_test
    (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous.locallyIntegrable hΔ hcΔ
  have hleft : (∫ x, (h x-b*(4*Real.pi)*ρ x)*g x) =
      (∫ x, h x*g x)-b*(4*Real.pi)*(∫ x, ρ x*g x) := by
    calc
      _ = ∫ x, h x*g x-(b*(4*Real.pi))*(ρ x*g x) := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by ring
      _ = _ := by
        rw [integral_sub hhi (hρi.const_mul (b*(4*Real.pi))),integral_const_mul]
  have hright : (∫ x, (u x+b*tfPotential ρ x)*Δ g x) =
      (∫ x, u x*Δ g x)-b*(4*Real.pi)*(∫ x, ρ x*g x) := by
    simp_rw [add_mul,mul_assoc]
    rw [integral_add hui (hpi.const_mul b),integral_const_mul,
      bounded_L1_weak_poisson hm hi hM hn hb hg hcg]
    ring
  rw [hleft,hright]
  exact sub_le_sub_right (hw g hg hcg hs hgn) _

end CoulombBarrier

end

end OAI
