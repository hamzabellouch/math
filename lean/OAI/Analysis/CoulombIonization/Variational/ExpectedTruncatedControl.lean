import Mathlib
import OAI.Analysis.CoulombIonization.Localization.MasterPotential
import OAI.Analysis.CoulombIonization.Variational.PotentialRecovery

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ExpectedTruncatedControl_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

open CoulombNeumann CoulombAnalysis
local instance : Fact ((5/3:ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by finiteness⟩
local instance : Fact ((5/2:ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by finiteness⟩
local instance (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
local instance (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

def weightedPatchTestAbs {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (g : TFSpace → ℝ)
    (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ s u)*
    |∫ x, g x*(retainedPatchLp hb (S u) u y R-
      tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ s Z lam y R u)) x
        ∂ballMeasure R|

lemma patchTestError_aestronglyMeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u}) {g : TFSpace → ℝ}
    (hm : MemLp g (5/2) (ballMeasure R)) :
    AEStronglyMeasurable (fun u =>
      ∫ x, g x*(retainedPatchLp hb (S u) u y R-
        tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ s Z lam y R u)) x
          ∂ballMeasure R) := by
  have hs : Measurable (fun u : Configuration M => retainedPatchLp hb (S u) u y R) :=
    retainedPatchLp_measurable hb S id hS measurable_id y R
  have hr := conditionalPatchMinimizer_aemeasurable hψ s Z lam y R
  exact ((patch_test_continuous_of_memLp R hm).measurable.comp_aemeasurable
    (hs.aemeasurable.sub hr)).aestronglyMeasurable

lemma weightedPatchTruncatedAbs_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space)
    {R r : ℝ} (hr : 0 < r) (hR : r < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    Integrable (weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/max ‖x‖ r)) :=
  (weighted_abs_integrable_and_bound (fun _ => formMass_nonneg _)
    (hψ.coreSlice_mass_integrable s)
    (patchTestError_aestronglyMeasurable hψ s Z lam y R hb S hS (truncated_kernel_memLp R hr))
    (weightedPatchTruncatedSquare_integrable hψ s Z lam y hr hR hb S hS hi)).1

theorem radial_truncated_absolute_control {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {r : ℝ} (hr : 0 < r) (hR : r < t-4*b) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestAbs (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/max ‖x‖ r) u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt ((2/r)*
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          weightedPatchGap (orderedCutForm (coreFirstRadialCut y ht hb)
            (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
            (radialPatchRetention N y t b c s) u)) := by
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let I := (c : Fin N → Fin 2) × Spins (cutOutNumber c)
  let w := fun i : I => fun u : Configuration (cutOutNumber i.1) =>
    formMass (coreSlice (orderedCutForm p hp ψ i.1) i.2 u)
  let f := fun i : I => fun u : Configuration (cutOutNumber i.1) =>
    ∫ x, (1/max ‖x‖ r)*(retainedPatchLp hb (radialPatchRetention N y t b i.1 i.2 u) u y (t-4*b)-
      tfPatchMinimizer (t-4*b) tfKinetic tfKinetic_pos
        (conditionalPatchField (orderedCutForm p hp ψ i.1) i.2 Z lam y (t-4*b) u)) x
      ∂ballMeasure (t-4*b)
  have hχ (c : Fin N → Fin 2) : SobolevVector (orderedCutForm p hp ψ c) :=
    orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hgap (i : I) := radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam
    hg hcg hgn hrad hgs i.1 i.2
  have hcs := finite_weighted_abs_bound (μ := fun i : I => (volume : Measure (Configuration (cutOutNumber i.1))))
    (w := w) (f := f) (fun _ _ => formMass_nonneg _)
    (fun i => (hχ i.1).coreSlice_mass_integrable i.2)
    (fun i => patchTestError_aestronglyMeasurable (hχ i.1) i.2 Z lam y (t-4*b) hb _
      (radialPatchRetention_measurable N y t b i.1 i.2) (truncated_kernel_memLp _ hr))
    (fun i => weightedPatchTruncatedSquare_integrable (hχ i.1) i.2 Z lam y hr hR hb _
      (radialPatchRetention_measurable N y t b i.1 i.2) (hgap i))
  have hmass : (∑ i : I, ∫ u, w i u) = formMass ψ := by
    rw [Fintype.sum_sigma]
    change (∑ c, ∑ s, ∫ u, formMass (coreSlice (orderedCutForm p hp ψ c) s u)) = _
    simp_rw [SobolevVector.integral_coreSlice_mass (hχ _)]
    exact orderedCutForm_mass_sum p hp hψ.sobolevVector
  rw [hmass,Fintype.sum_sigma,Fintype.sum_sigma] at hcs
  change (∑ c, ∑ s, ∫ u, weightedPatchTestAbs (orderedCutForm p hp ψ c) s Z lam y _ hb
    (radialPatchRetention N y t b c s) (fun x => 1/max ‖x‖ r) u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt
        (∑ c, ∑ s, ∫ u, weightedPatchTestSquare (orderedCutForm p hp ψ c) s Z lam y _ hb
          (radialPatchRetention N y t b c s) (fun x => 1/max ‖x‖ r) u) at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (radial_truncated_test_control hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hr hR))
    (Real.sqrt_nonneg _))

end Work_ExpectedTruncatedControl_scope

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

open CoulombAnalysis

def masterSmearing (c₁ r₀ s : ℝ) (g ρ : Space → ℝ) (y : Space) : ℝ :=
  ∫ x, ρ x*masterKernel c₁ r₀ s g x y

lemma scaled_packet_density_compact {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z => (scaledRealPacket b g z)^2) := by
  convert! (scaledRealPacket_compact hb hg).mul_right (f' := scaledRealPacket b g) using 1
  funext z
  exact pow_two _

lemma masterKernel_pole_measurable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) (y : Space) :
    Measurable (fun x => tfPotential (masterKernel c₁ r₀ s g x) y) := by
  have hm : Measurable (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2/‖y-p.2‖) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma master_potential_integrable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {ρ : Space → ℝ} (hmρ : Measurable ρ) (hρ : Integrable ρ) (hp : MemLp ρ (5/3)) (y : Space) :
    Integrable (fun x => ρ x*tfPotential (masterKernel c₁ r₀ s g x) y) := by
  apply (tfPotential_integrable hρ.norm hp.norm y).mono'
    (hmρ.mul (masterKernel_pole_measurable hc hr hs hg.continuous y)).aestronglyMeasurable
  filter_upwards [ae_ne_point y] with x hx
  change ‖ρ x*tfPotential (masterKernel c₁ r₀ s g x) y‖ ≤ _
  rw [norm_mul,Real.norm_eq_abs (tfPotential _ _),
    abs_of_nonneg (masterKernel_potential_nonneg c₁ r₀ s g x y)]
  have hh := mul_le_mul_of_nonneg_left
    (masterKernel_potential_le hc hr hs hg hcg hgn hrad hgs hx) (norm_nonneg (ρ x))
  simpa only [mul_one_div] using hh

lemma master_smearing_pole_integrable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {ρ : Space → ℝ} (hmρ : Measurable ρ) (hρ : Integrable ρ) (hp : MemLp ρ (5/3)) (y : Space) :
    Integrable (fun p : Space × Space => ρ p.1*masterKernel c₁ r₀ s g p.1 p.2/‖y-p.2‖) := by
  have hm : Measurable (fun p : Space × Space => ρ p.1*masterKernel c₁ r₀ s g p.1 p.2/‖y-p.2‖) :=
    ((hmρ.comp measurable_fst).mul (masterKernel_joint_continuous hc hr hs hg.continuous).measurable).div (by fun_prop)
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  refine ⟨Eventually.of_forall fun x => ?_,?_⟩
  · have hη := scaled_packet_density_compact (masterWidth_pos hc hr hs x) hcg
    have hηc := (scaledRealPacket_smooth (masterWidth c₁ r₀ s x) hg).continuous.pow 2
    have hh := (translated_pole_integrable (hηc.integrable_of_hasCompactSupport hη)
      (hηc.memLp_of_hasCompactSupport hη) y x).const_mul (ρ x)
    convert! hh using 1
    funext z
    simp only [masterKernel,Pi.pow_apply,mul_div_assoc]
  · have hi := master_potential_integrable hc hr hs hg hcg hgn hrad hgs hmρ.norm hρ.norm hp.norm y
    convert! hi using 1
    funext x
    simp only [norm_div,norm_mul,norm_norm,
      Real.norm_of_nonneg (masterKernel_nonneg c₁ r₀ s g x _),mul_div_assoc,integral_const_mul,tfPotential]

lemma masterSmearing_potential {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {ρ : Space → ℝ} (hmρ : Measurable ρ) (hρ : Integrable ρ) (hp : MemLp ρ (5/3)) (y : Space) :
    tfPotential (masterSmearing c₁ r₀ s g ρ) y =
      ∫ x, ρ x*tfPotential (masterKernel c₁ r₀ s g x) y := by
  change (∫ z, (∫ x, ρ x*masterKernel c₁ r₀ s g x z)/‖y-z‖) = _
  calc
    _ = ∫ z, ∫ x, ρ x*masterKernel c₁ r₀ s g x z/‖y-z‖ := by simp only [integral_div]
    _ = ∫ x, ∫ z, ρ x*masterKernel c₁ r₀ s g x z/‖y-z‖ :=
      integral_integral_swap (master_smearing_pole_integrable hc hr hs hg hcg hgn hrad hgs hmρ hρ hp y).swap
    _ = _ := by simp only [mul_div_assoc,integral_const_mul,tfPotential]

theorem masterSmearing_potential_loss {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {ρ : Space → ℝ} (hmρ : Measurable ρ) (hρ : Integrable ρ) (hp : MemLp ρ (5/3))
    (hn : ∀ x, 0 ≤ ρ x) (y : Space) :
    0 ≤ tfPotential ρ y-tfPotential (masterSmearing c₁ r₀ s g ρ) y ∧
      tfPotential ρ y-tfPotential (masterSmearing c₁ r₀ s g ρ) y ≤
        ∫ x in ball y (2*masterWidth c₁ r₀ s y), ρ x/‖y-x‖ := by
  rw [masterSmearing_potential hc hr hs hg hcg hgn hrad hgs hmρ hρ hp y]
  have hraw := tfPotential_integrable hρ hp y
  have hms := master_potential_integrable hc hr hs hg hcg hgn hrad hgs hmρ hρ hp y
  change 0 ≤ (∫ x, ρ x/‖y-x‖)-(∫ x, ρ x*tfPotential (masterKernel c₁ r₀ s g x) y) ∧
    (∫ x, ρ x/‖y-x‖)-(∫ x, ρ x*tfPotential (masterKernel c₁ r₀ s g x) y) ≤ _
  rw [←integral_sub hraw hms]
  rw [←integral_indicator measurableSet_ball]
  have hpoint : ∀ᵐ x, 0 ≤ ρ x/‖y-x‖-ρ x*tfPotential (masterKernel c₁ r₀ s g x) y ∧
      ρ x/‖y-x‖-ρ x*tfPotential (masterKernel c₁ r₀ s g x) y ≤
        (ball y (2*masterWidth c₁ r₀ s y)).indicator (fun x => ρ x/‖y-x‖) x := by
    filter_upwards [ae_ne_point y] with x hx
    obtain ⟨h0,h1⟩ := masterKernel_potential_loss hc hcL hr hs hs1 hg hcg hgn hrad hgs hx
    have h0' := mul_nonneg (hn x) h0
    have h1' := mul_le_mul_of_nonneg_left h1 (hn x)
    by_cases hxB : x ∈ ball y (2*masterWidth c₁ r₀ s y)
    · rw [indicator_of_mem hxB] at h1' ⊢
      constructor <;> nlinarith [show ρ x*(1/‖y-x‖) = ρ x/‖y-x‖ by ring]
    · rw [indicator_of_notMem hxB] at h1' ⊢
      constructor <;> nlinarith [show ρ x*(1/‖y-x‖) = ρ x/‖y-x‖ by ring]
  exact ⟨integral_nonneg_of_ae (hpoint.mono fun _ hx => hx.1),
    integral_mono_ae (hraw.sub hms) (hraw.indicator measurableSet_ball) (hpoint.mono fun _ hx => hx.2)⟩

end CoulombAtom

end

end OAI
