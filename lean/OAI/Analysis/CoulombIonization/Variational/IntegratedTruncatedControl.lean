import Mathlib
import OAI.Analysis.CoulombIonization.Variational.IntegratedLipschitzControl
import OAI.Analysis.CoulombIonization.RadialBounds.ShellCoulombDuality

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

namespace CoulombAtom
open CoulombNeumann CoulombAnalysis
local instance : Fact ((5/3:ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by finiteness⟩
local instance : Fact ((5/2:ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by finiteness⟩
local instance (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
local instance (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma patch_test_continuous_of_memLp (R : ℝ) {g : TFSpace → ℝ}
    (hm : MemLp g (5/2) (ballMeasure R)) :
    Continuous (fun f : TFLp (ballMeasure R) => ∫ x, g x*f x ∂ballMeasure R) := by
  have he : (fun f : TFLp (ballMeasure R) => ∫ x, g x*f x ∂ballMeasure R) =
      tfPatchPair R (hm.toLp g) := by
    funext f
    rw [tfPatchPair_apply]
    exact integral_congr_ae (hm.coeFn_toLp.mono fun x hx => by dsimp only; rw [hx])
  rw [he]
  exact (tfPatchPair R (hm.toLp g)).continuous

lemma truncated_kernel_memLp (R : ℝ) {t : ℝ} (ht : 0 < t) :
    MemLp (fun x : TFSpace => 1/max ‖x‖ t) (5/2) (ballMeasure R) := by
  have hc : Continuous (fun x : TFSpace => 1/max ‖x‖ t) :=
    continuous_const.div (continuous_norm.max continuous_const)
      (fun x => (ht.trans_le (le_max_right ‖x‖ t)).ne')
  apply MemLp.of_bound hc.aestronglyMeasurable (1/t)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le ht (le_max_right _ _)

lemma weightedPatchTestSquare_memLp_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u}) {g : TFSpace → ℝ}
    (hm : MemLp g (5/2) (ballMeasure R)) :
    AEMeasurable (weightedPatchTestSquare ψ s Z lam y R hb S g) := by
  have hmass := (hψ.coreSlice_mass_integrable s).aestronglyMeasurable.aemeasurable
  have hs : Measurable (fun u : Configuration M => retainedPatchLp hb (S u) u y R) :=
    retainedPatchLp_measurable hb S id hS measurable_id y R
  have hr := conditionalPatchMinimizer_aemeasurable hψ s Z lam y R
  have hp := (patch_test_continuous_of_memLp R hm).measurable.comp_aemeasurable
    (hs.aemeasurable.sub hr)
  exact hmass.mul (hp.pow_const 2)

lemma weightedPatchTruncatedSquare_le {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (Z lam : ℝ) (y : Space) {R t : ℝ} (ht : 0 < t) (hR : t < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M)) (u : Configuration M) :
    weightedPatchTestSquare ψ s Z lam y R hb S (fun x => 1/max ‖x‖ t) u ≤
      (2/t)*weightedPatchGap ψ s Z lam y R hb S u := by
  have hh := mul_le_mul_of_nonneg_left
    (tfPatchGap_truncated_control ht hR tfKinetic tfKinetic_pos
      (conditionalPatchField ψ s Z lam y R u) (retainedPatchLp_nonneg hb (S u) u y R))
    (formMass_nonneg (coreSlice ψ s u))
  simpa only [weightedPatchTestSquare,weightedPatchGap,mul_left_comm,mul_assoc] using hh

lemma weightedPatchTruncatedSquare_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space)
    {R t : ℝ} (ht : 0 < t) (hR : t < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    Integrable (weightedPatchTestSquare ψ s Z lam y R hb S (fun x => 1/max ‖x‖ t)) := by
  apply (hi.const_mul (2/t)).mono'
    (weightedPatchTestSquare_memLp_aemeasurable hψ s Z lam y R hb S hS
      (truncated_kernel_memLp R ht)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (weightedPatchTestSquare_nonneg ψ s Z lam y R hb S _ u)]
    exact weightedPatchTruncatedSquare_le ψ s Z lam y ht hR hb S u

lemma integral_weightedPatchTruncatedSquare_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space)
    {R t : ℝ} (ht : 0 < t) (hR : t < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    (∫ u, weightedPatchTestSquare ψ s Z lam y R hb S (fun x => 1/max ‖x‖ t) u) ≤
      (2/t)*(∫ u, weightedPatchGap ψ s Z lam y R hb S u) := by
  rw [←integral_const_mul]
  exact integral_mono (weightedPatchTruncatedSquare_integrable hψ s Z lam y ht hR hb S hS hi)
    (hi.const_mul _) (weightedPatchTruncatedSquare_le ψ s Z lam y ht hR hb S)

theorem radial_truncated_test_control {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {r : ℝ} (hr : 0 < r) (hR : r < t-4*b) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestSquare (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/max ‖x‖ r) u) ≤
      (2/r)*
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm (coreFirstRadialCut y ht hb)
          (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
          (radialPatchRetention N y t b c s) u) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro s _
  exact integral_weightedPatchTruncatedSquare_le
    (orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) hψ.sobolevVector c)
    s Z lam y hr hR hb _ (radialPatchRetention_measurable N y t b c s)
    (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs c s)

end CoulombAtom

end

end OAI
