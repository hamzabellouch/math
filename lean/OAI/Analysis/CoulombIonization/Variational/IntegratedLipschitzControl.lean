import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.PatchFailureMass
import OAI.Analysis.CoulombIonization.ThomasFermi.CoulombLipschitzDuality

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

lemma patch_test_continuous (R : ℝ) {g : TFSpace → ℝ}
    (hg : Continuous g) (hcg : HasCompactSupport g) :
    Continuous (fun f : TFLp (ballMeasure R) => ∫ x, g x*f x ∂ballMeasure R) := by
  have hm : MemLp g (5/2) (ballMeasure R) :=
    (hg.memLp_of_hasCompactSupport hcg).mono_measure Measure.restrict_le_self
  have he : (fun f : TFLp (ballMeasure R) => ∫ x, g x*f x ∂ballMeasure R) =
      tfPatchPair R (hm.toLp g) := by
    funext f
    rw [tfPatchPair_apply]
    exact integral_congr_ae (hm.coeFn_toLp.mono fun x hx => by dsimp only; rw [hx])
  rw [he]
  exact (tfPatchPair R (hm.toLp g)).continuous

def weightedPatchTestSquare {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (g : TFSpace → ℝ)
    (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ s u)*
    (∫ x, g x*(retainedPatchLp hb (S u) u y R-
      tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ s Z lam y R u)) x
        ∂ballMeasure R)^2

lemma weightedPatchTestSquare_nonneg {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (g : TFSpace → ℝ)
    (u : Configuration M) : 0 ≤ weightedPatchTestSquare ψ s Z lam y R hb S g u :=
  mul_nonneg (formMass_nonneg _) (sq_nonneg _)

lemma weightedPatchTestSquare_le {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (Z lam : ℝ) (y : Space) {R r : ℝ} (hr : 0 < r) (hR : 2*r < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    {g : TFSpace → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall 0 r) (u : Configuration M) :
    weightedPatchTestSquare ψ s Z lam y R hb S g u ≤
      (16*r^3*(L:ℝ)^2)*weightedPatchGap ψ s Z lam y R hb S u := by
  have hh := mul_le_mul_of_nonneg_left
    (tfPatchGap_lipschitz_control hr hR tfKinetic tfKinetic_pos
      (conditionalPatchField ψ s Z lam y R u) (retainedPatchLp_nonneg hb (S u) u y R) hg hs)
    (formMass_nonneg (coreSlice ψ s u))
  simpa only [weightedPatchTestSquare,weightedPatchGap,mul_left_comm,mul_assoc] using hh

lemma weightedPatchTestSquare_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u}) {g : TFSpace → ℝ}
    (hg : Continuous g) (hcg : HasCompactSupport g) :
    AEMeasurable (weightedPatchTestSquare ψ s Z lam y R hb S g) := by
  have hm := (hψ.coreSlice_mass_integrable s).aestronglyMeasurable.aemeasurable
  have hs : Measurable (fun u : Configuration M => retainedPatchLp hb (S u) u y R) :=
    retainedPatchLp_measurable hb S id hS measurable_id y R
  have hr := conditionalPatchMinimizer_aemeasurable hψ s Z lam y R
  have hp := (patch_test_continuous R hg hcg).measurable.comp_aemeasurable
    (hs.aemeasurable.sub hr)
  exact hm.mul (hp.pow_const 2)

lemma weightedPatchTestSquare_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space)
    {R r : ℝ} (hr : 0 < r) (hR : 2*r < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u}) {g : TFSpace → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hs : Function.support g ⊆ closedBall 0 r)
    (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    Integrable (weightedPatchTestSquare ψ s Z lam y R hb S g) := by
  have hcg : HasCompactSupport g :=
    (isCompact_closedBall (0 : TFSpace) r).of_isClosed_subset isClosed_closure
      (closure_minimal hs isClosed_closedBall)
  apply (hi.const_mul (16*r^3*(L:ℝ)^2)).mono'
    (weightedPatchTestSquare_aemeasurable hψ s Z lam y R hb S hS hg.continuous hcg).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (weightedPatchTestSquare_nonneg ψ s Z lam y R hb S g u)]
    exact weightedPatchTestSquare_le ψ s Z lam y hr hR hb S hg hs u

lemma integral_weightedPatchTestSquare_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space)
    {R r : ℝ} (hr : 0 < r) (hR : 2*r < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u}) {g : TFSpace → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hs : Function.support g ⊆ closedBall 0 r)
    (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    (∫ u, weightedPatchTestSquare ψ s Z lam y R hb S g u) ≤
      (16*r^3*(L:ℝ)^2)*(∫ u, weightedPatchGap ψ s Z lam y R hb S u) := by
  rw [←integral_const_mul]
  exact integral_mono (weightedPatchTestSquare_integrable hψ s Z lam y hr hR hb S hS hg hs hi)
    (hi.const_mul _) (weightedPatchTestSquare_le ψ s Z lam y hr hR hb S hg hs)

theorem radial_lipschitz_test_control {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : TFSpace → ℝ} {L : ℝ≥0} (hq : LipschitzWith L q)
    {r : ℝ} (hr : 0 < r) (hR : 2*r < t-4*b)
    (hs : Function.support q ⊆ closedBall 0 r) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestSquare (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) q u) ≤
      (16*r^3*(L:ℝ)^2)*
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm (coreFirstRadialCut y ht hb)
          (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
          (radialPatchRetention N y t b c s) u) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro s _
  exact integral_weightedPatchTestSquare_le
    (orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) hψ.sobolevVector c)
    s Z lam y hr hR hb _ (radialPatchRetention_measurable N y t b c s) hq hs
    (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs c s)

end CoulombAtom

end

end OAI
