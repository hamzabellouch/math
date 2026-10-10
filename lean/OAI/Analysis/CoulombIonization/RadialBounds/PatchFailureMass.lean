import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.CutMomentBounds

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma weighted_markov_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w G : X → ℝ} (hw : Integrable w μ) (hwn : ∀ x, 0 ≤ w x)
    (hG : AEMeasurable G μ) (hGn : ∀ x, 0 ≤ G x)
    (hi : Integrable (fun x => w x*G x) μ) {e : ℝ} (_he : 0 < e) :
    e*(∫ x, if e < G x then w x else 0 ∂μ) ≤ ∫ x, w x*G x ∂μ := by
  have hb : Integrable (fun x => if e < G x then w x else 0) μ := by
    exact hw.indicator₀ (nullMeasurableSet_lt aemeasurable_const hG)
  rw [←integral_const_mul]
  apply integral_mono (hb.const_mul e) hi
  intro x
  change e*(if e < G x then w x else 0) ≤ w x*G x
  split_ifs with hx
  · nlinarith [mul_le_mul_of_nonneg_left hx.le (hwn x)]
  · simpa only [mul_zero] using mul_nonneg (hwn x) (hGn x)

def radialPatchGapSample {L : ℕ} (ψ : FormVector L) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (Z lam : ℝ)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c)) : ℝ :=
  tfPatchGap (t-4*b) tfKinetic tfKinetic_pos
    (conditionalPatchField (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) u)
    (retainedPatchLp hb (radialPatchRetention L y t b c s u) u y (t-4*b))

lemma radialPatchGapSample_nonneg {L : ℕ} (ψ : FormVector L) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (Z lam : ℝ)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c)) :
    0 ≤ radialPatchGapSample ψ y ht hb Z lam c s u := by
  exact tfPatchGap_nonneg _ _ _ _ (retainedPatchLp_nonneg _ _ _ _ _)

lemma radialPatchGapSample_aemeasurable {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (Z lam : ℝ)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
    AEMeasurable (radialPatchGapSample ψ y ht hb Z lam c s) :=
  conditionalPatchGap_aemeasurable
    (orderedCutForm_sobolev (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ c)
    s Z lam y (t-4*b) hb _ (radialPatchRetention_measurable L y t b c s)

def radialPatchFailureMass {L : ℕ} (ψ : FormVector L) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (Z lam e : ℝ) : ℝ :=
  ∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
    if e < radialPatchGapSample ψ y ht hb Z lam c s u then
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s u) else 0

lemma radialPatchFailureMass_mem_Icc {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (Z lam e : ℝ) :
    radialPatchFailureMass ψ y ht hb Z lam e ∈ Icc 0 (formMass ψ) := by
  constructor
  · apply Finset.sum_nonneg; intro c _
    apply Finset.sum_nonneg; intro s _
    apply integral_nonneg; intro u
    change 0 ≤ if e < radialPatchGapSample ψ y ht hb Z lam c s u then _ else 0
    split_ifs
    · exact formMass_nonneg _
    · exact le_refl 0
  · have hh := orderedCutForm_mass_sum (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) hψ
    rw [←hh]
    apply Finset.sum_le_sum; intro c _
    have hχ := orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) hψ c
    rw [←hχ.integral_coreSlice_mass]
    apply Finset.sum_le_sum; intro s _
    have hmass := hχ.coreSlice_mass_integrable s
    have hi := hmass.indicator₀ (nullMeasurableSet_lt (aemeasurable_const (b := e))
      (radialPatchGapSample_aemeasurable hψ y ht hb Z lam c s))
    apply integral_mono hi hmass
    intro u
    change (if e < radialPatchGapSample ψ y ht hb Z lam c s u then _ else 0) ≤ _
    split_ifs
    · exact le_refl _
    · exact formMass_nonneg _

lemma radial_weightedPatchGap_integrable {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
    Integrable (weightedPatchGap (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s)) := by
  apply weightedPatchGap_integrable
    (orderedCutForm_sobolev (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ.sobolevVector c)
    (orderedCutForm_core_antisymmetric (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ c)
    s y (by linarith) hZ hlam hg hcg hgn hr hgs hb (radialPatchCore y t) _
    (radialPatch_packet_separation y hb hgs) (radialPatch_nuclear_distance hb hy)
    (radialPatch_core_distance y hb) _ (radialPatchRetention_measurable L y t b c s)
    (radialPatch_retained_margin y hb c s) (radialPatch_retained_nuclear hb hy c s)
    (radialPatch_retained_core y hb c s)
  intro u x i hi
  apply FormZeroAt.coreSlice
  exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
    (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
    (joinLists x u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)

theorem radial_patch_failure_markov {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {e : ℝ} (he : 0 < e) :
    e*radialPatchFailureMass ψ y ht hb Z lam e ≤
      ∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm (coreFirstRadialCut y ht hb)
          (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s) u := by
  simp only [radialPatchFailureMass,Finset.mul_sum]
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro s _
  exact weighted_markov_integral
    ((orderedCutForm_sobolev (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ.sobolevVector c).coreSlice_mass_integrable s)
    (fun _ => formMass_nonneg _) (radialPatchGapSample_aemeasurable hψ.sobolevVector y ht hb Z lam c s)
    (radialPatchGapSample_nonneg ψ y ht hb Z lam c s)
    (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam hg hcg hgn hr hgs c s) he

end CoulombAtom

end

end OAI
