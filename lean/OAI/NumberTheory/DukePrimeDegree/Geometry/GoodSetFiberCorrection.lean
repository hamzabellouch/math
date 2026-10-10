import OAI.NumberTheory.DukePrimeDegree.Dynamics.InvariantMeasureGroup
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-!
# Correcting a pair inside a large generic set

The two initial points may be corrected by a changing element of the
measure stabilizer.  Averaging the bad set along a fixed group patch
gives a larger good set.  For two points in that larger set, a common
group translation restores membership in the original generic set.
No commutation with the averaging flow is needed for this selection.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree

section FiberMass

variable {H Y : Type*} [MeasurableSpace H] [MeasurableSpace Y]

def badOrbitFiberMass (ρ : Measure H) (R : Y → H → Y)
    (K : Set H) (G : Set Y) (x : Y) : ℝ≥0∞ :=
  ∫⁻ h in K, Gᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (R x h) ∂ρ

lemma badOrbitFiberMass_eq_measure (ρ : Measure H) (R : Y → H → Y)
    (K : Set H) (G : Set Y) (hG : MeasurableSet G)
    (x : Y) (hR : Measurable (R x)) :
    badOrbitFiberMass ρ R K G x = ρ (K ∩ {h | R x h ∉ G}) := by
  unfold badOrbitFiberMass
  change (∫⁻ h in K, ((R x) ⁻¹' Gᶜ).indicator (1 : H → ℝ≥0∞) h ∂ρ) = _
  rw [lintegral_indicator_one (hG.compl.preimage hR),
    Measure.restrict_apply (hG.compl.preimage hR)]
  congr 1
  ext h
  simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_ofPred_eq]
  exact and_comm

lemma measurable_badOrbitFiberMass (ρ : Measure H) [SFinite ρ]
    (R : Y → H → Y) (hR : Measurable (Function.uncurry R))
    (K : Set H) (G : Set Y) (hG : MeasurableSet G) :
    Measurable (badOrbitFiberMass ρ R K G) := by
  exact ((measurable_const.indicator hG.compl).comp hR).lintegral_prod_right'

/-- Invariance gives the exact average bad-fiber mass. -/
lemma lintegral_badOrbitFiberMass
    (μ : Measure Y) [SFinite μ] (ρ : Measure H) [SFinite ρ]
    (R : Y → H → Y) (hR : Measurable (Function.uncurry R))
    (hinv : ∀ h, MeasurePreserving (fun x => R x h) μ μ)
    (K : Set H) (G : Set Y) (hG : MeasurableSet G) :
    (∫⁻ x, badOrbitFiberMass ρ R K G x ∂μ) = ρ K * μ Gᶜ := by
  unfold badOrbitFiberMass
  have hm : AEMeasurable (Function.uncurry
      (fun x h => Gᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (R x h)))
      (μ.prod (ρ.restrict K)) :=
    ((measurable_const.indicator hG.compl).comp hR).aemeasurable
  rw [lintegral_lintegral_swap hm]
  have hinner (h : H) :
      (∫⁻ x, Gᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (R x h) ∂μ) = μ Gᶜ := by
    change (∫⁻ x, ((fun x => R x h) ⁻¹' Gᶜ).indicator
      (1 : Y → ℝ≥0∞) x ∂μ) = _
    rw [lintegral_indicator_one (hG.compl.preimage (hinv h).measurable)]
    rw [← Measure.map_apply (hinv h).measurable hG.compl, (hinv h).map_eq]
  simp_rw [hinner]
  rw [setLIntegral_const, mul_comm]

/-- The enlarged good set has an explicit complement bound and a
pointwise fiber estimate, rather than only an almost-everywhere one. -/
theorem exists_goodOrbitFiber_set
    (μ : Measure Y) [SFinite μ] (ρ : Measure H) [SFinite ρ]
    (R : Y → H → Y) (hR : Measurable (Function.uncurry R))
    (hinv : ∀ h, MeasurePreserving (fun x => R x h) μ μ)
    (K : Set H) (G : Set Y) (hG : MeasurableSet G)
    (a : ℝ≥0∞) (ha : a ≠ 0) (hatop : a ≠ ⊤) :
    ∃ E : Set Y, MeasurableSet E ∧
      μ Eᶜ ≤ (ρ K * μ Gᶜ) / a ∧
      ∀ x ∈ E, badOrbitFiberMass ρ R K G x < a := by
  let E := {x | badOrbitFiberMass ρ R K G x < a}
  have hm := measurable_badOrbitFiberMass ρ R hR K G hG
  refine ⟨E, measurableSet_lt hm measurable_const, ?_, fun _ hx => hx⟩
  have heq : Eᶜ = {x | a ≤ badOrbitFiberMass ρ R K G x} := by
    ext x
    simp only [E, mem_compl_iff, mem_ofPred_eq, not_lt]
  rw [heq]
  simpa only [lintegral_badOrbitFiberMass μ ρ R hR hinv K G hG] using
    meas_ge_le_lintegral_div (hm.aemeasurable (μ := μ)) ha hatop

/-- A small original exceptional set leaves a genuinely positive-mass
set of points with uniformly small bad fibers. -/
theorem exists_positive_goodOrbitFiber_set
    (μ : Measure Y) [IsProbabilityMeasure μ] (ρ : Measure H) [SFinite ρ]
    (R : Y → H → Y) (hR : Measurable (Function.uncurry R))
    (hinv : ∀ h, MeasurePreserving (fun x => R x h) μ μ)
    (K : Set H) (G : Set Y) (hG : MeasurableSet G)
    (a : ℝ≥0∞) (ha : a ≠ 0) (hatop : a ≠ ⊤)
    (hbudget : (ρ K * μ Gᶜ) / a < 1) :
    ∃ E : Set Y, MeasurableSet E ∧ μ E ≠ 0 ∧
      ∀ x ∈ E, badOrbitFiberMass ρ R K G x < a := by
  obtain ⟨E, hE, hbound, hsmall⟩ :=
    exists_goodOrbitFiber_set μ ρ R hR hinv K G hG a ha hatop
  refine ⟨E, hE, ?_, hsmall⟩
  intro hzero
  have hcompl : μ Eᶜ = 1 := by
    simpa only [hzero, zero_add, measure_univ] using measure_add_measure_compl (μ := μ) hE
  have hlt := hbound.trans_lt hbudget
  rw [hcompl] at hlt
  exact lt_irrefl _ hlt

end FiberMass

section CommonCorrection

variable {H Y : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
  [MeasurableSpace Y]

/-- A common bounded translation corrects both points.  The first
correction is allowed to vary and need not commute with any flow. -/
theorem exists_common_goodOrbit_correction
    (ρ : Measure H) [ρ.IsMulLeftInvariant]
    (R : Y → H → Y) (hR : ∀ x, Measurable (R x))
    (K₀ K₁ : Set H) (hK : K₀ ⊆ K₁)
    (G : Set Y) (hG : MeasurableSet G) (x y : Y) (b : H)
    (hb : ∀ h ∈ K₀, b * h ∈ K₁)
    (hsmall : badOrbitFiberMass ρ R K₁ G x +
      badOrbitFiberMass ρ R K₁ G y < ρ K₀) :
    ∃ h ∈ K₀, R x h ∈ G ∧ R y (b * h) ∈ G := by
  classical
  let Dₓ := K₁ ∩ {h | R x h ∉ G}
  let Dᵧ := K₁ ∩ {h | R y h ∉ G}
  have hxmass : ρ Dₓ = badOrbitFiberMass ρ R K₁ G x :=
    (badOrbitFiberMass_eq_measure ρ R K₁ G hG x (hR x)).symm
  have hymass : ρ Dᵧ = badOrbitFiberMass ρ R K₁ G y :=
    (badOrbitFiberMass_eq_measure ρ R K₁ G hG y (hR y)).symm
  by_contra hn
  have hcover : K₀ ⊆ Dₓ ∪ (fun h => b * h) ⁻¹' Dᵧ := by
    intro h hh
    by_cases hx : R x h ∈ G
    · right
      refine ⟨hb h hh, ?_⟩
      intro hy
      exact hn ⟨h, hh, hx, hy⟩
    · exact Or.inl ⟨hK hh, hx⟩
  have hle : ρ K₀ ≤ badOrbitFiberMass ρ R K₁ G x +
      badOrbitFiberMass ρ R K₁ G y := by
    calc
      ρ K₀ ≤ ρ (Dₓ ∪ (fun h => b * h) ⁻¹' Dᵧ) := measure_mono hcover
      _ ≤ ρ Dₓ + ρ ((fun h => b * h) ⁻¹' Dᵧ) := measure_union_le _ _
      _ = _ := by rw [measure_preimage_mul, hxmass, hymass]
  exact (not_le_of_gt hsmall) hle

/-- The common correction applies uniformly to every pair in the
fiber-good set and every sufficiently small correction. -/
theorem exists_common_goodOrbit_correction_of_fiber_bounds
    (ρ : Measure H) [ρ.IsMulLeftInvariant]
    (R : Y → H → Y) (hR : ∀ x, Measurable (R x))
    (K₀ K₁ : Set H) (hK : K₀ ⊆ K₁)
    (G E : Set Y) (hG : MeasurableSet G)
    (a : ℝ≥0∞) (hsize : a + a < ρ K₀)
    (hE : ∀ x ∈ E, badOrbitFiberMass ρ R K₁ G x ≤ a)
    (x y : Y) (hx : x ∈ E) (hy : y ∈ E) (b : H)
    (hb : ∀ h ∈ K₀, b * h ∈ K₁) :
    ∃ h ∈ K₀, R x h ∈ G ∧ R y (b * h) ∈ G := by
  apply exists_common_goodOrbit_correction ρ R hR K₀ K₁ hK G hG x y b hb
  exact (add_le_add (hE x hx) (hE y hy)).trans_lt hsize

end CommonCorrection

end DukePrimeDegree

end

end OAI
