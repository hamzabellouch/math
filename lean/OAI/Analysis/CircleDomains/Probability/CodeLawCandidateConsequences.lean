import OAI.Analysis.CircleDomains.Probability.CodeLawCandidateBounds
import OAI.Analysis.CircleDomains.Probability.SlotLawMeasures

namespace OAI

/-! Unpack the fused candidate's quantitative estimates and slot laws. -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem countableSquareLawBounds_visit_norm (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (a : S → X) {C : ℝ≥0∞}
    (h : CountableSquareLawBounds (codeVisitWeight d a) (C ^ 2) P) :
    countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤ C := by
  have hs : (∑' s, meanVisitCount (codePathLaw d P) (a s) ^ 2) ≤ C ^ 2 := by
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    simpa only [meanVisitCount_codePathLaw_eq_integral] using h F
  calc
    _ ≤ (C ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hs (by norm_num)
    _ = C := by rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num

omit [BorelSpace X] [SecondCountableTopology X] [BorelSpace C(PathTime, X)] in
theorem CodeLawCandidate.slot_absolutelyContinuous
    (d : PathCodeData X Y) (a : S → X) (μ : Measure Y) (τ : Measure LevelTuple)
    (M N E V : ℝ≥0∞) (P : ProbabilityMeasure (BasePathCode d))
    (h : CodeLawCandidate d a μ τ M N E V P) (k : ℕ) : slotLaw d P k ≪ τ := by
  obtain ⟨q, _, hq, _⟩ := h.2.2.2
  exact slotLaw_absolutelyContinuous d P τ (hq ▸ withDensity_absolutelyContinuous τ q) k

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem ae_finite_prescribed_visits [Countable S]
    (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) (a : S → X)
    {V : ℝ≥0∞} (hV : V < ∞)
    (h : CountableSquareLawBounds (codeVisitWeight d a) V P) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ s, visitCount (codePath d Γ) (a s) < ∞ := by
  classical
  apply ae_all_iff.mpr
  intro s
  have hb : (∫⁻ Γ, codeVisitWeight d a s Γ ∂(P : Measure (BasePathCode d))) ^ 2 < ∞ := by
    simpa using (h {s}).trans_lt hV
  apply ae_lt_top (measurable_codeVisitWeight d a s)
  intro hh
  rw [hh] at hb
  simp at hb

end CircleDomainRigidity

end

end OAI
