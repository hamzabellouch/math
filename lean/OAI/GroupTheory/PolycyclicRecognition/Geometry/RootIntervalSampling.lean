import OAI.GroupTheory.PolycyclicRecognition.Analysis.UniformIntervalSamples

namespace OAI

/-! # The actual independent interval laws for the root increments -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

variable {L N I : Type*} [AddCommGroup L] [Module ℝ L] [Group N]

/-- Extend a fixed finite word by zero directions for the unused indices. -/
def rootIntervalDirection {m : ℕ} (letters : Fin m → I) (X : I → L)
    (s : I → ℝ) (r : ℝ) (j : ℕ) : L :=
  if h : j < m then Real.exp (r * s (letters ⟨j, h⟩)) • X (letters ⟨j, h⟩) else 0

def rootIntervalSample (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r : ℝ) (j : ℕ) (t : ℝ) : N :=
  Exp (t • rootIntervalDirection letters X s r j)

omit [Group N] in
theorem rootIntervalSample_letter (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r : ℝ) (j : Fin m) (t : ℝ) :
    rootIntervalSample Exp letters X s r j.val t =
      Exp (t • (Real.exp (r * s (letters j)) • X (letters j))) := by
  simp [rootIntervalSample, rootIntervalDirection, j.isLt]

/-- Two independent interval samples differ by the single intended root
increment. There is no need to retain a profile at their intermediate product. -/
theorem rootIntervalSample_sub (Exp : L → N)
    (hneg : ∀ v, Exp (-v) = (Exp v)⁻¹)
    (hadd : ∀ (v : L) (u t : ℝ), Exp ((u + t) • v) = Exp (u • v) * Exp (t • v))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ) (r : ℝ) (j : ℕ) (u t : ℝ) :
    rootIntervalSample Exp letters X s r j u * (rootIntervalSample Exp letters X s r j t)⁻¹ =
      rootIntervalSample Exp letters X s r j (u - t) := by
  unfold rootIntervalSample
  rw [← hneg, ← neg_smul, ← hadd, sub_eq_add_neg]

variable [MeasurableSpace N]

def rootIntervalLaw (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r R : ℝ) (j : ℕ) : Measure N :=
  Measure.map (rootIntervalSample Exp letters X s r j) (uniformIntervalLaw R)

omit [Group N] in
/-- These are pushforward laws of the original independent uniform samples. -/
theorem measurePreserving_rootIntervalSample [TopologicalSpace N] [BorelSpace N]
    (Exp : L → N)
    (hcont : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ) (r R : ℝ)
    (j : ℕ) :
    MeasurePreserving (rootIntervalSample Exp letters X s r j) (uniformIntervalLaw R)
      (rootIntervalLaw Exp letters X s r R j) := by
  exact ⟨(hcont _).measurable, rfl⟩

omit [Group N] in
theorem rootIntervalLaw_isProbability (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r : ℝ) {R : ℝ} (hR : 0 < R) (j : ℕ) :
    IsProbabilityMeasure (rootIntervalLaw Exp letters X s r R j) := by
  let := uniformIntervalLaw_isProbability hR
  unfold rootIntervalLaw
  infer_instance

end PolycyclicRecognition

end

end OAI
