import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairAction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasedImagePaths

namespace OAI

/-! # The source terminal set for a tuple centered at its initial image -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {N G : Type*} [TopologicalSpace N] [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]

def relativeTupleTerminals {h : ℕ} (ι : N → G) (origin base pivot : G)
    (last : Fin h) (S : Set (Fin h → N)) : Set G :=
  (fun v => origin⁻¹ * (base * ι (v last) * pivot)) '' S

omit [IsIsometricSMul G G] in
theorem isCompact_relativeTupleTerminals {h : ℕ} (ι : N → G) (hι : Continuous ι)
    (origin base pivot : G) (last : Fin h) {S : Set (Fin h → N)} (hS : IsCompact S) :
    IsCompact (relativeTupleTerminals ι origin base pivot last S) :=
  hS.image (continuous_const.mul ((continuous_const.mul
    (hι.comp (continuous_apply last))).mul continuous_const))

omit [TopologicalSpace N] in
/-- A source terminal relative to the original starting point maps to
the terminal coordinate of the centered tuple under the normalized pair. -/
theorem centered_image_terminal_mem {h : ℕ} {Λ : ℝ≥0}
    (p : NormalizedPair G Λ) (ι : N → G) (origin base pivot : G)
    (last : Fin h) (S : Set (Fin h → N)) {y : Fin h → G}
    (hy : y ∈ (fun v : Fin h → N => fun i =>
      basedImage p.val.1 origin (base * ι (v i) * pivot)) '' S) :
    ∃ z ∈ relativeTupleTerminals ι origin base pivot last S,
      y last = (normalizedTranslate origin p).val.1 z := by
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨origin⁻¹ * (base * ι (v last) * pivot), ⟨v, hv, rfl⟩, ?_⟩
  simp only [normalizedTranslate, translatePair, ContinuousMap.coe_mk,
    mul_inv_cancel_left, basedImage]

end PolycyclicRecognition

end

end OAI
