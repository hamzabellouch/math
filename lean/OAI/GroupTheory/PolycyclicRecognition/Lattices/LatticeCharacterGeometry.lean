import OAI.GroupTheory.PolycyclicRecognition.Geometry.CharacterHemisphereContraction
import Mathlib.Algebra.Module.ZLattice.Basic

namespace OAI

/-! # The actual vector lattice for the character criterion -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E] [Finite ι] (b : Basis ι ℝ E)

def basisLatticeEmbedding :
    Multiplicative (Submodule.span ℤ (Set.range b)) →* Multiplicative E :=
  (Submodule.span ℤ (Set.range b)).subtype.toAddMonoidHom.toMultiplicative

omit [ProperSpace E] [Finite ι] in
theorem basisLatticeEmbedding_span :
    Submodule.span ℝ (Set.range (fun q => (basisLatticeEmbedding b q).toAdd)) = ⊤ := by
  have he : Set.range (fun q => (basisLatticeEmbedding b q).toAdd) =
      (Submodule.span ℤ (Set.range b) : Set E) := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact q.toAdd.property
    · intro hx
      exact ⟨Multiplicative.ofAdd ⟨x, hx⟩, rfl⟩
  rw [he]
  exact ZSpan.span_top b

theorem basisLatticeEmbedding_bounded (R : ℝ) :
    Set.Finite {q | ‖(basisLatticeEmbedding b q).toAdd‖ ≤ R} := by
  let L := Submodule.span ℤ (Set.range b)
  have h := ZSpan.setFinite_inter b (Metric.isBounded_closedBall (x := (0 : E)) (r := R))
  have hi : Function.Injective (fun q : Multiplicative L => ((q.toAdd : L) : E)) := by
    intro q r hqr
    apply Multiplicative.toAdd.injective
    exact Subtype.ext hqr
  have hp := Set.Finite.preimage hi.injOn h
  apply hp.subset
  intro q hq
  change ‖((q.toAdd : L) : E)‖ ≤ R at hq
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hq, q.toAdd.property⟩

omit [ProperSpace E] in
theorem basisLatticeEmbedding_coarseCover :
    ∃ R : ℝ, ∀ x : E, ∃ q, ‖(basisLatticeEmbedding b q).toAdd - x‖ ≤ R := by
  let := Fintype.ofFinite ι
  obtain ⟨R, hR⟩ := b.parallelepiped.isCompact.isBounded.subset_closedBall (0 : E)
  refine ⟨R, fun x => ⟨Multiplicative.ofAdd (ZSpan.floor b x), ?_⟩⟩
  have hf := hR (ZSpan.fundamentalDomain_subset_parallelepiped b
    (ZSpan.fract_mem_fundamentalDomain b x))
  change ‖(ZSpan.floor b x : E) - x‖ ≤ R
  rw [norm_sub_rev]
  simpa only [dist_zero_right, ZSpan.fract_apply] using (Metric.mem_closedBall.mp hf)

end PolycyclicRecognition

end

end OAI
