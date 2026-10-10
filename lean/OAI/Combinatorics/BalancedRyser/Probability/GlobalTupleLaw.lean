import OAI.Combinatorics.BalancedRyser.Candidates.Candidates
import OAI.Combinatorics.BalancedRyser.Probability.UniformRestriction

namespace OAI

namespace Balanced.TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem fin_four_ne_next (i : Fin 4) : i ≠ i + 1 := by
  fin_cases i <;> decide

omit [Field F] [Fintype F] [DecidableEq F] in

theorem adjacent_ne_of_injective (T : FourTuple F) (hT : Function.Injective T.generator)
    (i : Fin 4) : T.generator i ≠ T.generator (i + 1) :=
  fun h => fin_four_ne_next i (hT h)

theorem tuplePoint_uniform (T : FourTuple F) (hT : Function.Injective T.generator) :
    (offsetLaw F).map (fun M => tuplePoint M T) =
      PMF.uniformOfFintype (Fin 4 → Point F) := by
  classical
  let hd := adjacent_ne_of_injective T hT
  let r : MergedPairs F → Fin 4 → Bool → F := fun M i => M (T.generator i)
  have hoff : offsetLaw F = PMF.uniformOfFintype (Direction F → Bool → F) := by
    ext M
    simp only [offsetLaw, PMF.uniformOfFintype_apply, Fintype.card_fun,
      Fintype.card_option, Fintype.card_bool]
  have hrestrict := uniform_map_restrict (ι := Fin 4) (D := Direction F)
    (A := Bool → F) ⟨T.generator, hT⟩
  simp only [Function.Embedding.coeFn_mk] at hrestrict
  have hf : (fun M => tuplePoint M T) = (tuplePositionEquiv T.generator hd T.side) ∘ r := by
    funext M i
    simp only [Function.comp_apply, tuplePositionEquiv_apply, tuplePoint, constituent]
    rfl
  rw [hf, ← PMF.map_comp, hoff]
  dsimp only [r]
  rw [hrestrict]
  exact tuplePosition_uniform T.generator hd T.side

theorem tuplePoint_alignment_probability (T : FourTuple F)
    (hT : Function.Injective T.generator) (l : Line F) :
    offsetEventProbability {M | ∀ i, OnLine (tuplePoint M T i) l} =
      (Fintype.card F : ℝ)⁻¹^4 := by
  let hd := adjacent_ne_of_injective T hT
  let E : Set (Fin 4 → Point F) := {p | ∀ i, OnLine (p i) l}
  have hg := congrArg (fun p => (p.toOuterMeasure E).toReal) (tuplePoint_uniform T hT)
  have hr := congrArg (fun p => (p.toOuterMeasure E).toReal)
    (tuplePosition_uniform T.generator hd T.side)
  rw [PMF.toOuterMeasure_map_apply] at hg hr
  exact hg.trans (hr.symm.trans (alignedOffsets_outer_probability
    T.generator hd T.side l.1 l.2))

end Balanced.TupleAlignment

end OAI
