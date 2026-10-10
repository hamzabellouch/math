import Mathlib
import OAI.Combinatorics.KMedian.Machines.AlphabetTable

namespace OAI

section Inline_PCPAlphabetSpec
namespace MetricKMedian.PCP.Compiler.AlphabetProgram
open AlphabetReduction Binary Binary.Automatic
open scoped Classical

variable (K : Type) [Fintype K] [DecidableEq K]
lemma position_correct (nv ne : ℕ) (C : BinaryCSP (Fin nv) (Fin ne) (BitVector K))
    (e : Fin ne) (a : LocalRelation.LocalPosition (C.allowed e : LocalRelation.Relation K)) :
    endpoint K nv e.val ((C.left e).val,(C.right e).val,C.allowed e)
      (positionInfo K (C.allowed e) a)=
    (nodeEquiv K nv ne (.inl (positionEmbed C (localMap C e a)))).val := by
  rcases a with x | (x | ⟨b,x⟩)
  · change (if (2:Fin 3)=0 then _ else if (2:Fin 3)=1 then _ else _)=_
    simp only [show (2:Fin 3)≠0 from by decide,show (2:Fin 3)≠1 from by decide,ite_false]
    rfl
  · change (if (2:Fin 3)=0 then _ else if (2:Fin 3)=1 then _ else _)=_
    simp only [show (2:Fin 3)≠0 from by decide,show (2:Fin 3)≠1 from by decide,ite_false]
    rfl
  · by_cases hb:b=0
    · simp only [positionInfo,hb,ite_eq_left,endpoint]
      change _=bitIndex K x+B K*(if (0:Fin 2)=0 then C.left e else C.right e).val
      simp only [ite_true]
    · simp only [positionInfo,hb,ite_false,endpoint]
      simp only [show (1:Fin 3)≠0 from by decide,ite_false,ite_eq_left]
      change _=bitIndex K x+B K*(if b=0 then C.left e else C.right e).val
      simp only [ite_eq_right hb]
variable (s : CSPTable (BitVector K)) (h : s.WellFormed)
lemma row_correct (e : Fin s.2.length) (z : Tag K) :
    row K s e.val z=
      ((vertexEquiv K s ((paddedBinary (s.csp h)).left ((e,z.1),z.2))).val,
       (vertexEquiv K s ((paddedBinary (s.csp h)).right ((e,z.1),z.2))).val,
       (paddedBinary (s.csp h)).allowed ((e,z.1),z.2)) := by
  unfold row
  rw [row_get]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · have hp := position_correct K s.1.length s.2.length (s.csp h) e
        ((LocalRelation.query ((s.csp h).allowed e : LocalRelation.Relation K) z.1.1
          (z.1.2 ((s.csp h).allowed e) z.1.1)).address z.2)
      exact hp
    · rfl
noncomputable def represents : (table K s).Represents (paddedBinary (s.csp h)) := by
  have he := CSPTable.rect_build (paddedBinary (s.csp h)) (seeds K s) (roots K s)
    (vertexEquiv K s) (edgeRootEquiv K s) (Ordered.fixed (Tag K))
    (Equiv.prodAssoc _ _ _).symm (row K s) (by
      intro e z
      exact row_correct K s h e z)
  unfold table
  rw [he]
  exact CSPTable.build_represents _ _ _
end MetricKMedian.PCP.Compiler.AlphabetProgram

end Inline_PCPAlphabetSpec

end OAI
