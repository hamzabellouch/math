import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CoordinateEquiv
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExtFields

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ArithmeticSaving.TriangularExpressions
open Finset Classical
variable {α β : Type*} [DecidableEq α] [DecidableEq β] {k E : ℕ}
variable {e : Fin k ↪ α} (d : TriangularExpressions e E)

noncomputable def ofRelabel (v : β ↪ α) (e' : Fin k ↪ β)
    (hs : ∀ i, v (e' i)=e i)
    (q : Fin k → SquarefreeExpression β E) (m : Fin k → β)
    (hq : ∀ i, (q i).relabel v=d.expression i) (hm : ∀ i, v (m i)=d.modulus i) :
    TriangularExpressions e' E where
  expression := q
  modulus := m
  linear := d.linear
  divisor_modulus i hi := v.injective (by rw [hm,hs,d.divisor_modulus i hi])
  divisor_own_absent i hi := by
    intro hp
    apply d.divisor_own_absent i hi
    rw [←hs i,←hq i,SquarefreeExpression.support_relabel]
    exact mem_image.mpr ⟨e' i,hp,rfl⟩
  linear_modulus_ne i hi := by
    intro he
    apply d.linear_modulus_ne i hi
    rw [←hm i,←hs i,he]
  future_absent i j hij := by
    intro hp
    apply d.future_absent i j hij
    rw [←hs j,←hm i,←hq i,SquarefreeExpression.support_relabel]
    rcases mem_insert.mp hp with hp|hp
    · exact mem_insert.mpr (Or.inl (congrArg v hp))
    · exact mem_insert_of_mem (mem_image.mpr ⟨e' j,hp,rfl⟩)

lemma admissible_ofRelabel (v : β ↪ α) (e' : Fin k ↪ β)
    (hs : ∀ i, v (e' i)=e i)
    (q : Fin k → SquarefreeExpression β E) (m : Fin k → β)
    (hq : ∀ i, (q i).relabel v=d.expression i) (hm : ∀ i, v (m i)=d.modulus i)
    (P K : ℝ) (x : α → ℕ) (hx : d.Admissible P K x) :
    (d.ofRelabel v e' hs q m hq hm).Admissible P K (fun a => x (v a)) := by
  intro i
  have hi := hx i
  change (if d.linear i then
    ArithmeticClause.linear ((q i).linearCoeff (e' i) (fun a => (x (v a):ℤ)))
      ((q i).constantTerm (e' i) (fun a => (x (v a):ℤ))) (x (v (m i)))
    else ArithmeticClause.divisor ((q i).eval (fun a => (x (v a):ℤ)))).Holds P K (x (v (e' i)))
  rw [←SquarefreeExpression.linearCoeff_relabel (q i) v (fun a => (x a:ℤ)) (e' i),
    ←SquarefreeExpression.constant_relabel (q i) v (fun a => (x a:ℤ)) (e' i),
    ←SquarefreeExpression.eval_relabel (q i) v (fun a => (x a:ℤ)),hs i,hm i,hq i]
  exact hi

end OrdinaryCorrelations.ArithmeticSaving.TriangularExpressions

end

end OAI
