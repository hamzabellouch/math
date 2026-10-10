import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.NilpotentLogarithm

namespace OAI

section
namespace ElementaryPositivity.FiniteLog
open PowerSeries
variable {A : Type*} [Ring A] [Algebra ℚ A]

open scoped IsMulCommutative in
lemma nilEval_exp_log {x : A} (hx : IsNilpotent x) :
    nilEval (nilEval x (log ℚ)) (exp ℚ)=1+x := by
  let s : Set A := {x}
  have hs : ∀ u ∈ s, ∀ v ∈ s, u*v=v*u := by
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst u; subst v; rfl
  let T := Algebra.adjoin ℚ s
  let : IsMulCommutative T := Algebra.isMulCommutative_adjoin ℚ
    (fun left hleft right hright _ => hs left hleft right hright)
  let : CommRing T := inferInstance
  let tx : T := ⟨x,Algebra.subset_adjoin (Set.mem_singleton x)⟩
  have htx : IsNilpotent tx := by
    obtain ⟨n,hn⟩ := hx
    exact ⟨n,Subtype.ext hn⟩
  have h := congrArg (Algebra.adjoin ℚ s).val (exp_nilEval_log htx)
  rw [←nilEval_exp (nilEval_nilpotent htx (constantCoeff_log (A := ℚ))),
    map_nilEval _ (nilEval_nilpotent htx (constantCoeff_log (A := ℚ))),
    map_nilEval _ htx,map_add,map_one] at h
  exact h

end ElementaryPositivity.FiniteLog

end

end OAI
