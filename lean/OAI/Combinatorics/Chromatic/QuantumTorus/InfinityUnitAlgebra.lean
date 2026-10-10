import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.PowerSeriesSplitLeading
import OAI.Combinatorics.Chromatic.Walls.CompletedPureComparison

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {A B : Type*} [Ring A] [Ring B]

lemma innerHom_foldr (l : List Bˣ) (x : B) :
    l.foldr (fun u y=>innerHom u y) x=innerHom l.prod x := by
  induction l with
  | nil=>simp only [List.foldr_nil,List.prod_nil,innerHom_one]
  | cons a l ih=>simp only [List.foldr_cons,List.prod_cons,ih,innerHom_mul]

lemma mapped_unit_square (F : A →+* B) (u : Aˣ) (w : Bˣ)
    (h : F u.val=w.val) (x : A) : innerHom w (F x)=F (innerHom u x) := by
  have H : Units.map F u=w := Units.ext h
  rw [map_innerHom,H]

lemma coeff_commute_of_adjoints (u : (PowerSeries B)ˣ) (x : PowerSeries B) (D : ℕ)
    (h : ∀d≤D,coeff d (innerHom u x)=coeff d x) :
    coeff D (u.val*x)=coeff D (x*u.val) := by
  have H : coeff D (innerHom u x*u.val)=coeff D (x*u.val) := by
    apply ElementaryPositivity.FormalLog.mul_coeff_congr
    · exact h
    · exact fun _ _=>rfl
  change coeff D (((u.val*x)*u.inv)*u.val)=coeff D (x*u.val) at H
  simpa only [mul_assoc,u.inv_val,mul_one] using H
end
end ElementaryPositivity.RationalFiber

end

end OAI
