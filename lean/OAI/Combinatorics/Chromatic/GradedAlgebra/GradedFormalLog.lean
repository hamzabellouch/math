import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.PowerSeriesSplitLeading

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma graded_multiply (V : ℕ→AddSubgroup A)
    (hMul : ∀n k a b,a∈V n→b∈V k→a*b∈V (n+k))
    (F G : PowerSeries A) (hF : ∀n,coeff n F∈V n) (hG : ∀n,coeff n G∈V n) :
    ∀n,coeff n (F*G)∈V n := by
  intro n
  rw [coeff_mul]
  apply (V n).sum_mem
  intro p hp
  have he:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [←he]
  exact hMul p.1 p.2 _ _ (hF p.1) (hG p.2)
lemma graded_one (V : ℕ→AddSubgroup A) (hOne : (1:A)∈V 0) :
    ∀n,coeff n (1:PowerSeries A)∈V n := by
  intro n
  rw [coeff_one]
  split_ifs with hn
  · subst n; exact hOne
  · exact (V n).zero_mem

variable [Module ℚ A]

lemma log_graded (V : ℕ→AddSubgroup A) (hOne : (1:A)∈V 0)
    (hMul : ∀n k a b,a∈V n→b∈V k→a*b∈V (n+k))
    (hScalar : ∀n (a : ℚ),∀x∈V n,a • x∈V n)
    (F : PowerSeries A) (hF : ∀n,coeff n F∈V n) :
    ∀n,coeff n (log F)∈V n := by
  have hu : ∀n,coeff n (F-1)∈V n:=by
    intro n
    rw [map_sub]
    exact (V n).sub_mem (hF n) (graded_one V hOne n)
  have hp : ∀k n,coeff n ((F-1)^k)∈V n:=by
    intro k
    induction k with
    | zero=>simpa only [pow_zero] using graded_one V hOne
    | succ k ih=>simpa only [pow_succ] using graded_multiply V hMul _ _ ih hu
  intro n
  simp only [log,coeff_mk]
  apply (V n).sum_mem
  intro k hk
  exact hScalar n _ _ (hp (k+1) n)
end
end ElementaryPositivity.FormalLog

end

end OAI
