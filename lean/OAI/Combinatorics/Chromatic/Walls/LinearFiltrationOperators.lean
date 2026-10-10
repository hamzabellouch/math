import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TensorFiltrationInterchange

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M : Type*} [AddCommGroup M] [Module ℚ M]

lemma restrict_pow_val (F : Submodule ℚ M) (D : Module.End ℚ M)
    (h : ∀ x∈F,D x∈F) (n : ℕ) (x : F) :
    ((restrict F F D h ^n) x).val=(D^n) x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ',Module.End.mul_apply]
    change D ((restrict F F D h^n) x).val=_
    rw [ih]

lemma map_pow_mk (F F' : Submodule ℚ M) (D : Module.End ℚ M)
    (h : ∀ x∈F,D x∈F) (h' : ∀ x∈F',D x∈F') (n : ℕ) (x : F) :
    (map F F' F F' D h h'^n) (mk F F' x)=mk F F' ((restrict F F D h^n) x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Module.End.mul_apply,ih]; rfl

lemma map_locally_nilpotent (F F' : Submodule ℚ M) (D : Module.End ℚ M)
    (h : ∀ x∈F,D x∈F) (h' : ∀ x∈F',D x∈F')
    (hnil : ∀ x,∃ N : ℕ,(D^N) x=0) (x : Grade F F') :
    ∃ N : ℕ,(map F F' F F' D h h'^N) x=0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨N,hN⟩:=hnil x.val
    refine ⟨N,?_⟩
    change (map F F' F F' D h h'^N) (mk F F' x)=0
    rw [map_pow_mk]
    have hz : (restrict F F D h^N) x=0 := by
      apply Subtype.ext
      rw [restrict_pow_val,hN]
      rfl
    rw [hz,map_zero]

lemma map_weyl (F F' : Submodule ℚ M) (D T : Module.End ℚ M)
    (hD : ∀ x∈F,D x∈F) (hD' : ∀ x∈F',D x∈F')
    (hT : ∀ x∈F,T x∈F) (hT' : ∀ x∈F',T x∈F')
    (h : ∀ x,D (T x)=T (D x)+x) (x : Grade F F') :
    map F F' F F' D hD hD' (map F F' F F' T hT hT' x)=
      map F F' F F' T hT hT' (map F F' F F' D hD hD' x)+x := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change mk F F' (restrict F F D hD (restrict F F T hT x)) =
      mk F F' (restrict F F T hT (restrict F F D hD x)) + mk F F' x
    rw [←map_add]
    exact congrArg (mk F F') (Subtype.ext (h x.val))

end ElementaryPositivity.LinearFiltration

end

end OAI
