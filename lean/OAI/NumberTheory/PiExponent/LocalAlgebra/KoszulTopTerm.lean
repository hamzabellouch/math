import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Prod
import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulBounded

namespace OAI

noncomputable section
universe u
namespace PiExponentSiegelAux.W31
variable {R : Type u} [CommRing R]

def scalarConeTopEquiv (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (d : ℕ)
    (hbound : ∀ n, d < n → Subsingleton (C.X n)) :
    (W30.scalarConeComplex C r).X (d + 1) ≃ₗ[R] C.X d := by
  letI := hbound (d + 1) (Nat.lt_succ_self d)
  letI : Unique (C.X (d + 1)) :=
    { default := 0, uniq := fun x => Subsingleton.elim x 0 }
  exact LinearEquiv.uniqueProd (R := R) (M := C.X d) (M₂ := C.X (d + 1))

def iterateScalarConesTopEquiv (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (d : ℕ) (hbound : ∀ n, d < n → Subsingleton (C.X n)) :
    (W30.iterateScalarCones C rs).X (d + rs.length) ≃ₗ[R] C.X d := by
  induction rs generalizing C d with
  | nil =>
    exact LinearEquiv.refl R (C.X d)
  | cons r rs ih =>
    have e := ih (W30.scalarConeComplex C r) (d + 1)
      (W30.scalarCone_bounded C r d hbound)
    let K := W30.iterateScalarCones (W30.scalarConeComplex C r) rs
    have hidx : d + (r :: rs).length = (d + 1) + rs.length := by
      simp only [List.length_cons]
      exact (Nat.add_assoc d rs.length 1).symm.trans (Nat.add_right_comm d rs.length 1)
    exact (K.XIsoOfEq hidx).toLinearEquiv.trans
      (e.trans (scalarConeTopEquiv C r d hbound))

def regularSequenceTopEquiv (rs : List R) :
    (W30.regularSequenceComplex rs).X rs.length ≃ₗ[R] R := by
  have hbound : ∀ n, 0 < n → Subsingleton (W30.emptyKoszulComplex (R := R) |>.X n) :=
    fun n hn => W30.regularSequenceComplex_bounded ([] : List R) n hn
  let K := W30.iterateScalarCones (W30.emptyKoszulComplex (R := R)) rs
  exact (K.XIsoOfEq (Nat.zero_add rs.length).symm).toLinearEquiv.trans
    (iterateScalarConesTopEquiv rs W30.emptyKoszulComplex 0 hbound)

def regularSequenceTopDualEquiv (rs : List R) :
    Module.Dual R ((W30.regularSequenceComplex rs).X rs.length) ≃ₗ[R] R :=
  (regularSequenceTopEquiv rs).dualMap.symm.trans (LinearMap.ringLmapEquivSelf R R R)

theorem regularSequenceTopDualEquiv_apply (rs : List R)
    (φ : Module.Dual R ((W30.regularSequenceComplex rs).X rs.length)) :
    regularSequenceTopDualEquiv rs φ = φ ((regularSequenceTopEquiv rs).symm 1) := rfl

end PiExponentSiegelAux.W31

end

end OAI
