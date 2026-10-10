import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem346
namespace PolynomialShift

variable {K B I : Type*} [CommRing K]

attribute [local instance] Classical.propDecidable

/-- Transfer one unit of polynomial degree from `src` to `dst`. Other blocks
are spectator variables. -/
def derivation (src dst : B) :
    Derivation K (MvPolynomial (B × I) K) (MvPolynomial (B × I) K) := by
  classical
  exact MvPolynomial.mkDerivation K
    (fun v => if v.1 = src then MvPolynomial.X (dst, v.2) else 0)

@[simp]
theorem derivation_X (src dst block : B) (i : I) :
    derivation (K := K) src dst (MvPolynomial.X (block, i)) =
      if block = src then MvPolynomial.X (dst, i) else 0 := by
  classical
  simp [derivation]

/-- The directional shift as a linear endomorphism. -/
def shift (src dst : B) : Module.End K (MvPolynomial (B × I) K) :=
  (derivation src dst).toLinearMap

@[simp]
theorem shift_apply (src dst : B) (p : MvPolynomial (B × I) K) :
    shift src dst p = derivation src dst p := rfl

/-- Euler's operator for one block. -/
def euler (block : B) : Module.End K (MvPolynomial (B × I) K) :=
  shift block block

theorem commutator (src dst : B) (h : src ≠ dst) :
    ⁅derivation (K := K) (I := I) dst src, derivation (K := K) (I := I) src dst⁆ =
      derivation (K := K) (I := I) src src - derivation (K := K) (I := I) dst dst := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨block, i⟩
  by_cases hs : block = src <;> by_cases hd : block = dst <;>
    simp_all [Derivation.commutator_apply]

theorem commutator_apply (src dst : B) (h : src ≠ dst)
    (p : MvPolynomial (B × I) K) :
    shift dst src (shift src dst p) - shift src dst (shift dst src p) =
      euler src p - euler dst p := by
  have h' := congrArg (fun d : Derivation K (MvPolynomial (B × I) K)
    (MvPolynomial (B × I) K) => d p) (commutator (K := K) (I := I) src dst h)
  simpa [Derivation.commutator_apply, euler] using h'

theorem weight_commutator (src dst : B) (h : src ≠ dst) :
    ⁅derivation (K := K) (I := I) src src - derivation (K := K) (I := I) dst dst,
      derivation (K := K) (I := I) dst src⁆ = (2 : K) • derivation (K := K) (I := I) dst src := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨block, i⟩
  by_cases hs : block = src <;> by_cases hd : block = dst <;>
    simp_all [Derivation.commutator_apply, two_smul]

end PolynomialShift
end Problem346

end

end OAI
