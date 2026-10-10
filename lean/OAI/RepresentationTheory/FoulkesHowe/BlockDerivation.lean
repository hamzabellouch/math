import Mathlib

namespace OAI

/-! Coordinate-block derivations used in the differential-shift argument. -/

noncomputable section

namespace Problem346

open MvPolynomial
open scoped BigOperators

variable (R : Type*) [CommRing R]
variable {ι κ : Type*} [DecidableEq ι]

/-- Move one unit of polynomial degree from block `u` to block `v`.
The other coordinate blocks are spectators. -/
def blockShift (u v : ι) :
    Derivation R (MvPolynomial (ι × κ) R) (MvPolynomial (ι × κ) R) :=
  MvPolynomial.mkDerivation R (fun k => if k.1 = u then X (v, k.2) else 0)

@[simp] theorem blockShift_X (u v k : ι) (l : κ) :
    blockShift (κ := κ) R u v (X (k, l)) = if k = u then X (v, l) else 0 :=
  MvPolynomial.mkDerivation_X R _ _

/-- The commutator of opposite block shifts is the difference of the two
block Euler operators. This identity needs no finiteness assumption. -/
theorem blockShift_commutator (u v : ι) :
    ⁅blockShift (κ := κ) R v u, blockShift (κ := κ) R u v⁆ =
      blockShift (κ := κ) R u u - blockShift (κ := κ) R v v := by
  apply MvPolynomial.derivation_ext
  rintro ⟨k, l⟩
  simp only [Derivation.commutator_apply, Derivation.sub_apply, blockShift_X]
  by_cases huv : u = v
  · subst v
    simp
  · by_cases hu : k = u <;> by_cases hv : k = v <;>
      simp_all

/-- The weight operator raises the weight of the reverse shift by two. -/
theorem blockShift_weight_commutator (u v : ι) (huv : u ≠ v) :
    ⁅blockShift (κ := κ) R u u - blockShift (κ := κ) R v v, blockShift (κ := κ) R v u⁆ =
      (2 : R) • blockShift (κ := κ) R v u := by
  apply MvPolynomial.derivation_ext
  rintro ⟨k, l⟩
  simp only [Derivation.commutator_apply, Derivation.sub_apply,
    Derivation.smul_apply, blockShift_X]
  by_cases hu : k = u <;> by_cases hv : k = v <;>
    simp [hu, hv, huv, Ne.symm huv, two_smul]

/-- Pointwise version of the opposite-shift commutator. -/
theorem blockShift_commutator_apply (u v : ι) (f : MvPolynomial (ι × κ) R) :
    blockShift (κ := κ) R v u (blockShift (κ := κ) R u v f) -
        blockShift (κ := κ) R u v (blockShift (κ := κ) R v u f) =
      blockShift (κ := κ) R u u f - blockShift (κ := κ) R v v f := by
  have h := congrArg (fun D : Derivation R (MvPolynomial (ι × κ) R)
      (MvPolynomial (ι × κ) R) => D f) (blockShift_commutator R u v)
  exact h

/-- Pointwise version of the weight/raising commutator. -/
theorem blockShift_weight_commutator_apply (u v : ι) (huv : u ≠ v)
    (f : MvPolynomial (ι × κ) R) :
    (blockShift (κ := κ) R u u - blockShift (κ := κ) R v v) (blockShift (κ := κ) R v u f) -
      blockShift (κ := κ) R v u ((blockShift (κ := κ) R u u - blockShift (κ := κ) R v v) f) =
      (2 : R) • blockShift (κ := κ) R v u f := by
  have h := congrArg (fun D : Derivation R (MvPolynomial (ι × κ) R)
      (MvPolynomial (ι × κ) R) => D f) (blockShift_weight_commutator R u v huv)
  exact h

/-- An off-diagonal block shift squares to zero on each coordinate generator. -/
theorem blockShift_square_X (u v k : ι) (huv : u ≠ v) (l : κ) :
    blockShift (κ := κ) R u v (blockShift R u v (X (k, l))) = 0 := by
  by_cases h : k = u <;> simp [h, Ne.symm huv]

/-- With finitely many coordinates, `blockShift` is the usual directional
partial derivative, written as a sum of coordinate derivations. -/
theorem blockShift_eq_sum [Fintype κ] (u v : ι) :
    blockShift (κ := κ) R u v =
      ∑ l : κ, (X (v, l) : MvPolynomial (ι × κ) R) • pderiv (u, l) := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨k, m⟩
  rw [blockShift_X]
  have heval (ds : κ → Derivation R (MvPolynomial (ι × κ) R)
      (MvPolynomial (ι × κ) R)) (f : MvPolynomial (ι × κ) R) :
      (∑ l, ds l) f = ∑ l, ds l f := by
    simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using
      congrFun (map_sum Derivation.coeFnAddMonoidHom ds Finset.univ) f
  rw [heval]
  simp only [Derivation.smul_apply, smul_eq_mul, pderiv_X, Pi.single_apply,
    Prod.mk.injEq]
  by_cases h : k = u
  · subst k
    simp
  · simp [h]

end Problem346

end

end OAI
