import OAI.GroupTheory.PolycyclicRecognition.Algebra.HomogeneousUniversalLogarithm

namespace OAI

/-! # Explicit degree components of weighted words -/

noncomputable section
namespace PolycyclicRecognition

variable {c n d : ℕ}

theorem weightedWord_coefficient (w : FreeMonoid (Fin n)) (hd : d ≤ c) :
    monoidCoefficientLinear (truncatedScalarCoefficient c d) (weightedWord c n w) =
      if w.length = d then MonoidAlgebra.single w 1 else 0 := by
  rw [weightedWord, monoidCoefficientLinear_single]
  by_cases hw : w.length ≤ c
  · rw [truncatedScalarCoefficient_parameter_pow c w.length d hw]
    split_ifs <;> simp
  · have hz : truncatedScalarParameter c ^ w.length = 0 :=
      pow_eq_zero_of_le (Nat.lt_of_not_ge hw) (truncatedScalarParameter_pow c)
    have hwd : w.length ≠ d := by omega
    rw [hz, map_zero, MonoidAlgebra.single_zero, ite_eq_right hwd]

theorem homogeneous_degree_zero_eq_single {p : RationalWords n}
    (hp : IsHomogeneousRationalWord p 0) : p = MonoidAlgebra.single 1 (p.coeff 1) := by
  classical
  ext w
  by_cases hw : w = 1
  · subst w; simp
  · have hz : p.coeff w = 0 := by
      by_contra h
      have hlen := hp w h
      have hlist : w.toList = [] := List.length_eq_zero_iff.mp hlen
      exact hw (FreeMonoid.toList.injective hlist)
    simp [hz, MonoidAlgebra.coeff_single, hw]

theorem primitive_homogeneous_degree_zero {p : RationalWords n}
    (hp : IsPrimitiveRationalWord p) (hd : IsHomogeneousRationalWord p 0) : p = 0 := by
  have he := homogeneous_degree_zero_eq_single hd
  have h := congrArg (monoidTensorCoordinates ℚ (FreeMonoid (Fin n)) (FreeMonoid (Fin n))) hp
  rw [← pairedWordCoproduct_eq_rational, map_add, monoidTensorCoordinates_tmul_one,
    monoidTensorCoordinates_one_tmul] at h
  rw [he] at h
  have hc := congrArg (fun q => q.coeff (1, 1)) h
  simp [pairedWordCoproduct, MonoidAlgebra.lift_single, FreeMonoid.lift_apply,
    MonoidAlgebra.one_def, smul_eq_mul] at hc
  have hs : (Finsupp.single (1 : FreeMonoid (Fin n) × FreeMonoid (Fin n))
      (p.coeff 1)) (1, 1) = p.coeff 1 := Finsupp.single_eq_same
  rw [hs] at hc
  have hq : p.coeff 1 = 0 := add_eq_left.mp hc.symm
  rw [he, hq]
  exact MonoidAlgebra.single_zero _

theorem universalLogarithmCoefficient_zero (c n : ℕ) : universalLogarithmCoefficient c n 0 = 0 :=
  primitive_homogeneous_degree_zero (universalLogarithmCoefficient_primitive c n 0)
    (universalLogarithmCoefficient_homogeneous c n 0)

end PolycyclicRecognition

end

end OAI
