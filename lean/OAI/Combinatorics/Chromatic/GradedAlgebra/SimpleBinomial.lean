import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SimpleIncomingData
import OAI.Combinatorics.Chromatic.Walls.FiniteElementaryAdjoint

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
def normalizedSimple (p : M) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  raySeries LaurentRay.vUnit Ω p
    (elementary (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (1:ℤ) (1:ℚ)))
omit [Fintype I] in
lemma simpleDatum_value (pc : I) : (simpleDatum C pc).value Ω=normalizedSimple Ω (simpleRoot C pc) := by
  apply PowerSeries.ext
  intro n
  rw [WallUnitDatum.value,coeff_weightedRay]
  simp only [simpleDatum,one_dvd,Nat.div_one,UnitSelections.indexedUnit,↓reduceIte,
    LaurentRay.elementary_atInfinity,neg_neg,coeff_raySeries,normalizedSimple]
lemma normalizedSimple_constant (p : M) : constantCoeff (normalizedSimple Ω p)=1 := by
  rw [←coeff_zero_eq_constantCoeff]
  rw [normalizedSimple,coeff_raySeries,zero_nsmul,coeff_zero_eq_constantCoeff,constant_elementary]
  rfl
lemma normalizedSimple_inverse (hΩ : ∀m,Ω m m=0) (p : M) :
    invOfUnit (normalizedSimple Ω p) 1=
      raySeries LaurentRay.vUnit Ω p
        (elementary (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (1:ℤ) (1:ℚ)))⁻¹ := by
  let U:=rayUnit LaurentRay.vUnit Ω p (hΩ p)
    (elementary (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (1:ℤ) (1:ℚ))) (constant_elementary _ _)
  change invOfUnit U.val 1=U.inv
  calc
    _=invOfUnit U.val 1*(U.val*U.inv):=by rw [U.val_inv,mul_one]
    _=(invOfUnit U.val 1*U.val)*U.inv:=by rw [mul_assoc]
    _=U.inv:=by rw [invOfUnit_mul U.val 1 (normalizedSimple_constant Ω p),one_mul]
lemma laurent_q_nonzero : (HahnSeries.single (2:ℤ) (1:ℚ) : LaurentSeries ℚ)≠0 := by
  rw [←LaurentRay.atInfinity_q]
  intro hz
  exact RationalRay.q_nonzero (LaurentRay.atInfinity_injective (hz.trans (map_zero _).symm))
lemma laurent_shift_positive (t : ℕ) :
    (↑(LaurentRay.vUnit^(2*(t:ℤ))) : LaurentSeries ℚ)=
      (HahnSeries.single (2:ℤ) (1:ℚ))⁻¹^t := by
  rw [LaurentRay.vUnit_zpow,←LaurentRay.atInfinity_v_pow,←LaurentRay.atInfinity_q,←map_inv₀,←map_pow]
  congr 1
  rw [inv_pow,RationalRay.q_pow,←zpow_neg]
  congr 1
  ring
lemma laurent_shift_negative (t : ℕ) :
    (↑(LaurentRay.vUnit^(2*(-(t:ℤ)))) : LaurentSeries ℚ)=
      (HahnSeries.single (2:ℤ) (1:ℚ))^t := by
  rw [LaurentRay.vUnit_zpow,←LaurentRay.atInfinity_v_pow,←LaurentRay.atInfinity_q,←map_pow,RationalRay.q_pow]
  congr 2
  ring
lemma normalizedSimple_adjoint_support (hΩ : ∀m,Ω m m=0) (p m x : M) (t N : ℕ)
    (ht : Ω p m=(t:ℤ))
    (hx : coeff N (adjoint (normalizedSimple Ω p) (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) x≠0) :
    N≤t ∧ x=m+N • p := by
  rw [adjoint,normalizedSimple_inverse Ω hΩ p] at hx
  exact elementary_adjoint_support LaurentRay.vUnit Ω hΩ p m x _ _ laurent_q_nonzero
    UnitSelections.laurent_q_not_root t N (by rw [ht]; exact laurent_shift_positive t) hx
lemma normalizedSimple_inverse_adjoint_support (hΩ : ∀m,Ω m m=0) (p m x : M) (t N : ℕ)
    (ht : Ω p m= -(t:ℤ))
    (hx : coeff N (adjoint (invOfUnit (normalizedSimple Ω p) 1)
      (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) x≠0) : N≤t ∧ x=m+N • p := by
  rw [adjoint_inverse _ _ (normalizedSimple_constant Ω p),normalizedSimple_inverse Ω hΩ p] at hx
  exact elementary_inverse_adjoint_support LaurentRay.vUnit Ω hΩ p m x _ _ laurent_q_nonzero
    UnitSelections.laurent_q_not_root t N (by rw [ht]; exact laurent_shift_negative t) hx
end
end ElementaryPositivity.QuantumTorus

end

end OAI
