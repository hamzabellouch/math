import Mathlib
import OAI.Algebra.FrobeniusObstruction.ChartPairing

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction
open Frobenius MixedForms
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime]

                                                                                       
def wallSpecial (b : Bool) (i : Fin d) :
    Frobenius.Ring (ι := WallVar n i) (k := k) ell →ₐ[k]
      Frobenius.Ring (ι := InternalVar n) (k := k) ell :=
  eval ell (Sum.elim (fun _ => 0) (fun y => coordinate ell (b,⟨i,y⟩))) (by
    intro v
    cases v with
    | inl _ => exact zero_pow (Nat.Prime.ne_zero Fact.out)
    | inr y => exact coordinate_pow ell _)

omit [CharP k ell] in
@[simp] theorem wallSpecial_slope (b : Bool) (i : Fin d) (j : Fin 3) :
    wallSpecial (n := n) (k := k) ell b i (coordinate ell (.inl j)) = 0 :=
  eval_coordinate ell _ _ _

omit [CharP k ell] in
@[simp] theorem wallSpecial_internal (b : Bool) (i : Fin d) (y : Fin (n i)) :
    wallSpecial (k := k) ell b i (coordinate ell (.inr y)) = coordinate ell (b,⟨i,y⟩) :=
  eval_coordinate ell _ _ _

 theorem plusCoordinates_constant_zero (i : Fin d) (v : WallVar n i) :
    MvPowerSeries.constantCoeff (plusCoordinates (k := k) n i v) = 0 := by
  cases v <;> simp [plusCoordinates]

 theorem minusCoordinates_constant_zero (i : Fin d) (v : WallVar n i) :
    MvPowerSeries.constantCoeff (minusCoordinates (k := k) n i v) = 0 := by
  cases v <;> simp [minusCoordinates]

 theorem specialAmbient_plus (i : Fin d) (p : MvPowerSeries (WallVar n i) k) :
    specialAmbient (n := n) (k := k) ell (Ideal.Quotient.mk _ (MvPowerSeries.subst (plusCoordinates n i) p)) =
      wallSpecial ell true i (Ideal.Quotient.mk _ p) := by
  have hh : (specialAmbient (n := n) (k := k) ell).comp
      (substitute ell (plusCoordinates n i) (plusCoordinates_constant_zero i)) =
      wallSpecial ell true i := by
    apply algHom_ext
    intro v
    simp only [AlgHom.comp_apply, substitute_coordinate]
    cases v with
    | inl j =>
      rw [wallSpecial_slope]
      exact specialAmbient_slope ell (i,j)
    | inr y =>
      rw [wallSpecial_internal]
      exact specialAmbient_internal ell (true,⟨i,y⟩)
  simpa only [AlgHom.comp_apply, substitute_mk] using
    AlgHom.congr_fun hh (Ideal.Quotient.mk _ p)

 theorem specialAmbient_minus (i : Fin d) (p : MvPowerSeries (WallVar n i) k) :
    specialAmbient (n := n) (k := k) ell (Ideal.Quotient.mk _ (MvPowerSeries.subst (minusCoordinates n i) p)) =
      wallSpecial ell false i (Ideal.Quotient.mk _ p) := by
  have hh : (specialAmbient (n := n) (k := k) ell).comp
      (substitute ell (minusCoordinates n i) (minusCoordinates_constant_zero i)) =
      wallSpecial ell false i := by
    apply algHom_ext
    intro v
    simp only [AlgHom.comp_apply, substitute_coordinate]
    cases v with
    | inl j => simp only [minusCoordinates, map_zero, wallSpecial_slope]
    | inr y =>
      rw [wallSpecial_internal]
      exact specialAmbient_internal ell (false,⟨i,y⟩)
  simpa only [AlgHom.comp_apply, substitute_mk] using
    AlgHom.congr_fun hh (Ideal.Quotient.mk _ p)

 theorem specialPotential_separated (D : FormalData (k := k) n) :
    specialPotential ell D = ∑ i,
      (wallSpecial ell true i (Ideal.Quotient.mk _ (D.P i)) -
       wallSpecial ell false i (Ideal.Quotient.mk _ (D.P i))) := by
  simp only [specialPotential, potential, map_sum, map_sub,
    specialAmbient_plus, specialAmbient_minus]

omit [CharP k ell] in
 theorem swap_wallSpecial (b : Bool) (i : Fin d)
    (x : Frobenius.Ring (ι := WallVar n i) (k := k) ell) :
    Frobenius.reindex ell swapEquiv (wallSpecial ell b i x) = wallSpecial ell (!b) i x := by
  have hh : (Frobenius.reindex (k := k) ell (swapEquiv (n := n))).toAlgHom.comp
      (wallSpecial (k := k) ell b i) = wallSpecial ell (!b) i := by
    apply algHom_ext
    intro v
    cases v <;> simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      wallSpecial_slope, wallSpecial_internal, map_zero,
      reindex_coordinate, swapEquiv_apply]
  exact AlgHom.congr_fun hh x

 theorem specialPotential_swap (D : FormalData (k := k) n) :
    Frobenius.reindex ell swapEquiv (specialPotential ell D) = -specialPotential ell D := by
  rw [specialPotential_separated]
  simp only [map_sum, map_sub, swap_wallSpecial, Bool.not_true, Bool.not_false]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  abel

 theorem negativeNormal_d (D : FormalData (k := k) n) :
    MixedForms.d (partialDeriv ell) (negativeNormal ell htwo D) = 0 := by
  rw [negativeNormal, ← FormsReindex.equiv_d, specialNormal_d, map_zero]

omit [Fact ell.Prime] in
 theorem gradient_neg (x : Frobenius.Ring (ι := InternalVar n) (k := k) ell) :
    MixedForms.gradient (partialDeriv ell) (-x) = -MixedForms.gradient (partialDeriv ell) x := by
  change MixedForms.d (partialDeriv ell) (coeff (-x)) = -MixedForms.d (partialDeriv ell) (coeff x)
  rw [map_neg, map_neg]

 theorem negativeNormal_delta (D : FormalData (k := k) n) :
    delta (partialDeriv ell) (specialPotential ell D) (negativeNormal ell htwo D) = 0 := by
  have hh := congrArg (FormsReindex.equiv ell swapEquiv) (specialNormal_delta ell htwo D)
  rw [FormsReindex.equiv_delta, specialPotential_swap, map_zero, delta_apply,
    gradient_neg, neg_mul, neg_eq_zero] at hh
  exact hh

                                                          
def specialSlope (D : FormalData (k := k) n) (b : Bool) (i : Fin d) :
    Frobenius.Ring (ι := InternalVar n) (k := k) ell :=
  includeVariables ell (fun y => (b,⟨i,y⟩))
    (Ideal.Quotient.mk _ (slopeDerivative n D.P i))

omit [CharP k ell] [Fact ell.Prime] in
 theorem specialSlope_swap (D : FormalData (k := k) n) (b : Bool) (i : Fin d) :
    Frobenius.reindex ell swapEquiv (specialSlope ell D b i) = specialSlope ell D (!b) i := by
  have hh : (Frobenius.reindex (k := k) ell (swapEquiv (n := n))).toAlgHom.comp
      (includeVariables (k := k) ell (fun y : Fin (n i) => ((b,⟨i,y⟩) : InternalVar n))) =
      includeVariables ell (fun y : Fin (n i) => ((!b,⟨i,y⟩) : InternalVar n)) := by
    apply algHom_ext
    intro y
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      includeVariables_coordinate, reindex_coordinate, swapEquiv_apply]
  exact AlgHom.congr_fun hh _

omit [CharP k ell] in
 theorem specialPlane_graphSlot (x : Frobenius.Ring (ι := GraphVar n) (k := k) ell) :
    planeRestriction ell (by omega) normalIndices (graphSlot ell false x) = graphSlot ell false x := by
  have hh : (planeRestriction (k := k) ell (by omega) (normalIndices (n := n))).comp (graphSlot ell false) =
      graphSlot ell false := by
    apply algHom_ext
    intro v
    cases v <;> simp only [AlgHom.comp_apply, graphSlot_slope, graphSlot_tangent,
      map_zero, planeRestriction_coordinate, mem_normalIndices, Bool.false_eq_true, ite_false]
  exact AlgHom.congr_fun hh x

omit [CharP k ell] [Fact ell.Prime] in
 theorem specialPlane_fixedComplement (D : FormalData (k := k) n) (c : InternalVar n) :
    planeRestriction ell (by omega) normalIndices (fixedComplement ell D c) = 0 := by
  simp only [fixedComplement, map_sum, map_smul, planeRestriction_coordinate,
    mem_normalIndices, ite_true, smul_zero, Finset.sum_const_zero]

 theorem specialSlope_restriction (D : FormalData (k := k) n) (i : Fin d) :
    planeRestriction ell (by omega) normalIndices (specialChart ell D (specialSlope ell D false i)) =
      graphSlot ell false (Ideal.Quotient.mk _ (negativeSlopeValue n D.P D.Y i)) := by
  have ha (y : Fin (n i)) : MvPowerSeries.constantCoeff (D.Y (false,⟨i,y⟩)) = 0 :=
    graph_constant_zero D _
  have hh : ((planeRestriction ell (by omega) (normalIndices (n := n))).comp (specialChart ell D)).comp
      (includeVariables ell (fun y : Fin (n i) => ((false,⟨i,y⟩) : InternalVar n))) =
      (graphSlot ell false).comp (substitute ell (fun y : Fin (n i) => D.Y (false,⟨i,y⟩)) ha) := by
    apply algHom_ext
    intro y
    simp only [AlgHom.comp_apply, includeVariables_coordinate, specialChart_coordinate,
      specialChartCoordinate, map_add, specialPlane_fixedComplement ell htwo D, add_zero,
      specialPlane_graphSlot ell htwo, substitute_coordinate]
  simpa only [AlgHom.comp_apply, substitute_mk, specialSlope, negativeSlopeValue] using
    AlgHom.congr_fun hh (Ideal.Quotient.mk _ (slopeDerivative n D.P i))

 theorem specialSlope_mul_normal (D : FormalData (k := k) n) (i : Fin d) :
    coeff (specialSlope ell D false i) * specialNormal ell htwo D =
      coeff ((specialChartEquiv ell htwo D).symm
        (graphSlot ell false (Ideal.Quotient.mk _ (negativeSlopeValue n D.P D.Y i)))) *
        specialNormal ell htwo D := by
  apply sub_eq_zero.mp
  rw [← sub_mul, ← map_sub]
  apply chartNormal_annihilate ell (by omega)
  apply (chart_restriction_eq_zero_iff ell (by omega) (specialChartEquiv ell htwo D).symm
    normalIndices _).mp
  simp only [map_sub, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply,
    specialPlane_graphSlot ell htwo]
  exact sub_eq_zero.mpr (specialSlope_restriction ell htwo D i)

omit [CharP k ell] [Fact ell.Prime] in
 theorem specialPlane_idempotent (x : Frobenius.Ring (ι := InternalVar n) (k := k) ell) :
    planeRestriction ell (show 0 < ell by omega) normalIndices
      (planeRestriction ell (show 0 < ell by omega) normalIndices x) =
        planeRestriction ell (show 0 < ell by omega) normalIndices x := by
  have hh : (planeRestriction (ι := InternalVar n) (k := k) ell (by omega) normalIndices).comp
      (planeRestriction ell (by omega) normalIndices) =
        planeRestriction ell (by omega) normalIndices := by
    apply algHom_ext
    intro i
    by_cases hi : i ∈ normalIndices
    · simp only [AlgHom.comp_apply, planeRestriction_coordinate, ite_eq_left hi, map_zero]
    · simp only [AlgHom.comp_apply, planeRestriction_coordinate, ite_eq_right hi]
  exact AlgHom.congr_fun hh x

 theorem specialScalar_mul_normal (D : FormalData (k := k) n)
    (x : Frobenius.Ring (ι := InternalVar n) (k := k) ell) :
    coeff x * specialNormal ell htwo D =
      coeff ((specialChartEquiv ell htwo D).symm
        (planeRestriction ell (by omega) normalIndices (specialChart ell D x))) *
          specialNormal ell htwo D := by
  apply sub_eq_zero.mp
  rw [← sub_mul, ← map_sub]
  apply chartNormal_annihilate ell (by omega)
  apply (chart_restriction_eq_zero_iff ell (by omega) (specialChartEquiv ell htwo D).symm
    normalIndices _).mp
  simp only [map_sub, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply,
    specialPlane_idempotent ell htwo]
  exact sub_self _

 theorem specialNegativeTriple_boundary (D : FormalData (k := k) n) (i j l : Fin d) :
    ∃ eta : Forms (k := k) (A := Frobenius.Ring (ι := InternalVar n) (k := k) ell)
        (ι := InternalVar n),
      delta (partialDeriv ell) (specialPotential ell D) eta =
        coeff (specialSlope ell D false i * specialSlope ell D false j * specialSlope ell D false l) *
          specialNormal ell htwo D := by
  obtain ⟨eta,he⟩ := specialNormal_primitive ell htwo D _ (D.negative_cubic i j l)
  refine ⟨eta, he.trans ?_⟩
  symm
  calc
    _ = coeff ((specialChartEquiv ell htwo D).symm
      (planeRestriction ell (by omega) normalIndices
        (specialChart ell D (specialSlope ell D false i * specialSlope ell D false j * specialSlope ell D false l)))) *
        specialNormal ell htwo D := specialScalar_mul_normal ell htwo D _
    _ = _ := by simp only [map_mul, specialSlope_restriction ell htwo D]

                                                                                         
 theorem negativeNormal_triple (D : FormalData (k := k) n) (i j l : Fin d) :
    ∃ eta : Forms (k := k) (A := Frobenius.Ring (ι := InternalVar n) (k := k) ell)
        (ι := InternalVar n),
      delta (partialDeriv ell) (specialPotential ell D) eta =
        coeff (specialSlope ell D true i * specialSlope ell D true j * specialSlope ell D true l) *
          negativeNormal ell htwo D := by
  obtain ⟨eta,he⟩ := specialNegativeTriple_boundary ell htwo D i j l
  refine ⟨-FormsReindex.equiv ell swapEquiv eta, ?_⟩
  have hh := congrArg (FormsReindex.equiv ell swapEquiv) he
  rw [FormsReindex.equiv_delta, specialPotential_swap] at hh
  simp only [map_mul, FormsReindex.equiv_coeff, specialSlope_swap] at hh
  simp only [Bool.not_false] at hh
  rw [delta_apply, gradient_neg, neg_mul] at hh
  simpa only [delta_apply, mul_neg, map_mul, negativeNormal] using hh

end BoundaryOnly.FormalObstruction

end

end OAI
