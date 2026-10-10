import Mathlib
import OAI.Algebra.FrobeniusObstruction.FormalData

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι κ k : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Field k]
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell]

theorem tangentCoeff_eq_augmentation_partial (i : ι) (x : Ring (ι := ι) (k := k) ell) :
    tangentCoeff ell htwo i x = augmentation ell (by omega) (partialDeriv ell i x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [tangentCoeff_mk, partial_mk]
  change _ = MvPowerSeries.constantCoeff (MvPowerSeries.pderiv i p)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_pderiv]
  simp

omit [DecidableEq κ] [CharP k ell] in
theorem augmentation_natural (f : Ring (ι := ι) (k := k) ell →ₐ[k]
    Ring (ι := κ) (k := k) ell) :
    (augmentation ell (by omega)).comp f = augmentation ell (by omega) := by
  apply algHom_ext
  intro i
  rw [AlgHom.comp_apply, augmentation_coordinate]
  apply eq_zero_of_pow_eq_zero (n := ell)
  rw [← map_pow, ← map_pow, coordinate_pow, map_zero, map_zero]

theorem tangentCoeff_chain_rule (f : Ring (ι := ι) (k := k) ell →ₐ[k]
    Ring (ι := κ) (k := k) ell) (j : κ) (x : Ring (ι := ι) (k := k) ell) :
    tangentCoeff ell htwo j (f x) = ∑ i, tangentCoeff ell htwo i x *
      tangentCoeff ell htwo j (f (coordinate ell i)) := by
  rw [tangentCoeff_eq_augmentation_partial, partial_chain_rule, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, ← tangentCoeff_eq_augmentation_partial,
    ← AlgHom.comp_apply, augmentation_natural ell htwo f, ← tangentCoeff_eq_augmentation_partial]

end BoundaryOnly.FormalObstruction.Frobenius

namespace BoundaryOnly.FormalObstruction
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime]
open Frobenius

                                                                        
theorem graph_constant_zero (D : FormalData (k := k) n) (c : InternalVar n) :
    MvPowerSeries.constantCoeff (D.Y c) = 0 := by
  have h : originIdeal k (GraphVar n) ≤ RingHom.ker MvPowerSeries.constantCoeff := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp
  exact h (D.centered c)

                                                                            
                             
def graphSlot (b : Bool) : Frobenius.Ring (ι := GraphVar n) (k := k) ell →ₐ[k]
    Frobenius.Ring (ι := InternalVar n) (k := k) ell :=
  eval ell (fun v => match v with
    | .inl _ => 0
    | .inr t => coordinate ell (b,t)) (by
      intro v
      cases v with
      | inl a => exact zero_pow (Nat.Prime.ne_zero Fact.out)
      | inr t => exact coordinate_pow ell (b,t))

omit [CharP k ell] in
@[simp] theorem graphSlot_slope (b : Bool) (a : SlopeVar d) :
    graphSlot (n := n) (k := k) ell b (coordinate ell (.inl a)) = 0 :=
  eval_coordinate ell _ _ _

omit [CharP k ell] in
@[simp] theorem graphSlot_tangent (b : Bool) (t : TangentVar n) :
    graphSlot (k := k) ell b (coordinate ell (.inr t)) = coordinate ell (b,t) :=
  eval_coordinate ell _ _ _

                                                                             
def fixedComplement (D : FormalData (k := k) n) (c : InternalVar n) :
    Frobenius.Ring (ι := InternalVar n) (k := k) ell :=
  ∑ t : TangentVar n, tangentMatrix n D.Y (swapBlocks n c) t • coordinate ell (true,t)

omit [CharP k ell] in
@[simp] theorem fixedComplement_augmentation (D : FormalData (k := k) n) (c : InternalVar n) :
    augmentation ell (Nat.Prime.pos Fact.out) (fixedComplement ell D c) = 0 := by
  simp [fixedComplement]

theorem fixedComplement_pow (D : FormalData (k := k) n) (c : InternalVar n) :
    fixedComplement ell D c ^ ell = 0 := by
  apply frobenius_zero_of_constant
  change (augmentation ell (Nat.Prime.pos Fact.out) (fixedComplement ell D c)) ^ ell = 0
  rw [fixedComplement_augmentation, zero_pow (Nat.Prime.ne_zero Fact.out)]

def specialChartCoordinate (D : FormalData (k := k) n) (c : InternalVar n) :
    Frobenius.Ring (ι := InternalVar n) (k := k) ell :=
  graphSlot ell false (Ideal.Quotient.mk _ (D.Y c)) + fixedComplement ell D c

theorem specialChartCoordinate_pow (D : FormalData (k := k) n) (c : InternalVar n) :
    specialChartCoordinate ell D c ^ ell = 0 := by
  have h (c : InternalVar n) :
      (Ideal.Quotient.mk (powerIdeal (k := k) ell) (D.Y c)) ^ ell = 0 := by
    apply frobenius_zero_of_constant
    rw [constantHom_mk, graph_constant_zero D c]
    exact zero_pow (Nat.Prime.ne_zero Fact.out)
  let : CharP (Frobenius.Ring (ι := InternalVar n) (k := k) ell) ell :=
    quotient_charP (Nat.Prime.pos Fact.out)
  have hslot :
      (graphSlot ell false (Ideal.Quotient.mk _ (D.Y c))) ^ ell = 0 := by
    rw [← map_pow, h, map_zero]
  rw [specialChartCoordinate, add_pow_char, hslot, fixedComplement_pow, zero_add]

                                                                        
def specialChart (D : FormalData (k := k) n) :
    Frobenius.Ring (ι := InternalVar n) (k := k) ell →ₐ[k]
      Frobenius.Ring (ι := InternalVar n) (k := k) ell :=
  eval ell (specialChartCoordinate ell D) (specialChartCoordinate_pow ell D)

@[simp] theorem specialChart_coordinate (D : FormalData (k := k) n) (c : InternalVar n) :
    specialChart ell D (coordinate ell c) = specialChartCoordinate ell D c :=
  eval_coordinate ell _ _ _

theorem graphSlot_tangentCoeff (b : Bool) (j : InternalVar n)
    (x : Frobenius.Ring (ι := GraphVar n) (k := k) ell) :
    tangentCoeff ell htwo j (graphSlot ell b x) =
      if j.1 = b then tangentCoeff ell htwo (.inr j.2) x else 0 := by
  rw [tangentCoeff_chain_rule]
  rw [Fintype.sum_sum_type]
  simp only [graphSlot_slope, map_zero, mul_zero, Finset.sum_const_zero, zero_add,
    graphSlot_tangent, tangentCoeff_coordinate]
  obtain ⟨b', t⟩ := j
  by_cases hb : b' = b
  · subst b'
    simp only [Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  · simp only [Prod.mk.injEq, hb, false_and, ite_false, mul_zero, Finset.sum_const_zero]

omit [CharP k ell] [Fact (Nat.Prime ell)] in
theorem fixedComplement_tangentCoeff (D : FormalData (k := k) n)
    (c j : InternalVar n) :
    tangentCoeff ell htwo j (fixedComplement ell D c) =
      if j.1 then tangentMatrix n D.Y (swapBlocks n c) j.2 else 0 := by
  unfold fixedComplement
  simp only [map_sum, map_smul, tangentCoeff_coordinate, smul_eq_mul]
  obtain ⟨b,t⟩ := j
  cases b <;> simp

theorem specialChart_tangent_matrix (D : FormalData (k := k) n) :
    (fun i j => tangentCoeff ell htwo j (specialChart ell D (coordinate ell i))) =
      complementaryMatrix n D.Y := by
  funext i j
  rw [specialChart_coordinate, specialChartCoordinate, map_add,
    graphSlot_tangentCoeff, fixedComplement_tangentCoeff]
  have h (c : InternalVar n) : tangentCoeff ell htwo (.inr j.2)
        (Ideal.Quotient.mk (powerIdeal (k := k) ell) (D.Y c)) = tangentMatrix n D.Y c j.2 := by
    rw [tangentCoeff_eq_augmentation_partial, partial_mk]
    rfl
  rw [h]
  obtain ⟨b,t⟩ := j
  cases b <;> simp [complementaryMatrix]

include htwo in
theorem specialChart_bijective (D : FormalData (k := k) n) :
    Function.Bijective (specialChart ell D) := by
  apply bijective_of_tangent_matrix ell htwo
  rw [specialChart_tangent_matrix]
  exact isUnit_iff_ne_zero.mpr D.complementary

def specialChartEquiv (D : FormalData (k := k) n) :
    Frobenius.Ring (ι := InternalVar n) (k := k) ell ≃ₐ[k]
      Frobenius.Ring (ι := InternalVar n) (k := k) ell :=
  AlgEquiv.ofBijective (specialChart ell D) (specialChart_bijective ell htwo D)

end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k]
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell]

def tangentJacobian (f : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell) :
    Matrix ι ι k := fun i j => tangentCoeff ell htwo j (f (coordinate ell i))

theorem tangentJacobian_comp
    (f g : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι) (k := k) ell) :
    tangentJacobian ell htwo (f.comp g) =
      tangentJacobian ell htwo g * tangentJacobian ell htwo f := by
  ext i j
  exact tangentCoeff_chain_rule ell htwo f j (g (coordinate ell i))

omit [CharP k ell] in
@[simp] theorem tangentJacobian_id :
    tangentJacobian (ι := ι) (k := k) ell htwo (AlgHom.id k _) = 1 := by
  ext i j
  simp only [tangentJacobian, AlgHom.id_apply, tangentCoeff_coordinate, Matrix.one_apply]
  by_cases h : i = j
  · subst j; simp only [ite_true]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

                                                                              
                                                                           
theorem tangentJacobian_det_unit
    (f : Ring (ι := ι) (k := k) ell ≃ₐ[k] Ring (ι := ι) (k := k) ell) :
    IsUnit (tangentJacobian ell htwo f.toAlgHom).det := by
  have he : f.symm.toAlgHom.comp f.toAlgHom = AlgHom.id k _ := by
    ext x
    exact f.symm_apply_apply x
  have hm := tangentJacobian_comp ell htwo f.symm.toAlgHom f.toAlgHom
  rw [he, tangentJacobian_id] at hm
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_one, Matrix.det_mul] at hd
  apply isUnit_iff_ne_zero.mpr
  intro h
  rw [h, zero_mul] at hd
  exact one_ne_zero hd

end BoundaryOnly.FormalObstruction.Frobenius

end

end OAI
