import OAI.Geometry.HeilbronnTriangle.IntegralPlaneReduction
import OAI.Geometry.HeilbronnTriangle.RowLattice
import OAI.Geometry.HeilbronnTriangle.PrimitiveNormal

namespace OAI


noncomputable section
namespace Problem355.RowPlaneReduction
open scoped LinearAlgebra.Projectivization
open IntegralPlaneReduction

abbrev rowModule (B k : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) :
    Submodule ℤ Vector := (RowLattice.integerRowLattice (B ^ k) C).toIntSubmodule

variable (B k b e : ℕ) (hbe : b ≤ e)
  (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
  (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
  (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
    DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
    (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))

include hbe hC

theorem larger_divisor_smul_mem (v : Vector) :
    ((B ^ e : ℕ) : ℤ) • v ∈ rowModule B k C := by
  rw [Nat.cast_smul_eq_nsmul]
  exact RowLattice.nsmul_mem_integerRowLattice_prime_power B k b e hbe C P Q hC v

theorem reduction_surjective (q : ℕ) [Fact q.Prime] (hcop : B.Coprime q)
    (x : Vector) (hx : PrimitiveNormal.IsPrimitive x) :
    Function.Surjective (reductionHom q (rowModule B k C) x) := by
  obtain ⟨z, hz⟩ := (PrimitiveNormal.isPrimitive_iff_exists_dot_eq_one x).mp hx
  have hE : IsUnit (((B ^ e : ℕ) : ℤ) : ZMod q) := by
    simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime (B ^ e) q).mpr (hcop.pow_left e)
  exact reductionHom_surjective q (rowModule B k C) x z hz ((B ^ e : ℕ) : ℤ) hE
    (larger_divisor_smul_mem B k b e hbe C P Q hC)

theorem line_index (q : ℕ) [Fact q.Prime] (hcop : B.Coprime q)
    (x : Vector) (hx : PrimitiveNormal.IsPrimitive x)
    (p : ℙ (ZMod q) (PlaneLines.normalMap (reducedNormal q x)).ker) :
    (lineLattice q (rowModule B k C) x p).index = q := by
  obtain ⟨z, hz⟩ := (PrimitiveNormal.isPrimitive_iff_exists_dot_eq_one x).mp hx
  have hE : IsUnit (((B ^ e : ℕ) : ℤ) : ZMod q) := by
    simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime (B ^ e) q).mpr (hcop.pow_left e)
  exact lineLattice_index q (rowModule B k C) x z hz ((B ^ e : ℕ) : ℤ) hE
    (larger_divisor_smul_mem B k b e hbe C P Q hC) p

theorem equal_coordinate_index (q : ℕ) [Fact q.Prime] (hcop : B.Coprime q)
    (x : Vector) (hx : PrimitiveNormal.IsPrimitive x) (i j : Fin 3) (hij : i ≠ j)
    (hspan : ¬ ∃ a : ZMod q,
      reducedNormal q x = a • PlaneFunctional.coordinateDifference i j) :
    (PlaneFunctional.equalCoordinateSubgroup q
      (integralPlane (rowModule B k C) x).toAddSubgroup i j).index = q := by
  obtain ⟨z, hz⟩ := (PrimitiveNormal.isPrimitive_iff_exists_dot_eq_one x).mp hx
  have hE : IsUnit (((B ^ e : ℕ) : ℤ) : ZMod q) := by
    simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime (B ^ e) q).mpr (hcop.pow_left e)
  exact equalCoordinate_index q (rowModule B k C) x z hz ((B ^ e : ℕ) : ℤ) hE
    (larger_divisor_smul_mem B k b e hbe C P Q hC) i j hij hspan

end Problem355.RowPlaneReduction

end

end OAI
