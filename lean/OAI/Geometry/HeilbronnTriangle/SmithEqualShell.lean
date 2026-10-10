import OAI.Geometry.HeilbronnTriangle.SmithPlaneData
import OAI.Geometry.HeilbronnTriangle.RowLatticeEqualShell

namespace OAI


noncomputable section

namespace Problem355.PrimePowerData

open scoped BigOperators Matrix
open Matrix PrimitiveNormal IntegralPlaneLattice PairingDivisor

theorem equal_pair_shell_bound
    {B k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}
    (d : PrimePowerData B k C) (hB : 0 < B)
    (q : ℕ) [Fact q.Prime] (hBq : IsUnit (B : ZMod q))
    (i j : Fin 3) (hij : i ≠ j)
    (S : Finset (Fin 3 → ℤ)) (R N W : ℝ)
    (hR : 1 ≤ R) (hN : 0 ≤ N) (hW : 0 ≤ W)
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hshell : ∀ x ∈ S, R ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ ≤ 2 * R)
    (hspan : ∀ x ∈ S, ¬ ∃ a : ZMod q, (fun t => (x t : ZMod q)) =
      a • PlaneFunctional.coordinateDifference i j)
    (F : (Fin 3 → ℤ) → Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (weight : Matrix (Fin 3) (Fin 3) ℤ → ℝ)
    (hkernel : ∀ x ∈ S, ∀ A ∈ F x, A *ᵥ x = 0)
    (hrows : ∀ x ∈ S, ∀ A ∈ F x, ∀ t,
      A t ∈ RowLattice.integerRowLattice (B ^ k) C)
    (hequal : ∀ x ∈ S, ∀ A ∈ F x, ∀ t, (A t i : ZMod q) = (A t j : ZMod q))
    (hcoord : ∀ x ∈ S, ∀ A ∈ F x, ∀ s t, |(A s t : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ S, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hweight : ∀ x ∈ S, ∀ A ∈ F x, weight A ≤ W) :
    (∑ x ∈ S, ∑ A ∈ F x, weight A) ≤
      125 * W * (144 * Real.pi) ^ 3 * N ^ 6 * ((B : ℝ) ^ k) ^ 2 /
        ((q : ℝ) ^ 3 * ((B : ℝ) ^ (d.b + d.e)) ^ 2) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hi : 0 < (B : ℝ) ^ d.b * (B : ℝ) ^ d.e := by positivity
  have he := LatticeMoment.divisor_cube_div_index_le_modulus_sq
    B d.b d.e k (B ^ d.e) hB d.e_le_k (dvd_refl _)
  have he' : ((B ^ d.e : ℕ) : ℝ) ^ 3 ≤
      (B : ℝ) ^ (d.b + d.e) * ((B : ℝ) ^ k) ^ 2 := by
    simpa only [pow_add, mul_comm] using (div_le_iff₀ hi).mp he
  have hindex :
      (((RowLattice.integerRowLattice (B ^ k) C).toIntSubmodule.toAddSubgroup).index : ℝ) =
        (B : ℝ) ^ (d.b + d.e) := by
    change ((RowLattice.integerRowLattice (B ^ k) C).index : ℝ) = _
    rw [d.row_lattice_index (Nat.ne_of_gt hB)]
    simp only [Nat.cast_mul, Nat.cast_pow, pow_add]
  have h := RowLatticeEqualShell.weighted_matrix_shell_bound q
    (RowLattice.integerRowLattice (B ^ k) C).toIntSubmodule
    (B ^ d.e) (pow_pos hB _) (by simpa using hBq.pow d.e)
    d.multiple_mem_row_lattice i j hij S hprimitive hspan F
    (fun x hx A hA => ⟨hkernel x hx A hA, hrows x hx A hA⟩)
    weight R N ((B : ℝ) ^ (d.b + d.e)) ((B : ℝ) ^ k) W
    hR hN (by positivity) hW hindex he' hshell hequal hcoord hproj hweight
  convert h using 1
  ring

end Problem355.PrimePowerData

end

end OAI
