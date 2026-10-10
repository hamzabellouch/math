import OAI.Geometry.HeilbronnTriangle.MatrixSpecialRankTwo
import OAI.Geometry.HeilbronnTriangle.PrimePowerData

namespace OAI


noncomputable section

namespace Problem355.SmithSpecialRankTwo

open scoped BigOperators Matrix
open Matrix PrimitiveNormal RowLatticeMatrices

theorem weighted_matrix_shell_le
    {B k : ℕ} (hB : B.Prime)
    {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}
    (d : PrimePowerData B k C)
    (S : Finset (Fin 3 → ℤ)) (R q : ℕ) (hR : 0 < R)
    (hq : (B ^ k) ^ 100 < q)
    (hnorm : ∀ x ∈ S, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (i j l : Fin 3) (hli : l ≠ i) (hlj : l ≠ j)
    (hnonzero : ∀ x ∈ S, x l ≠ 0)
    (hline : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1})
    (F : (Fin 3 → ℤ) → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧
      ∀ t, A t ∈ RowLattice.integerRowLattice (B ^ k) C)
    (W : (Fin 3 → ℤ) → IntMatrix → ℝ)
    (N Cw : ℝ) (hN : 0 ≤ N) (hCw : 0 ≤ Cw)
    (hW : ∀ x ∈ S, ∀ A ∈ F x,
      W x A ≤ Cw * (q : ℝ) * ((B ^ k : ℕ) : ℝ) ^ 12)
    (hcoord : ∀ x ∈ S, ∀ A ∈ F x, ∀ s t, |(A s t : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ S, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t) :
    (∑ x ∈ S, ∑ A ∈ F x, W x A) ≤
      512 * (144 * Real.pi) ^ 3 * Cw * N ^ 6 /
        ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
  let L := (RowLattice.integerRowLattice (B ^ k) C).toIntSubmodule
  have hE : 0 < B ^ d.e := pow_pos hB.pos _
  have hcontain : ∀ v : Fin 3 → ℤ, (B ^ d.e) • v ∈ L :=
    d.multiple_mem_row_lattice
  have hindex : L.toAddSubgroup.index = B ^ d.b * B ^ d.e :=
    d.row_lattice_index hB.ne_zero
  have hqpos : 0 < q := (pow_pos (pow_pos hB.pos k) 100).trans hq
  have hparam : (((B ^ k : ℕ) : ℝ)) ^ 14 ≤ q := by
    exact_mod_cast (Nat.pow_le_pow_right (pow_pos hB.pos k)
      (by norm_num : 14 ≤ 100)).trans hq.le
  have hcube : ((B ^ d.e : ℕ) : ℝ) ^ 3 ≤
      ((B ^ d.b * B ^ d.e : ℕ) : ℝ) * ((B ^ k : ℕ) : ℝ) ^ 2 := by
    simpa only [pow_add] using
      (MatrixSpecialRankTwo.prime_power_cube_bound B d.b d.e k hB.one_lt.le d.e_le_k)
  have hc := MatrixSpecialRankTwo.weighted_matrix_shell_le S L (B ^ d.e)
    (B ^ d.b * B ^ d.e) R q hE (Nat.mul_pos (pow_pos hB.pos _) hE) hR hqpos
    hprimitive hcontain hindex hnorm i j l hli hlj hnonzero hline F hF W
    N (B ^ k : ℕ) Cw hN hCw hparam hcube hW hcoord hproj
  simpa only [Nat.cast_mul, Nat.cast_pow] using hc

end Problem355.SmithSpecialRankTwo

end

end OAI
