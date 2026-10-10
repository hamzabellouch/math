import OAI.Geometry.HeilbronnTriangle.SmithSpecialRankTwo
import OAI.Geometry.HeilbronnTriangle.AuxiliarySamplingLaw

namespace OAI


noncomputable section

namespace Problem355.AuxiliarySpecialRankTwo

open scoped BigOperators Matrix
open Matrix PrimitiveNormal RowLatticeMatrices LiftingProbability

theorem weighted_matrix_shell_le
    {B k : ℕ} (hB : B.Prime)
    {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}
    (d : PrimePowerData B k C)
    (S : Finset (Fin 3 → ℤ)) (R q : ℕ) [Fact q.Prime] (hR : 0 < R)
    (hq : (B ^ k) ^ 100 < q)
    (law : AuxiliarySampling.Law q ((B ^ k) ^ 2))
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
    (N : ℝ) (hN : 0 ≤ N)
    (hcoord : ∀ x ∈ S, ∀ A ∈ F x, ∀ s t, |(A s t : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ S, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hresidue : ∀ x ∈ S, ∀ A ∈ F x, ∃ u v : Fin 3,
      (A.map (Int.castRingHom (ZMod q))).col u ≠
        (A.map (Int.castRingHom (ZMod q))).col v) :
    (∑ x ∈ S, ∑ A ∈ F x, auxiliaryWeight q law.size law.weight law.sets
      (A.map (Int.castRingHom (ZMod q))).col) ≤
      512 * (144 * Real.pi) ^ 3 * (4 * 2000 ^ 3) * N ^ 6 /
        ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
  have hsizepos : (0 : ℝ) < law.size := by exact_mod_cast law.size_pos
  have hsize : (q : ℝ) ^ 2 ≤
      2000 ^ 3 * (((B ^ k : ℕ) : ℝ)) ^ 12 * law.size := by
    have hs := law.size_lower
    have hs' : (q : ℝ) ^ 2 ≤
        2000 ^ 3 * ((((B ^ k : ℕ) : ℝ)) ^ 2) ^ 6 * law.size := by
      exact_mod_cast hs
    simpa only [← pow_mul] using hs'
  have hratio : (q : ℝ) ^ 3 / law.size ≤
      2000 ^ 3 * (q : ℝ) * (((B ^ k : ℕ) : ℝ)) ^ 12 := by
    apply (div_le_iff₀ hsizepos).mpr
    calc
      (q : ℝ) ^ 3 = (q : ℝ) * (q : ℝ) ^ 2 := by ring
      _ ≤ (q : ℝ) * (2000 ^ 3 * (((B ^ k : ℕ) : ℝ)) ^ 12 * law.size) :=
        mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg q)
      _ = _ := by ring
  apply SmithSpecialRankTwo.weighted_matrix_shell_le hB d S R q hR hq
    hnorm hprimitive i j l hli hlj hnonzero hline F hF
    (fun _ A => auxiliaryWeight q law.size law.weight law.sets
      (A.map (Int.castRingHom (ZMod q))).col)
    N (4 * 2000 ^ 3) hN (by positivity) _ hcoord hproj
  intro x hx A hA
  obtain ⟨u, v, huv⟩ := hresidue x hx A hA
  calc
    auxiliaryWeight q law.size law.weight law.sets
        (A.map (Int.castRingHom (ZMod q))).col ≤
        4 * ((q : ℝ) ^ 3 / law.size) :=
      law.weight_le_four _ u v huv
    _ ≤ 4 * (2000 ^ 3 * (q : ℝ) * (((B ^ k : ℕ) : ℝ)) ^ 12) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = _ := by ring

end Problem355.AuxiliarySpecialRankTwo

end

end OAI
