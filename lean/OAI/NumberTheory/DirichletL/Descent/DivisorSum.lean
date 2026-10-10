import OAI.NumberTheory.DirichletL.Descent.DivisorExtraction

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def hybridDivisorPool (rows : Finset (Ideal Eis)) : Finset (Ideal Eis) :=
  rows.biUnion idealDivisors

def hybridDivisorPairPool (rows : Finset (Ideal Eis)) : Finset (Ideal Eis × Ideal Eis) :=
  rows.biUnion fun k => (idealDivisors k) ×ˢ (idealDivisors k)

theorem hybridDivisorPool_bounds (rows : Finset (Ideal Eis)) (K : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K)
    (D : Ideal Eis) (hD : D ∈ hybridDivisorPool rows) :
    D ≠ 0 ∧ (Ideal.absNorm D : ℝ) ≤ K := by
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  have hdiv := (mem_idealDivisors (hrows k hk).1).mp hDk
  exact ⟨ne_zero_of_dvd_ne_zero (hrows k hk).1 hdiv,
    (QuadraticMainBoundary.norm_le_of_dvd (hrows k hk).1 hdiv).trans (hrows k hk).2⟩

theorem hybridDivisorPairPool_subset (rows : Finset (Ideal Eis)) :
    hybridDivisorPairPool rows ⊆ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows) := by
  intro D hD
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  exact Finset.mem_product.mpr
    ⟨Finset.mem_biUnion.mpr ⟨k, hk, (Finset.mem_product.mp hDk).1⟩,
      Finset.mem_biUnion.mpr ⟨k, hk, (Finset.mem_product.mp hDk).2⟩⟩

theorem hybrid_divisor_pair_inverse_norm_sum
    (rows : Finset (Ideal Eis)) (K : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) :
    (∑ D ∈ hybridDivisorPairPool rows,
      1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ))) ≤
      (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2 := by
  have hb := hybridDivisorPool_bounds rows K hrows
  have hsum := finite_inverse_norm_sum (hybridDivisorPool rows) K
    (fun D hD => (hb D hD).1) (fun D hD => (hb D hD).2)
  calc
    _ ≤ ∑ D ∈ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows),
        1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (hybridDivisorPairPool_subset rows)
      intro D hD hn
      positivity
    _ = (∑ D ∈ hybridDivisorPool rows, 1 / (Ideal.absNorm D : ℝ)) ^ 2 := by
      rw [Finset.sum_product, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro R hR
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hsum 2

end
end SevenEighths.InverseMoment

end OAI
