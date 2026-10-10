import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalBase
import OAI.Probability.InvariantIsing.Cavity.CavityHaarRank

namespace OAI

/-! Full rank of the actual spectral compressions, with the eigenvalue
groups arranged in their given consecutive coordinate windows. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityColumns_gram {N n : ℕ} (U : Orthogonal (N + n)) :
    (cavityColumns U).transpose * cavityColumns U = 1 := by
  have hU := (Matrix.mem_orthogonalGroup_iff' (Fin (N + n)) ℝ).mp U.property
  ext i j
  have h := congrArg (fun M : Matrix (Fin (N + n)) (Fin (N + n)) ℝ =>
    M (Fin.natAdd N i) (Fin.natAdd N j)) hU
  change (∑ k : Fin (N + n), (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
    k (Fin.natAdd N i) * (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      k (Fin.natAdd N j)) = if i = j then 1 else 0
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.natAdd_inj] using h

lemma cavityColumns_eq_mul {N n : ℕ} (U : Orthogonal (N + n)) :
    cavityColumns U = (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *
      cavityColumns (1 : Orthogonal (N + n)) := by
  ext i j
  change (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j) =
    ∑ k : Fin (N + n), (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i k *
      (if k = Fin.natAdd N j then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma cavityCompressionGrams_eq_window {N n m : ℕ} (g : Fin (N + n) → Fin m)
    (a : Fin m) (l u : ℕ) (hlu : l ≤ u)
    (hg : ∀ i, g i = a ↔ l ≤ i.val ∧ i.val < u) (U : Orthogonal (N + n)) :
    cavityCompressionGrams g U a = cavityWindowGram (cavityColumns U) l u := by
  ext i j
  change (∑ k : Fin (N + n), (if g k = a then cavityColumns U k i else 0) *
    (if g k = a then cavityColumns U k j else 0)) = _
  rw [cavityWindowGram, Matrix.sub_apply, cavityPrefixGram_apply, cavityPrefixGram_apply,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [hg k]
  split_ifs <;> simp_all <;> omega

theorem cavityCompressionGrams_posDef_ae {N n m : ℕ}
    (g : Fin (N + n) → Fin m) (l u : Fin m → ℕ)
    (hg : ∀ a i, g i = a ↔ l a ≤ i.val ∧ i.val < u a)
    (hln : ∀ a, l a + n ≤ u a) (hu : ∀ a, u a ≤ N + n)
    (μ : Measure (Orthogonal (N + n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant] :
    ∀ᵐ U ∂μ, ∀ a, (cavityCompressionGrams g U a).PosDef := by
  apply ae_all_iff.mpr
  intro a
  have h := cavityHaarWindowGram_posDef (l a) (u a) (hln a) (hu a) μ
    (cavityColumns (1 : Orthogonal (N + n))) (cavityColumns_gram _)
  filter_upwards [h] with U hU
  rw [cavityCompressionGrams_eq_window g a (l a) (u a) (by have := hln a; omega) (hg a) U,
    cavityColumns_eq_mul]
  exact hU

end InvariantIsing

end

end OAI
