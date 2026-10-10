import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.SimplexLaw
import OAI.Combinatorics.IndependentSets.Geometry.RationalSimplexApproximation
import OAI.Combinatorics.IndependentSets.Reduction.Small

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

theorem rational_pattern_alignment (s d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ r ≥ s, ∃ p : (Fin s ↪o Fin r) → ℚ, ((∀ coordinate, 0 ≤ p coordinate) ∧
      ∑ coordinate, p coordinate = 1) ∧
      ∀ C : ListPattern s d (Fin r),
        ∑ e, (p e : ℝ) * (if ¬GoodPatternOn (C.restrict e) Finset.univ then 1 else 0) ≤ η := by
  obtain ⟨r, hr, q, hq, hqbound⟩ := real_pattern_alignment s d (η / 2) (half_pos hη)
  have : Nonempty (Fin s ↪o Fin r) := ⟨Fin.castLEOrderEmb hr⟩
  obtain ⟨p, hp, happ⟩ := rational_simplex_approximation q hq (η / 2) (half_pos hη)
  refine ⟨r, hr, p, hp, ?_⟩
  intro C
  have ha := happ (fun e => if ¬GoodPatternOn (C.restrict e) Finset.univ then 1 else 0)
    (fun e => by split_ifs <;> norm_num)
  have hb := hqbound C
  linarith

noncomputable def embeddingLayerLaw {r s : ℕ}
    (p : (Fin s ↪o Fin r) → ℚ)
    (hp : (∀ coordinate, 0 ≤ p coordinate) ∧ ∑ coordinate, p coordinate = 1) : LayerLaw r s where
  weight B := ∑ e, if B = Finset.univ.map e.toEmbedding then p e else 0
  nonneg B := Finset.sum_nonneg (fun e _ => by split_ifs; exact hp.1 e; rfl)
  total := by
    rw [Finset.sum_comm]
    simpa using hp.2
  support B hB := by
    apply Finset.sum_eq_zero
    intro e _
    apply ite_eq_right
    intro h
    apply hB
    rw [h]
    simp

lemma embeddingLayerLaw_badMass {r s : ℕ} {M : Type}
    (p : (Fin s ↪o Fin r) → ℚ)
    (hp : (∀ coordinate, 0 ≤ p coordinate) ∧ ∑ coordinate, p coordinate = 1)
    (A : Finset (Fin r) → Finset M) :
    (embeddingLayerLaw p hp).badMass A =
      ∑ e, if Aligned A (Finset.univ.map e.toEmbedding) then 0 else p e := by
  classical
  unfold LayerLaw.badMass
  change (∑ B, if Aligned A B then 0 else
    ∑ e, if B = Finset.univ.map e.toEmbedding then p e else 0) = _
  have h (B : Finset (Fin r)) :
      (if Aligned A B then 0 else ∑ e, if B = Finset.univ.map e.toEmbedding then p e else 0) =
      ∑ e, if B = Finset.univ.map e.toEmbedding then
        (if Aligned A (Finset.univ.map e.toEmbedding) then 0 else p e) else 0 := by
    by_cases ha : Aligned A B
    · rw [ite_eq_left ha]
      symm
      apply Finset.sum_eq_zero
      intro e _
      by_cases he : B = Finset.univ.map e.toEmbedding
      · simp [← he, ha]
      · simp [he]
    · rw [ite_eq_right ha]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : B = Finset.univ.map e.toEmbedding
      · simp [← he, ha]
      · simp [he]
  simp_rw [h]
  rw [Finset.sum_comm]
  simp

theorem distributional_alignment : DistributionalAlignment := by
  classical
  intro s d hs hd η hη
  obtain ⟨r, hr, p, hp, hbound⟩ := rational_pattern_alignment s d η hη
  refine ⟨r, hr, embeddingLayerLaw p hp, ?_⟩
  intro M _ A hcard hsep
  rw [embeddingLayerLaw_badMass, Rat.cast_sum]
  apply le_trans ?_ (hbound (actualPattern (d := d) A hsep))
  apply Finset.sum_le_sum
  intro e _
  have hnonneg : (0 : ℝ) ≤ p e := by exact_mod_cast hp.1 e
  by_cases hg : GoodPatternOn ((actualPattern (d := d) A hsep).restrict e) Finset.univ
  · have hBcard : (Finset.univ.map e.toEmbedding).card = s := by simp
    have hB : (Finset.univ.map e.toEmbedding).Nonempty :=
      Finset.card_pos.mp (by omega)
    have ha : Aligned A (Finset.univ.map e.toEmbedding) :=
      actualPattern_good_aligned A hcard hsep _ hB hBcard.le
        (good_embedding_restrict_goodOn _ e hg)
    simp [ha, hg]
  · simp only [hg, not_false_eq_true, ite_true, mul_one]
    split_ifs <;> simp_all

end LargeIndependentSets

end OAI
