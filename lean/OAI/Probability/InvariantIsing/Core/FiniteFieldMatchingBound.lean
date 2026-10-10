import OAI.Probability.InvariantIsing.Core.FiniteFieldMatching

namespace OAI

/-! The unmatched field sites are controlled by differences of label counts. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma fieldLabelCount_sum {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (g : Fin N → A) : ∑ a, spinGroupSize g a=N := by
  simpa only [Fintype.card_sigma, Fintype.card_subtype, spinGroupSize, Fintype.card_fin] using
    Fintype.card_congr (Equiv.sigmaFiberEquiv g)

theorem exists_field_permutation_l1_bound {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (g h : Fin N → A) (b : A → ℝ) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ a, |b a| ≤ B) :
    ∃ p : Equiv.Perm (Fin N),
      (∑ i, |b (g i)-b (h (p i))|) ≤
        2*B*∑ a, |(spinGroupSize g a : ℝ)-spinGroupSize h a| := by
  obtain ⟨p,hp⟩ := exists_field_label_matching g h
  let S := Finset.univ.filter (fun i => g i=h (p i))
  let T := Finset.univ \ S
  have hsmall : ∑ a, min (spinGroupSize g a) (spinGroupSize h a) ≤ N :=
    (Finset.sum_le_sum (fun a _ => min_le_left _ _)).trans_eq (fieldLabelCount_sum g)
  have hmiss : ((N-∑ a, min (spinGroupSize g a) (spinGroupSize h a) : ℕ) : ℝ) ≤
      ∑ a, |(spinGroupSize g a : ℝ)-spinGroupSize h a| := by
    rw [Nat.cast_sub hsmall]
    have hn : (N : ℝ)=∑ a, (spinGroupSize g a : ℝ) := by
      exact_mod_cast (fieldLabelCount_sum g).symm
    rw [hn, Nat.cast_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : spinGroupSize g a ≤ spinGroupSize h a
    · rw [min_eq_left ha, sub_self]
      exact abs_nonneg _
    · rw [min_eq_right (by omega)]
      exact le_abs_self _
  have hT : T.card ≤ N-∑ a, min (spinGroupSize g a) (spinGroupSize h a) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simpa only [Finset.card_univ, Fintype.card_fin] using Nat.sub_le_sub_left hp N
  have hsum : (∑ i, |b (g i)-b (h (p i))|) ≤ (T.card : ℝ)*(2*B) := by
    have he : (∑ i, |b (g i)-b (h (p i))|)=∑ i ∈ T, |b (g i)-b (h (p i))| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ T)
      intro i _ hi
      have hg : g i=h (p i) := by
        by_contra hn
        exact hi (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hn⟩)
      rw [hg,sub_self,abs_zero]
    rw [he]
    calc
      _ ≤ ∑ _i ∈ T, 2*B := Finset.sum_le_sum fun i _ =>
        (abs_sub _ _).trans (by linarith [hb (g i),hb (h (p i))])
      _ = _ := by simp
  refine ⟨p, hsum.trans ?_⟩
  calc
    (T.card : ℝ)*(2*B) ≤ ((N-∑ a, min (spinGroupSize g a) (spinGroupSize h a) : ℕ) : ℝ)*(2*B) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hT) (by positivity)
    _ ≤ (∑ a, |(spinGroupSize g a : ℝ)-spinGroupSize h a|)*(2*B) :=
      mul_le_mul_of_nonneg_right hmiss (by positivity)
    _ = _ := mul_comm _ _

end InvariantIsing

end

end OAI
