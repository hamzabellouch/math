import OAI.NumberTheory.TwoPoint.Bounds.GoodColumnSum
import OAI.NumberTheory.TwoPoint.Bounds.PaddingWordSum

namespace OAI

/-! Sum padding only after fixing each complete column pattern. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma weighted_pair_sum_le {I Q : Type*} [DecidableEq I] [Fintype Q]
    (F : Finset (I × Q)) (b : I → ℝ) (weight : I → Q → ℝ) (K : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hw : ∀ i q, 0 ≤ weight i q)
    (hK : ∀ i, (∑ q, weight i q) ≤ K) :
    (∑ a ∈ F, b a.1 * weight a.1 a.2) ≤ K * ∑ i ∈ F.image Prod.fst, b i := by
  rw [← sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem Prod.fst ha)
    (fun a : I × Q => b a.1 * weight a.1 a.2), mul_sum]
  apply sum_le_sum
  intro i _
  let S := F.filter (fun a => a.1 = i)
  have hinj : Set.InjOn (Prod.snd : I × Q → Q) S := by
    intro a ha c hc he
    exact Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hc).2.symm) he
  calc
    _ = ∑ q ∈ S.image Prod.snd, b i * weight i q := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro a ha
      rw [(mem_filter.mp ha).2]
    _ ≤ ∑ q : Q, b i * weight i q := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro q _ _
      exact mul_nonneg (hb i) (hw i q)
    _ = b i * ∑ q, weight i q := (mul_sum _ _ _).symm
    _ ≤ b i * K := mul_le_mul_of_nonneg_left (hK i) (hb i)
    _ = K * b i := mul_comm _ _

/-- The code may depend on the padding word. After fixing a code, sum
all padding choices for each prime assignment and use the uniform bound.
This avoids exchanging a prime-dependent cutoff with a supremum. -/
theorem covered_column_padding_sum {J R M : ℕ} {Q Code : Type*}
    [Fintype Q] [Fintype Code]
    (P : Fin J → Finset ℕ) (F : Finset (ColumnPrimeAssignment J R P × Q))
    (decode : Code → Fin J → Fin R → Fin R → Bool)
    (weight : ColumnPrimeAssignment J R P → Q → ℝ) (A K : ℝ)
    (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hw : ∀ w q, 0 ≤ weight w q) (hpad : ∀ w, (∑ q, weight w q) ≤ K)
    (hlabels : ∀ a ∈ F, (∑ j, (univ.image (a.1 j)).card) ≤ M)
    (hcover : ∀ a ∈ F, ∃ c, ∀ j i l, decode c j i l = decide (a.1 j i = a.1 j l)) :
    (∑ a ∈ F, columnReciprocalWeight a.1 * weight a.1 a.2) ≤
      (Fintype.card Code : ℝ) * K * A ^ M := by
  let fiber (c : Code) := F.filter (fun a =>
    ∀ j i l, decode c j i l = decide (a.1 j i = a.1 j l))
  have hsum : (∑ a ∈ F, columnReciprocalWeight a.1 * weight a.1 a.2) ≤
      ∑ c, ∑ a ∈ fiber c, columnReciprocalWeight a.1 * weight a.1 a.2 := by
    calc
      _ ≤ ∑ a ∈ F, ∑ c, if ∀ j i l, decode c j i l = decide (a.1 j i = a.1 j l)
          then columnReciprocalWeight a.1 * weight a.1 a.2 else 0 := by
        apply sum_le_sum
        intro a ha
        obtain ⟨c, hc⟩ := hcover a ha
        have hs := single_le_sum (s := (univ : Finset Code))
          (f := fun d => if ∀ j i l, decode d j i l = decide (a.1 j i = a.1 j l)
            then columnReciprocalWeight a.1 * weight a.1 a.2 else 0)
          (fun d _ => ite_nonneg (mul_nonneg (columnReciprocalWeight_nonneg _) (hw _ _)) le_rfl)
          (mem_univ c)
        simpa only [ite_eq_left hc] using hs
      _ = _ := by rw [sum_comm]; simp only [fiber, sum_filter]
  have hfiber (c : Code) :
      (∑ a ∈ fiber c, columnReciprocalWeight a.1 * weight a.1 a.2) ≤ K * A ^ M := by
    apply (weighted_pair_sum_le (fiber c) columnReciprocalWeight weight K
      columnReciprocalWeight_nonneg hw hpad).trans
    apply mul_le_mul_of_nonneg_left _ hK
    have hm : ∀ w ∈ (fiber c).image Prod.fst, (∑ j, (univ.image (w j)).card) ≤ M := by
      intro w hw
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hw
      exact hlabels a (mem_filter.mp ha).1
    have hc : ∀ w ∈ (fiber c).image Prod.fst, ∃ _d : Unit,
        ∀ j i l, decode c j i l = decide (w j i = w j l) := by
      intro w hw
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hw
      exact ⟨(), (mem_filter.mp ha).2⟩
    simpa only [Fintype.card_unit, Nat.cast_one, one_mul] using
      covered_column_patterns_reciprocal_sum P ((fiber c).image Prod.fst)
        (fun (_ : Unit) => decode c) A M hA hmass hm hc
  exact hsum.trans (by
    calc
      _ ≤ ∑ _c : Code, K * A ^ M := sum_le_sum (fun c _ => hfiber c)
      _ = _ := by simp [mul_assoc])

/-- The good-word column count, with padding summed uniformly before the
remaining prime assignments. All actual admissibility restrictions can
remain in the finite set `F`. -/
theorem covered_good_column_padding_sum {J k S : ℕ} {Q Code : Type*}
    [Fintype Q] [Fintype Code]
    (P : Fin J → Finset ℕ) (F : Finset (ColumnPrimeAssignment J (2 * k) P × Q))
    (decode : Code → Fin J → Fin (2 * k) → Fin (2 * k) → Bool)
    (weight : ColumnPrimeAssignment J (2 * k) P → Q → ℝ) (A K : ℝ)
    (hA : 1 ≤ A) (hK : 0 ≤ K) (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hw : ∀ w q, 0 ≤ weight w q) (hpad : ∀ w, (∑ q, weight w q) ≤ K)
    (hsingle : ∀ a ∈ F, columnSingletonCount a.1 ≤ 2 * S)
    (hcover : ∀ a ∈ F, ∃ c, ∀ j i l, decode c j i l = decide (a.1 j i = a.1 j l)) :
    (∑ a ∈ F, columnReciprocalWeight a.1 * weight a.1 a.2) ≤
      (Fintype.card Code : ℝ) * K * A ^ (J * k + S) :=
  covered_column_padding_sum P F decode weight A K hA hK hmass hw hpad
    (fun a ha => good_column_observed_count a.1 (hsingle a ha)) hcover

end TwoPointCorrelations

end OAI
