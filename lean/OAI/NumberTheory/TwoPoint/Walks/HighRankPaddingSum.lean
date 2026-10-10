import OAI.NumberTheory.TwoPoint.Walks.HighRankFixedPadding
import OAI.NumberTheory.TwoPoint.Bounds.PaddingCatalog

namespace OAI

/-! Sum actual squarefree padding after the full high-rank column estimate. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma weighted_pair_second_fiber_sum_le {I Q : Type*} [DecidableEq I] [DecidableEq Q]
    (F : Finset (I × Q)) (b : Q → ℝ) (c : I → ℝ) (K : ℝ)
    (hb : ∀ q, 0 ≤ b q)
    (hfiber : ∀ q ∈ F.image Prod.snd,
      (∑ i ∈ (F.filter (fun a => a.2 = q)).image Prod.fst, c i) ≤ K) :
    (∑ a ∈ F, c a.1 * b a.2) ≤ K * ∑ q ∈ F.image Prod.snd, b q := by
  rw [← sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem Prod.snd ha)
    (fun a : I × Q => c a.1 * b a.2), mul_sum]
  apply sum_le_sum
  intro q hq
  let S := F.filter (fun a => a.2 = q)
  have hinj : Set.InjOn (Prod.fst : I × Q → I) S := by
    intro a ha d hd he
    exact Prod.ext he ((mem_filter.mp ha).2.trans (mem_filter.mp hd).2.symm)
  calc
    _ = (∑ i ∈ S.image Prod.fst, c i) * b q := by
      rw [sum_mul, sum_image hinj]
      apply sum_congr rfl
      intro a ha
      rw [(mem_filter.mp ha).2]
    _ ≤ K * b q := mul_le_mul_of_nonneg_right (hfiber q hq) (hb q)

/-- A complete reciprocal sum over numerical columns and numerical
padding values. All pattern and padding catalogs are supplied by proved
encodings, and the lit conditions are those of the original words. -/
theorem high_rank_column_padding_sum {J R : ℕ} (P : Fin J → Finset ℕ) (Qp : Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
    (hR : 0 < R) (forward : Fin R → Bool) (j : Fin J)
    (h Q D B H r M : ℕ) (U : ℝ) (hU : 1 ≤ U)
    (hP : ∀ p ∈ P j, p.Prime) (hV : 0 < primeHarmonicMass (P j))
    (hmass : ∀ l, primeHarmonicMass (P l) ≤ U) (hQmass : primeHarmonicMass Qp ≤ U)
    (hH : 0 < H) (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ a ∈ F, ∀ i, a.2 i ≤ Q)
    (hd : ∀ a ∈ F, ∀ i, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D)
    (hsq : ∀ a ∈ F, ∀ i, Squarefree (a.2 i))
    (hpool : ∀ a ∈ F, ∀ i, (a.2 i).primeFactors ⊆ Qp)
    (hcount : ∀ a ∈ F, ∀ i, (a.2 i).primeFactors.card ≤ M)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (hrank : ∀ a ∈ F,
      ¬ColumnLowRank (tupleColumnPattern a.1 hR forward a.2 j) hR h perfect cut r)
    (base : ColumnPrimeAssignment J R P → (Fin R → ℕ) → ℤ)
    (hlit : ∀ a ∈ F, ∀ i ∈ perfect, ((a.1 j i).val : ℤ) ∣ base a.1 a.2 +
      wordDisplacement h ((columnTupleWord a.1 forward a.2).take i.val)) :
    (∑ a ∈ F, columnReciprocalWeight a.1 *
      ∏ p ∈ paddingPrimeSupport a.2, (p : ℝ)⁻¹) ≤
      ((Fintype.card (CrudeColumnPatternCode J R) : ℝ) * U ^ (R * J) *
        Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
          (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r)) *
      ((∑ n : Fin (R * M + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) * U ^ (R * M)) := by
  let K := (Fintype.card (CrudeColumnPatternCode J R) : ℝ) * U ^ (R * J) *
    Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
      (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfiber (q : Fin R → ℕ) (hqF : q ∈ F.image Prod.snd) :
      (∑ w ∈ (F.filter (fun a => a.2 = q)).image Prod.fst, columnReciprocalWeight w) ≤ K := by
    let G := (F.filter (fun a => a.2 = q)).image Prod.fst
    have hmem (w : ColumnPrimeAssignment J R P) (hw : w ∈ G) : (w, q) ∈ F := by
      obtain ⟨a, ha, haw⟩ := mem_image.mp hw
      have he : a = (w, q) := Prod.ext haw (mem_filter.mp ha).2
      exact he ▸ (mem_filter.mp ha).1
    obtain ⟨a, ha, haq⟩ := mem_image.mp hqF
    have hq' : ∀ i, q i ≤ Q := by simpa only [haq] using hq a ha
    exact high_rank_fixed_padding_sum P G hR forward q j h Q D B H r U hU
      hP hV hmass hH hlo hbound hq'
      (fun w hw => hd (w, q) (hmem w hw)) perfect cut
      (fun w hw => hrank (w, q) (hmem w hw)) (fun w => base w q)
      (fun w hw => hlit (w, q) (hmem w hw))
  have hpad := padding_catalog_reciprocal_sum R M Qp (F.image Prod.snd) U hU hQmass
    (by intro q hqF; obtain ⟨a, ha, rfl⟩ := mem_image.mp hqF; exact hsq a ha)
    (by intro q hqF; obtain ⟨a, ha, rfl⟩ := mem_image.mp hqF; exact hpool a ha)
    (by intro q hqF; obtain ⟨a, ha, rfl⟩ := mem_image.mp hqF; exact hcount a ha)
  have hb := weighted_pair_second_fiber_sum_le F
    (fun q => ∏ p ∈ paddingPrimeSupport q, (p : ℝ)⁻¹)
    columnReciprocalWeight K (fun _ => by positivity) hfiber
  exact hb.trans (mul_le_mul_of_nonneg_left hpad hK)

end TwoPointCorrelations

end OAI
