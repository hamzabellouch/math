import OAI.Combinatorics.BinaryEdit.CodeAdditive
import OAI.Combinatorics.BinaryEdit.UnequalSegments
import OAI.Combinatorics.BinaryEdit.EncodingIndex

namespace OAI

namespace TreeEdit.BinaryLower.Code

universe u v

/-- Simultaneous separation of the actual codeword segments implies the
concrete within-block separation predicate used by unequal matching counts.
Optional lookup makes the bad-pair predicate total on natural block indices;
the predicate is only used at the explicitly valid indices in this theorem. -/
theorem encoded_block_segment_separation {α : Type u} {β : Type v}
    {M P a₀ : ℕ} (c : α → Word β P)
    (hsep : ∀ k l : α, k ≠ l → ∀ a i j : ℕ, a₀ ≤ a →
      i + a ≤ P → j + a ≤ P →
      100 * lcs (((c k).val.drop i).take a) (((c l).val.drop j).take a) ≤ 99 * a)
    (x y : List α) (hx : x.length = M) (hy : y.length = M) :
    BlockSegmentSeparation (encodedBit c x hx) (encodedBit c y hy)
      (fun b => x[b.1]? ≠ y[b.2]?) a₀ := by
  intro b hb hb₁ hb₂ i j a hi hi' hj hj' ha w hwx hwy
  have hb₁' : b.1 < x.length := by simpa only [hx] using hb₁
  have hb₂' : b.2 < y.length := by simpa only [hy] using hb₂
  have hletters : x[b.1] ≠ y[b.2] := by
    simpa only [List.getElem?_eq_getElem hb₁', List.getElem?_eq_getElem hb₂',
      ne_eq, Option.some.injEq] using hb
  have hioff : i - b.1 * P + a ≤ P := by
    simp only [Nat.add_mul, Nat.one_mul] at hi'
    omega
  have hjoff : j - b.2 * P + a ≤ P := by
    simp only [Nat.add_mul, Nat.one_mul] at hj'
    omega
  have heqx : ((encode c x).drop i).take a =
      (((c x[b.1]).val).drop (i - b.1 * P)).take a := by
    have h := encode_segment_eq c x b.1 (i - b.1 * P) a hb₁' hioff
    simpa only [Nat.add_sub_of_le hi] using h
  have heqy : ((encode c y).drop j).take a =
      (((c y[b.2]).val).drop (j - b.2 * P)).take a := by
    have h := encode_segment_eq c y b.2 (j - b.2 * P) a hb₂' hjoff
    simpa only [Nat.add_sub_of_le hj] using h
  rw [ofFn_encodedBit, heqx] at hwx
  rw [ofFn_encodedBit, heqy] at hwy
  exact (Nat.mul_le_mul_left 100 (length_le_lcs hwx hwy)).trans
    (hsep x[b.1] y[b.2] hletters a (i - b.1 * P) (j - b.2 * P) ha hioff hjoff)

/-- The actual codebook's segment property gives the full additive deficit
bound, with no remaining local charge or matching-count hypothesis. -/
theorem additive_of_codeword_separation {α : Type u} {β : Type v}
    {M P a₀ : ℕ} (hP : 0 < P) (c : α → Word β P)
    (hsep : ∀ k l : α, k ≠ l → ∀ a i j : ℕ, a₀ ≤ a →
      i + a ≤ P → j + a ≤ P →
      100 * lcs (((c k).val.drop i).take a) (((c l).val.drop j).take a) ≤ 99 * a)
    (x y : List α) (hx : x.length = M) (hy : y.length = M) :
    P * deficit M x y ≤
      201 * deficit (M * P) (encode c x) (encode c y) + 2 * M * a₀ := by
  classical
  apply additive_of_unequal_matching_bound c x y hx hy hP
  intro r f g hf hg hmatch
  rw [unequalEdges_eq_filter_getElem?]
  exact unequal_matches_le_of_segment_separation hP
    (encodedBit c x hx) (encodedBit c y hy) f g hf hg hmatch
    (fun b => x[b.1]? ≠ y[b.2]?) a₀
    (encoded_block_segment_separation c hsep x y hx hy)

end TreeEdit.BinaryLower.Code

end OAI
