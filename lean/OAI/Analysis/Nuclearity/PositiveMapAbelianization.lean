import OAI.Analysis.PureInfiniteness.AbelianRangeExtension

namespace OAI

/-! Finite relative abelianization of a positive map. This form permits the
local orthogonal corner sums used in KR02's coefficient cone: only the chosen
commuting positive values must be fixed. -/

noncomputable section

namespace WeakPureInfiniteness

variable {A B I : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  [Fintype I]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem finite_positive_map_abelianization (hP : MainGap.PropertyP A)
    (φ : B →L[ℂ] N) (hφ : ∀ b, 0 ≤ b → 0 ≤ φ b)
    (a : I → N) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i j, Commute (a i) (a j)) :
    ∃ z : N, ‖z‖ ≤ 1 ∧ (∀ i, star z * a i * z = a i) ∧
      ∀ b c, Commute (star z * φ b * z) (star z * φ c * z) := by
  classical
  let : Encodable I := Fintype.toEncodable I
  let a' (n : ℕ) := match Encodable.decode (α := I) n with
    | none => (0 : N)
    | some i => a i
  have ha' (n : ℕ) : 0 ≤ a' n := by
    cases h : Encodable.decode (α := I) n with
    | none => simp only [a', h, le_refl]
    | some i => simpa only [a', h] using ha i
  have hc' (n m : ℕ) : Commute (a' n) (a' m) := by
    cases hn : Encodable.decode (α := I) n with
    | none => simp only [a', hn]; exact Commute.zero_left _
    | some i =>
      cases hm : Encodable.decode (α := I) m with
      | none => simp only [a', hm]; exact Commute.zero_right _
      | some j => simpa only [a', hn, hm] using hc i j
  obtain ⟨q, hq⟩ := exists_dense_positive_sequence (D := B)
  obtain ⟨z, hz, hfix, _, hpair⟩ := ultrapower_countable_positive_abelianization U hP
    a' (fun n => φ (q n)) ha' (fun n => hφ _ (q n).property) hc'
  let R : B →L[ℂ] N := (ContinuousLinearMap.mulLeftRight ℂ N (star z) z).comp φ
  refine ⟨z, hz, ?_, ?_⟩
  · intro i
    simpa only [a', Encodable.encodek] using hfix (Encodable.encode i)
  · exact abelian_range_of_positive_sequence q hq R hpair

end WeakPureInfiniteness

end

end OAI
