import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MergeOrdering

namespace OAI

/-!
# A bounded tie-group buffer

The tail-recursive collector stores at most the requested number of matching
occurrences and leaves the first different-key occurrence unconsumed. Its
instrumented query counter counts every reader call, including the final
lookahead. No clearing of unused buffer positions is performed.
-/

namespace LowSpaceSubsetSum
namespace TieBuffer

universe u v

variable {α : Type u} {σ : Type v}

def groupView (key : α → ℤ) (K : ℤ) (view : σ → List α) (s : σ) : List α :=
  (view s).takeWhile (fun a => decide (key a = K))

structure Result (α : Type u) (σ : Type v) where
  buffer : Array α
  cursor : σ
  queries : ℕ

def fillAcc (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ) :
    ℕ → σ → Array α → ℕ → Result α σ
  | 0, s, buf, q => ⟨buf, s, q⟩
  | k + 1, s, buf, q => match read s with
    | none => ⟨buf, s, q + 1⟩
    | some (a, s') => if key a = K then fillAcc read key K k s' (buf.push a) (q + 1)
      else ⟨buf, s, q + 1⟩

def fill (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ) (B : ℕ) (s : σ) :
    Result α σ := fillAcc read key K B s #[] 0

theorem fillAcc_spec (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (fuel : ℕ) (s : σ) (buf : Array α) (q : ℕ) :
    (fillAcc read key K fuel s buf q).buffer.toList =
        buf.toList ++ (groupView key K view s).take fuel ∧
    view s = (groupView key K view s).take fuel ++
        view (fillAcc read key K fuel s buf q).cursor ∧
    groupView key K view (fillAcc read key K fuel s buf q).cursor =
        (groupView key K view s).drop fuel ∧
    (fillAcc read key K fuel s buf q).queries ≤ q + fuel := by
  induction fuel generalizing s buf q with
  | zero => simp [fillAcc]
  | succ fuel ih =>
    have hr := hread s
    cases h : read s with
    | none =>
      simp only [h] at hr
      simp [fillAcc, h, groupView, hr]
    | some z =>
      rcases z with ⟨a, s'⟩
      simp only [h] at hr
      by_cases ha : key a = K
      · have hg : groupView key K view s = a :: groupView key K view s' := by
          simp [groupView, hr, ha]
        have hi := ih s' (buf.push a) (q + 1)
        simp only [fillAcc, h, ite_eq_left ha]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hi.1, hg]
          simp [List.append_assoc]
        · rw [hr, hi.2.1, hg]
          simp
        · rw [hi.2.2.1, hg]
          simp
        · have := hi.2.2.2
          omega
      · have hg : groupView key K view s = [] := by simp [groupView, hr, ha]
        simp [fillAcc, h, ha, hg]

theorem fill_buffer (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (view : σ → List α) (hread : RowMerge.IsReader read view) (B : ℕ) (s : σ) :
    (fill read key K B s).buffer.toList = (groupView key K view s).take B := by
  simpa [fill] using (fillAcc_spec read key K view hread B s #[] 0).1

theorem fill_size_le (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (view : σ → List α) (hread : RowMerge.IsReader read view) (B : ℕ) (s : σ) :
    (fill read key K B s).buffer.size ≤ B := by
  have h := congrArg List.length (fill_buffer read key K view hread B s)
  simp only [Array.length_toList, List.length_take] at h
  omega

theorem fill_suffix (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (view : σ → List α) (hread : RowMerge.IsReader read view) (B : ℕ) (s : σ) :
    groupView key K view (fill read key K B s).cursor =
      (groupView key K view s).drop B :=
  (fillAcc_spec read key K view hread B s #[] 0).2.2.1

theorem fill_queries_le (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (view : σ → List α) (hread : RowMerge.IsReader read view) (B : ℕ) (s : σ) :
    (fill read key K B s).queries ≤ B := by
  simpa [fill] using (fillAcc_spec read key K view hread B s #[] 0).2.2.2

/-- The collector reads each stored occurrence once and performs at most
one additional lookahead, irrespective of the chosen buffer capacity. -/
theorem fillAcc_queries_le_potential (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (fuel : ℕ) (s : σ) (buf : Array α) (q : ℕ) :
    (fillAcc read key K fuel s buf q).queries ≤
      q + min fuel ((groupView key K view s).length + 1) := by
  induction fuel generalizing s buf q with
  | zero => simp [fillAcc]
  | succ fuel ih =>
    have hr := hread s
    cases h : read s with
    | none =>
      simp only [h] at hr
      simp [fillAcc, h, groupView, hr]
    | some z =>
      rcases z with ⟨x, s'⟩
      simp only [h] at hr
      by_cases hx : key x = K
      · have hg : groupView key K view s = x :: groupView key K view s' := by
          simp [groupView, hr, hx]
        have hi := ih s' (buf.push x) (q + 1)
        simp only [fillAcc, h, ite_eq_left hx, hg, List.length_cons]
        omega
      · have hg : groupView key K view s = [] := by simp [groupView, hr, hx]
        simp [fillAcc, h, hx, hg]

theorem fill_queries_le_potential (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (view : σ → List α) (hread : RowMerge.IsReader read view) (B : ℕ) (s : σ) :
    (fill read key K B s).queries ≤ (groupView key K view s).length + 1 := by
  have h := fillAcc_queries_le_potential read key K view hread B s #[] 0
  simp only [fill, zero_add] at h ⊢
  exact h.trans (Nat.min_le_right _ _)

def hasKey (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ) (s : σ) : Bool :=
  match read s with
  | none => false
  | some (a, _) => decide (key a = K)

theorem hasKey_iff (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (view : σ → List α) (hread : RowMerge.IsReader read view) (s : σ) :
    hasKey read key K s = true ↔ groupView key K view s ≠ [] := by
  have hr := hread s
  cases h : read s with
  | none =>
    simp only [h] at hr
    simp [hasKey, h, groupView, hr]
  | some z =>
    rcases z with ⟨a, s'⟩
    simp only [h] at hr
    by_cases ha : key a = K <;> simp [hasKey, h, groupView, hr, ha]

/-- A snapshot is needed only if more than `B` second-row occurrences have
this key. In particular the buffer is full when a snapshot is taken. -/
theorem long_group_full_buffer (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (view : σ → List α) (hread : RowMerge.IsReader read view) (B : ℕ) (s : σ)
    (hlong : hasKey read key K (fill read key K B s).cursor = true) :
    B < (groupView key K view s).length ∧ (fill read key K B s).buffer.size = B := by
  have hn := (hasKey_iff read key K view hread _).mp hlong
  rw [fill_suffix read key K view hread B s] at hn
  have hB : B < (groupView key K view s).length := by
    by_contra h
    apply hn
    exact List.drop_eq_nil_of_le (by omega)
  refine ⟨hB, ?_⟩
  have h := congrArg List.length (fill_buffer read key K view hread B s)
  simpa only [Array.length_toList, List.length_take, Nat.min_eq_left hB.le] using h

end TieBuffer
end LowSpaceSubsetSum

end OAI
