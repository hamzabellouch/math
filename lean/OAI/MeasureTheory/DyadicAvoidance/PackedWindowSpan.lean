import OAI.MeasureTheory.DyadicAvoidance.WindowRecursion

namespace OAI

namespace Problem310.WindowRecursion

/-- Length of a list of windows packed with a fixed gap between consecutive
windows, with no leading or trailing gap. -/
def packedSpan (g : ℕ) (L : List ℕ) : ℕ := L.sum + (L.length - 1) * g

@[simp] theorem packedSpan_nil (g : ℕ) : packedSpan g [] = 0 := by
  simp [packedSpan]

@[simp] theorem packedSpan_singleton (g r : ℕ) : packedSpan g [r] = r := by
  simp [packedSpan]

theorem packedSpan_append (g : ℕ) (L K : List ℕ) (hL : L ≠ []) (hK : K ≠ []) :
    packedSpan g (L ++ K) = packedSpan g L + g + packedSpan g K := by
  have hLl : 1 ≤ L.length := List.length_pos_iff.mpr hL
  have hKl : 1 ≤ K.length := List.length_pos_iff.mpr hK
  have hlen : L.length + K.length - 1 = (L.length - 1) + 1 + (K.length - 1) := by
    omega
  simp only [packedSpan, List.sum_append, List.length_append, hlen, Nat.add_mul, one_mul]
  omega

theorem packedSpan_cons (g r : ℕ) (L : List ℕ) (hL : L ≠ []) :
    packedSpan g (r :: L) = r + g + packedSpan g L := by
  simpa using packedSpan_append g [r] L (by simp) hL

theorem packedSpan_flatten_replicate (M g : ℕ) (L : List ℕ)
    (hM : 1 ≤ M) (hL : L ≠ []) :
    packedSpan g ((List.replicate M L).flatten) = M * packedSpan g L + (M - 1) * g := by
  have hLl : 1 ≤ L.length := List.length_pos_iff.mpr hL
  have hlen : M * L.length - 1 = M * (L.length - 1) + (M - 1) := by
    have he : M * L.length = M * (L.length - 1) + M := by
      calc
        M * L.length = M * ((L.length - 1) + 1) := by rw [Nat.sub_add_cancel hLl]
        _ = M * (L.length - 1) + M := by ring
    omega
  simp only [packedSpan, List.sum_flatten, List.map_replicate, List.sum_replicate,
    List.length_flatten, nsmul_eq_mul, Nat.cast_id]
  rw [hlen]
  ring

/-- The deterministic list of incoming-window lengths in full preorder. -/
def preorderLengths (M g r₀ : ℕ) : ℕ → List ℕ
  | 0 => []
  | h + 1 => (List.replicate M (length M g r₀ (h + 1) :: preorderLengths M g r₀ h)).flatten

@[simp] theorem preorderLengths_zero (M g r₀ : ℕ) : preorderLengths M g r₀ 0 = [] := rfl

theorem preorderLengths_succ (M g r₀ h : ℕ) :
    preorderLengths M g r₀ (h + 1) =
      (List.replicate M (length M g r₀ (h + 1) :: preorderLengths M g r₀ h)).flatten := rfl

theorem preorderLengths_succ_ne_nil (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    preorderLengths M g r₀ (h + 1) ≠ [] := by
  cases M with
  | zero => omega
  | succ M => simp [preorderLengths, List.replicate_succ, List.flatten_cons]

/-- The numeric recursive span is exactly the actual packed span of the
preorder list; it is not merely a formal upper bound. -/
theorem packedSpan_preorderLengths (M g r₀ h : ℕ) (hM : 1 ≤ M) :
    packedSpan g (preorderLengths M g r₀ h) = span M g r₀ h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [preorderLengths_succ, packedSpan_flatten_replicate M g _ hM (by simp), span_succ]
    congr 1
    congr 1
    cases h with
    | zero => simp
    | succ h =>
      rw [packedSpan_cons g _ _ (preorderLengths_succ_ne_nil M g r₀ h hM), ih,
        childSpan_succ]

/-- Every emitted window is at least the chosen entropy threshold. -/
theorem threshold_le_of_mem_preorderLengths (M g r₀ h r : ℕ)
    (hr : r ∈ preorderLengths M g r₀ h) : r₀ ≤ r := by
  induction h with
  | zero => simp at hr
  | succ h ih =>
    rw [preorderLengths_succ] at hr
    obtain ⟨L, hL, hr⟩ := List.mem_flatten.mp hr
    have heq := (List.mem_replicate.mp hL).2
    subst L
    rcases List.mem_cons.mp hr with rfl | hr
    · exact threshold_le_length _ _ _ _
    · exact ih hr

end Problem310.WindowRecursion

end OAI
