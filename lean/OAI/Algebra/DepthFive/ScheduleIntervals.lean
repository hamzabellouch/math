import OAI.Algebra.DepthFive.BalancedSchedule

namespace OAI

noncomputable section

namespace Problem335.BalancedSchedule

lemma card_get_eq_count (w : List Bool) (b : Bool) :
    (Finset.univ.filter (fun i : Fin w.length => w.get i = b)).card = w.count b := by
  exact Fin.card_filter_univ_eq_vector_get_eq_count b (⟨w, rfl⟩ : List.Vector Bool w.length)

/-- Counting a contiguous list interval equals counting its finite-indexed layers. -/
lemma count_slice_eq_card (w : List Bool) (a len : ℕ) (b : Bool) :
    ((w.drop a).take len).count b =
      (Finset.univ.filter (fun i : Fin w.length =>
        a ≤ i.val ∧ i.val < a + len ∧ w.get i = b)).card := by
  let z := (w.drop a).take len
  have hz : z.length = min len (w.length - a) := by simp [z]
  let shift : Fin z.length → Fin w.length := fun i => ⟨a + i.val, by
    have h := i.isLt
    omega⟩
  have hget (i : Fin z.length) : z.get i = w.get (shift i) := by
    simp only [z, List.get_eq_getElem, List.getElem_take, List.getElem_drop, shift]
  rw [← card_get_eq_count z b]
  apply Finset.card_nbij shift
  · intro i hi
    have hib := (Finset.mem_filter.mp hi).2
    have hlt := i.isLt
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · dsimp [shift]; omega
    · dsimp [shift]; omega
    · rwa [← hget]
  · intro i hi j hj hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    dsimp [shift] at h
    omega
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    let i : Fin z.length := ⟨j.val - a, by
      rw [hz]
      have h := j.isLt
      omega⟩
    have heq : shift i = j := by
      apply Fin.ext
      dsimp [shift, i]
      omega
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
    rw [hget, heq]
    exact hj'.2.2

/-- Pulling the finite-indexed partition back to a list gives the constructed schedule. -/
lemma ofFn_indexedWord {k : ℕ} (hk : 0 < k) (s : ℕ) :
    List.ofFn (indexedWord hk s) = word k s := by
  apply List.ext_getElem
  · simp [word_length hk]
  · intro i h₁ h₂
    simp [indexedWord]

/-- A finite interval of the schedule, with a specified layer type. -/
def intervalLayers {k : ℕ} (hk : 0 < k) (s a len : ℕ) (b : Bool) :
    Finset (Fin (2 * k + s)) :=
  Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < a + len ∧ indexedWord hk s i = b)

lemma card_intervalLayers {k : ℕ} (hk : 0 < k) (s a len : ℕ) (b : Bool) :
    (intervalLayers hk s a len b).card = (((word k s).drop a).take len).count b := by
  have h := count_slice_eq_card (List.ofFn (indexedWord hk s)) a len b
  rw [ofFn_indexedWord] at h
  rw [h]
  let castIndex : Fin (2 * k + s) → Fin (word k s).length :=
    fun i => ⟨i.val, by simp [word_length hk]⟩
  apply Finset.card_nbij castIndex
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hi'⟩
  · intro i hi j hj hij
    have hv := congrArg (fun t : Fin (word k s).length => t.val) hij
    exact Fin.ext hv
  · intro j hj
    let i : Fin (2 * k + s) := ⟨j.val, by simpa [word_length hk] using j.isLt⟩
    refine ⟨i, ?_, Fin.ext rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩

/-- The balanced interval discrepancy in the finite-set form used for run bounds. -/
lemma intervalLayers_discrepancy_lt {k : ℕ} (hk : 0 < k) (s a len : ℕ) :
    ((intervalLayers hk s a len true).card : ℝ) - rho k s *
      ((intervalLayers hk s a len false).card : ℝ) < 1 + rho k s := by
  rw [card_intervalLayers, card_intervalLayers]
  exact interval_discrepancy_lt hk s k a len

/-- RunLayerWeights' precise countP interface for a contiguous finite-index interval. -/
lemma indexed_infix_discrepancy_lt {k : ℕ} (hk : 0 < k) (s : ℕ)
    (b : List (Fin (2 * k + s))) (hb : b <:+: List.ofFn id) :
    (b.countP (indexedWord hk s) : ℝ) - rho k s *
      (b.countP (fun i => !indexedWord hk s i) : ℝ) < 1 + rho k s := by
  have hmap := hb.map (indexedWord hk s)
  have heq : (List.ofFn (id : Fin (2 * k + s) → Fin (2 * k + s))).map
      (indexedWord hk s) = word k s := by
    rw [List.map_ofFn]
    exact ofFn_indexedWord hk s
  rw [heq] at hmap
  have h := infix_discrepancy_lt hk s k hmap
  simpa [discrepancy, List.count_eq_countP, List.countP_map, Function.comp_def] using h

end Problem335.BalancedSchedule

end

end OAI
