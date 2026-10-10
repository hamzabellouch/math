import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335
namespace BalancedSchedule

/-- Number of `U` layers following the `i`th `V` layer. -/
def chunkLength (k s i : ℕ) : ℕ :=
  1 + ((i + 1) * s / k - i * s / k)

lemma quotient_mono (k s : ℕ) {i j : ℕ} (hij : i ≤ j) :
    i * s / k ≤ j * s / k :=
  Nat.div_le_div_right (Nat.mul_le_mul_right s hij)

lemma chunkLength_pos (k s i : ℕ) : 0 < chunkLength k s i := by
  unfold chunkLength
  omega

lemma chunkLength_le_two {k s : ℕ} (hs : s < k) (i : ℕ) :
    chunkLength k s i ≤ 2 := by
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le s) hs
  have hrem := Nat.mod_lt (i * s) hk
  have hdiv := Nat.mod_add_div (i * s) k
  have hnext : (i + 1) * s < (i * s / k + 2) * k := by nlinarith
  have hq : (i + 1) * s / k < i * s / k + 2 :=
    (Nat.div_lt_iff_lt_mul hk).2 hnext
  unfold chunkLength
  omega

lemma chunkLength_eq_one_or_two {k s : ℕ} (hs : s < k) (i : ℕ) :
    chunkLength k s i = 1 ∨ chunkLength k s i = 2 := by
  have hp := chunkLength_pos k s i
  have hl := chunkLength_le_two hs i
  omega

/-- The number of `U` layers in consecutive complete chunks. -/
lemma sum_chunkLength (k s a r : ℕ) :
    (∑ j ∈ Finset.range r, chunkLength k s (a + j)) =
      r + ((a + r) * s / k - a * s / k) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    have h₁ := quotient_mono k s (show a ≤ a + r by omega)
    have h₂ := quotient_mono k s (show a + r ≤ a + (r + 1) by omega)
    unfold chunkLength
    have heq : a + r + 1 = a + (r + 1) := by omega
    rw [heq]
    omega

lemma sum_all_chunkLength {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (∑ j ∈ Finset.range k, chunkLength k s j) = k + s := by
  simpa [Nat.mul_div_cancel_left s hk] using sum_chunkLength k s 0 k

/-- A complete-chunk block has discrepancy strictly less than `ρ = k / (k+s)`. -/
lemma complete_chunks_discrepancy_lt {k : ℕ} (hk : 0 < k) (s a r : ℕ) :
    (r : ℝ) - (k : ℝ) / (k + s) *
      (∑ j ∈ Finset.range r, (chunkLength k s (a + j) : ℝ)) <
      (k : ℝ) / (k + s) := by
  have hm := quotient_mono k s (show a ≤ a + r by omega)
  have hsum : (∑ j ∈ Finset.range r, (chunkLength k s (a + j) : ℝ)) =
      (r : ℝ) + (((a + r) * s / k : ℕ) : ℝ) - ((a * s / k : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, sum_chunkLength]
    rw [Nat.cast_add, Nat.cast_sub hm]
    ring
  rw [hsum]
  have hd₀ := Nat.mod_add_div (a * s) k
  have hd₁ := Nat.mod_add_div ((a + r) * s) k
  have hr₁ := Nat.mod_lt ((a + r) * s) hk
  have hd₀' : ((a * s % k : ℕ) : ℝ) + (k : ℝ) * ((a * s / k : ℕ) : ℝ) =
      (a : ℝ) * s := by exact_mod_cast hd₀
  have hd₁' : (((a + r) * s % k : ℕ) : ℝ) + (k : ℝ) *
      (((a + r) * s / k : ℕ) : ℝ) = ((a : ℝ) + r) * s := by
    exact_mod_cast hd₁
  have hr₁' : (((a + r) * s % k : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast hr₁
  have hr₀' : 0 ≤ ((a * s % k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hks : (0 : ℝ) < k + s := by positivity
  apply (mul_lt_mul_iff_left₀ hks).1
  field_simp
  nlinarith

/-- The relative density used in the mixed rank measure. -/
def rho (k s : ℕ) : ℝ := (k : ℝ) / (k + s)

/-- `true` denotes a `V` layer and `false` denotes a `U` layer. -/
def chunk (k s i : ℕ) : List Bool :=
  true :: List.replicate (chunkLength k s i) false

/-- The first `r` complete chunks of the balanced schedule. -/
def wordPrefix (k s : ℕ) : ℕ → List Bool
  | 0 => []
  | r + 1 => wordPrefix k s r ++ chunk k s r

/-- The complete balanced layer schedule. -/
def word (k s : ℕ) : List Bool := wordPrefix k s k

/-- The number of `V` layers minus `ρ` times the number of `U` layers. -/
def discrepancy (k s : ℕ) (w : List Bool) : ℝ :=
  (w.count true : ℝ) - rho k s * (w.count false : ℝ)

@[simp] lemma count_true_chunk (k s i : ℕ) : (chunk k s i).count true = 1 := by
  simp [chunk, List.count_replicate]

@[simp] lemma count_false_chunk (k s i : ℕ) :
    (chunk k s i).count false = chunkLength k s i := by
  simp [chunk]

@[simp] lemma count_true_wordPrefix (k s r : ℕ) :
    (wordPrefix k s r).count true = r := by
  induction r with
  | zero => simp [wordPrefix]
  | succ r ih => simp [wordPrefix, List.count_append, ih]

@[simp] lemma count_false_wordPrefix (k s r : ℕ) :
    (wordPrefix k s r).count false = r + r * s / k := by
  induction r with
  | zero => simp [wordPrefix]
  | succ r ih =>
    simp only [wordPrefix, List.count_append, ih, count_false_chunk]
    have hm : r * s / k ≤ (r + 1) * s / k := quotient_mono k s (by omega)
    unfold chunkLength
    omega

@[simp] lemma discrepancy_nil (k s : ℕ) : discrepancy k s [] = 0 := by
  simp [discrepancy]

@[simp] lemma discrepancy_append (k s : ℕ) (w z : List Bool) :
    discrepancy k s (w ++ z) = discrepancy k s w + discrepancy k s z := by
  simp only [discrepancy, List.count_append, Nat.cast_add]
  ring

@[simp] lemma discrepancy_chunk (k s i : ℕ) :
    discrepancy k s (chunk k s i) = 1 - rho k s * chunkLength k s i := by
  simp [discrepancy]

lemma discrepancy_wordPrefix_eq_mod {k : ℕ} (hk : 0 < k) (s r : ℕ) :
    discrepancy k s (wordPrefix k s r) = ((r * s % k : ℕ) : ℝ) / (k + s) := by
  simp only [discrepancy, count_true_wordPrefix, count_false_wordPrefix, Nat.cast_add]
  have hd := Nat.mod_add_div (r * s) k
  have hd' : ((r * s % k : ℕ) : ℝ) + (k : ℝ) * ((r * s / k : ℕ) : ℝ) =
      (r : ℝ) * s := by exact_mod_cast hd
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hks : (0 : ℝ) < k + s := by positivity
  unfold rho
  field_simp
  nlinarith

lemma discrepancy_wordPrefix_nonneg {k : ℕ} (hk : 0 < k) (s r : ℕ) :
    0 ≤ discrepancy k s (wordPrefix k s r) := by
  rw [discrepancy_wordPrefix_eq_mod hk]
  positivity

lemma discrepancy_wordPrefix_lt_rho {k : ℕ} (hk : 0 < k) (s r : ℕ) :
    discrepancy k s (wordPrefix k s r) < rho k s := by
  rw [discrepancy_wordPrefix_eq_mod hk]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hks : (0 : ℝ) < k + s := by positivity
  apply (div_lt_div_iff_of_pos_right hks).2
  exact_mod_cast Nat.mod_lt (r * s) hk

lemma take_chunk_discrepancy (k s i p : ℕ) (hp : 0 < p) :
    discrepancy k s ((chunk k s i).take p) =
      1 - rho k s * (min (p - 1) (chunkLength k s i) : ℕ) := by
  simp [chunk, List.take_cons hp, discrepancy, List.count_replicate]

/-- Every prefix of the balanced schedule stays in a strip of width `1+ρ`. -/
lemma take_wordPrefix_discrepancy_bounds {k : ℕ} (hk : 0 < k) (s r p : ℕ) :
    0 ≤ discrepancy k s ((wordPrefix k s r).take p) ∧
      discrepancy k s ((wordPrefix k s r).take p) < 1 + rho k s := by
  have hrho : 0 ≤ rho k s := by unfold rho; positivity
  induction r with
  | zero => simp [wordPrefix]; positivity
  | succ r ih =>
    change 0 ≤ discrepancy k s ((wordPrefix k s r ++ chunk k s r).take p) ∧
      discrepancy k s ((wordPrefix k s r ++ chunk k s r).take p) < 1 + rho k s
    by_cases hp : p ≤ (wordPrefix k s r).length
    · simpa only [List.take_append_of_le_length hp] using ih
    · have hlt : (wordPrefix k s r).length < p := by omega
      rw [List.take_append, List.take_of_length_le hlt.le, discrepancy_append]
      rw [take_chunk_discrepancy k s r _ (by omega)]
      have hmin : ((min (p - (wordPrefix k s r).length - 1) (chunkLength k s r) : ℕ) : ℝ) ≤
          (chunkLength k s r : ℝ) := by exact_mod_cast Nat.min_le_right _ _
      have hmul := mul_le_mul_of_nonneg_left hmin hrho
      have hnonneg := discrepancy_wordPrefix_nonneg hk s (r + 1)
      simp only [wordPrefix, discrepancy_append, discrepancy_chunk] at hnonneg
      have hupper := discrepancy_wordPrefix_lt_rho hk s r
      have hprod : 0 ≤ rho k s *
          ((min (p - (wordPrefix k s r).length - 1) (chunkLength k s r) : ℕ) : ℝ) := by positivity
      constructor <;> linarith

/-- Every interval of layers has discrepancy strictly less than `1+ρ`. -/
lemma interval_discrepancy_lt {k : ℕ} (hk : 0 < k) (s r a len : ℕ) :
    discrepancy k s (((wordPrefix k s r).drop a).take len) < 1 + rho k s := by
  have h₁ := (take_wordPrefix_discrepancy_bounds hk s r a).1
  have h₂ := (take_wordPrefix_discrepancy_bounds hk s r (a + len)).2
  rw [List.take_add, discrepancy_append] at h₂
  linarith

lemma infix_discrepancy_lt {k : ℕ} (hk : 0 < k) (s r : ℕ) {w : List Bool}
    (hw : w <:+: wordPrefix k s r) : discrepancy k s w < 1 + rho k s := by
  rcases hw with ⟨l, z, heq⟩
  have h := interval_discrepancy_lt hk s r l.length w.length
  rw [← heq, List.append_assoc, List.drop_left, List.take_left] at h
  exact h

@[simp] lemma word_count_true (k s : ℕ) : (word k s).count true = k := by
  simp [word]

@[simp] lemma word_count_false {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (word k s).count false = k + s := by
  simp [word, Nat.mul_div_cancel_left s hk]

lemma word_length {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (word k s).length = 2 * k + s := by
  rw [← List.count_true_add_count_false, word_count_true, word_count_false hk]
  omega

@[simp] lemma discrepancy_word {k : ℕ} (hk : 0 < k) (s : ℕ) :
    discrepancy k s (word k s) = 0 := by
  rw [word, discrepancy_wordPrefix_eq_mod hk]
  simp

@[simp] lemma chunk_head (k s i : ℕ) : (chunk k s i).head? = some true := rfl

@[simp] lemma chunk_last (k s i : ℕ) : (chunk k s i).getLast? = some false := by
  have hp := chunkLength_pos k s i
  simp [chunk, List.getLast?_cons, List.getLast?_replicate, Nat.ne_of_gt hp]

lemma wordPrefix_head {r : ℕ} (hr : 0 < r) (k s : ℕ) :
    (wordPrefix k s r).head? = some true := by
  induction r with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero => simp [wordPrefix]
    | succ r =>
      change (wordPrefix k s (r + 1) ++ chunk k s (r + 1)).head? = some true
      rw [List.head?_append, ih (by omega)]
      rfl

lemma wordPrefix_last {r : ℕ} (hr : 0 < r) (k s : ℕ) :
    (wordPrefix k s r).getLast? = some false := by
  cases r with
  | zero => omega
  | succ r => simp [wordPrefix, List.getLast?_append]

lemma replicate_no_adjacent_V (d : ℕ) :
    (List.replicate d false).IsChain (fun a b => a = false ∨ b = false) := by
  rw [List.isChain_iff_getElem]
  simp

lemma chunk_no_adjacent_V (k s i : ℕ) :
    (chunk k s i).IsChain (fun a b => a = false ∨ b = false) := by
  unfold chunk
  apply (List.isChain_cons).2
  constructor
  · intro y hy
    right
    exact List.eq_of_mem_replicate (List.mem_of_mem_head? hy)
  · exact replicate_no_adjacent_V _

/-- No two `V` layers are adjacent, a key independence property of the schedule. -/
lemma wordPrefix_no_adjacent_V (k s r : ℕ) :
    (wordPrefix k s r).IsChain (fun a b => a = false ∨ b = false) := by
  induction r with
  | zero => simp [wordPrefix]
  | succ r ih =>
    apply ih.append (chunk_no_adjacent_V k s r)
    intro x hx y hy
    cases r with
    | zero => simp [wordPrefix] at hx
    | succ r =>
      left
      have hlast := wordPrefix_last (r := r + 1) (by omega) k s
      rw [hlast] at hx
      simpa [eq_comm] using hx

lemma word_no_adjacent_V (k s : ℕ) :
    (word k s).IsChain (fun a b => a = false ∨ b = false) :=
  wordPrefix_no_adjacent_V k s k

/-- Finite-indexed form of the balanced layer partition. -/
def indexedWord {k : ℕ} (hk : 0 < k) (s : ℕ) : Fin (2 * k + s) → Bool :=
  fun i => (word k s).get ⟨i.val, by simp [word_length hk]⟩

/-- The finite set of the `V` layers. -/
def vLayers {k : ℕ} (hk : 0 < k) (s : ℕ) : Finset (Fin (2 * k + s)) :=
  Finset.univ.filter (fun i => indexedWord hk s i = true)

/-- The finite set of the `U` layers. -/
def uLayers {k : ℕ} (hk : 0 < k) (s : ℕ) : Finset (Fin (2 * k + s)) :=
  Finset.univ.filter (fun i => indexedWord hk s i = false)

lemma card_vLayers {k : ℕ} (hk : 0 < k) (s : ℕ) : (vLayers hk s).card = k := by
  let v : List.Vector Bool (2 * k + s) := ⟨word k s, word_length hk s⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count true v
  change (vLayers hk s).card = (word k s).count true at h
  simpa using h

lemma card_uLayers {k : ℕ} (hk : 0 < k) (s : ℕ) : (uLayers hk s).card = k + s := by
  let v : List.Vector Bool (2 * k + s) := ⟨word k s, word_length hk s⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count false v
  change (uLayers hk s).card = (word k s).count false at h
  simpa [word_count_false hk] using h

lemma layer_partition {k : ℕ} (hk : 0 < k) (s : ℕ) :
    vLayers hk s ∪ uLayers hk s = Finset.univ := by
  ext i
  simp only [vLayers, uLayers, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and, iff_true]
  cases indexedWord hk s i <;> simp

lemma layer_disjoint {k : ℕ} (hk : 0 < k) (s : ℕ) :
    Disjoint (vLayers hk s) (uLayers hk s) := by
  apply Finset.disjoint_left.2
  intro i hi hj
  simp only [vLayers, uLayers, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  rw [hi] at hj
  cases hj

lemma indexedWord_no_adjacent_V {k : ℕ} (hk : 0 < k) (s : ℕ)
    (i j : Fin (2 * k + s)) (hij : i.val + 1 = j.val) :
    indexedWord hk s i = false ∨ indexedWord hk s j = false := by
  have hlt : i.val + 1 < (word k s).length := by
    rw [word_length hk, hij]
    exact j.isLt
  have h := List.isChain_iff_getElem.mp (word_no_adjacent_V k s) i.val hlt
  simpa only [indexedWord, List.get_eq_getElem, hij] using h

/-- Adjacent layer positions in either order. -/
def adjacent {n : ℕ} (i j : Fin n) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val

lemma vLayers_independent {k : ℕ} (hk : 0 < k) (s : ℕ)
    {i j : Fin (2 * k + s)} (hi : i ∈ vLayers hk s) (hij : adjacent i j) :
    j ∉ vLayers hk s := by
  intro hj
  have hi' : indexedWord hk s i = true := (Finset.mem_filter.mp hi).2
  have hj' : indexedWord hk s j = true := (Finset.mem_filter.mp hj).2
  rcases hij with hij | hji
  · have h := indexedWord_no_adjacent_V hk s i j hij
    simp [hi', hj'] at h
  · have h := indexedWord_no_adjacent_V hk s j i hji
    simp [hi', hj'] at h

/-- Internal vertices adjacent to a layer. Vertex `j` is between layers `j` and `j+1`. -/
def internalEnds {n : ℕ} (i : Fin n) : Finset (Fin (n - 1)) :=
  Finset.univ.filter (fun j => j.val = i.val ∨ j.val + 1 = i.val)

lemma internalEnds_disjoint_of_not_adjacent {n : ℕ} {i j : Fin n}
    (hne : i ≠ j) (hij : ¬ adjacent i j) :
    Disjoint (internalEnds i) (internalEnds j) := by
  apply Finset.disjoint_left.2
  intro v hvi hvj
  have hi := (Finset.mem_filter.mp hvi).2
  have hj := (Finset.mem_filter.mp hvj).2
  have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
  unfold adjacent at hij
  omega

/-- Distinct selected V layers depend on disjoint internal-vertex coordinates. -/
lemma vLayers_internalEnds_disjoint {k : ℕ} (hk : 0 < k) (s : ℕ)
    {i j : Fin (2 * k + s)} (hi : i ∈ vLayers hk s) (hj : j ∈ vLayers hk s)
    (hne : i ≠ j) : Disjoint (internalEnds i) (internalEnds j) := by
  apply internalEnds_disjoint_of_not_adjacent hne
  exact fun hadj => vLayers_independent hk s hi hadj hj

/-- The left end of an interior layer is an internal vertex. -/
lemma mem_internalEnds_left {n : ℕ} (i : Fin n) (hi : 0 < i.val) :
    (⟨i.val - 1, by omega⟩ : Fin (n - 1)) ∈ internalEnds i := by
  simp only [internalEnds, Finset.mem_filter, Finset.mem_univ, true_and]
  right
  exact Nat.sub_add_cancel hi

/-- The right end of a nonfinal layer is an internal vertex. -/
lemma mem_internalEnds_right {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    (⟨i.val, by omega⟩ : Fin (n - 1)) ∈ internalEnds i := by
  simp [internalEnds]

lemma card_internalEnds_le_two {n : ℕ} (i : Fin n) : (internalEnds i).card ≤ 2 := by
  let f : Fin (n - 1) → Bool := fun v => v.val = i.val
  have hinj : Set.InjOn f (internalEnds i : Set (Fin (n - 1))) := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hab' : (decide (a.val = i.val)) = decide (b.val = i.val) := hab
    apply Fin.ext
    by_cases hai : a.val = i.val
    · have hbi : b.val = i.val := by simpa [hai] using hab'.symm
      omega
    · have hbi : b.val ≠ i.val := by simpa [hai] using hab'.symm
      omega
  calc
    (internalEnds i).card = ((internalEnds i).image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card Bool := Finset.card_le_univ _
    _ = 2 := by decide

end BalancedSchedule
end Problem335

end

end OAI
