import OAI.Algebra.FormulaHitting.Program

namespace OAI

namespace NCHitting

open BitModel

private theorem length_flatMap_uniform {α β : Type*} (xs : List α) (f : α → List β)
    (k : ℕ) (h : ∀ x ∈ xs, (f x).length = k) :
    (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, (f y).length = k := by
      intro y hy
      exact h y (by simp [hy])
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [hx, ih hxs, Nat.add_mul]
    omega

private theorem getElem?_flatMap_uniform {α β : Type*} (xs : List α) (f : α → List β)
    (k : ℕ) (h : ∀ x ∈ xs, (f x).length = k) (i j : ℕ) (hj : j < k) :
    (xs.flatMap f)[i * k + j]? = xs[i]?.bind (fun x => (f x)[j]?) := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, (f y).length = k := by
      intro y hy
      exact h y (by simp [hy])
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.flatMap_cons,
        List.getElem?_cons_zero, Option.bind_some]
      exact List.getElem?_append_left (by omega)
    | succ i =>
      have hlarge : (f x).length ≤ (i + 1) * k + j := by
        rw [hx, Nat.add_mul]
        omega
      have hindex : (i + 1) * k + j - (f x).length = i * k + j := by
        rw [hx, Nat.add_mul]
        omega
      simp only [List.flatMap_cons, List.getElem?_cons_succ]
      rw [List.getElem?_append_right hlarge, hindex]
      exact ih hxs i

private theorem rows_length (d i : ℕ) :
    ((List.range d).flatMap fun r => (List.range d).map fun q => encodedEntry i r q).length = d * d := by
  apply (length_flatMap_uniform (List.range d) _ d ?_).trans
  · simp
  · intro r hr
    simp

theorem generate_output_length (n s : ℕ) :
    (generate n s).output.length = n * dimension n s * dimension n s := by
  rw [generate_output]
  by_cases h : n = 1 ∧ s = 1
  · rcases h with ⟨rfl, rfl⟩
    simp [encodedOutput, dimension]
  · simp only [encodedOutput, ite_eq_right h, dimension]
    have hl := length_flatMap_uniform (List.range n)
      (fun i => (List.range (2 * n * s ^ 2)).flatMap fun r =>
        (List.range (2 * n * s ^ 2)).map fun q => encodedEntry i r q)
      ((2 * n * s ^ 2) * (2 * n * s ^ 2)) (fun i _ => rows_length _ i)
    simp [Nat.mul_assoc] at hl ⊢

theorem encodedEntry_numerator_le (i r q : ℕ) : (encodedEntry i r q).numerator ≤ 1 := by
  unfold encodedEntry
  split_ifs <;> simp

theorem encodedEntry_denominator_size_le {n d i r q : ℕ} (hi : i < n) (hr : r < d) :
    (encodedEntry i r q).denominator.size ≤ entryBitBound n d := by
  unfold encodedEntry
  split_ifs with h
  · exact denominator_size_le (q := q) (Nat.succ_le_of_lt hi) hr
  · simp only [Nat.size_one]
    unfold entryBitBound
    omega

theorem generate_entry_bounds {n s : ℕ} (entry : RationalCode)
    (hentry : entry ∈ (generate n s).output) :
    0 < entry.denominator ∧ entry.numerator ≤ 1 ∧
      entry.denominator.size ≤ entryBitBound n (dimension n s) ∧
      entry.bits ≤ 4 + entryBitBound n (dimension n s) := by
  rw [generate_output] at hentry
  by_cases h : n = 1 ∧ s = 1
  · rcases h with ⟨rfl, rfl⟩
    simp only [encodedOutput, and_self, ite_true, List.mem_singleton] at hentry
    subst entry
    norm_num [dimension, entryBitBound, RationalCode.bits, width]
  · simp only [encodedOutput, ite_eq_right h, List.mem_flatMap, List.mem_map, List.mem_range] at hentry
    obtain ⟨i, hi, r, hr, q, hq, rfl⟩ := hentry
    have hd : dimension n s = 2 * n * s ^ 2 := by simp [dimension, h]
    rw [hd]
    exact ⟨encodedEntry_denominator_pos i r q, encodedEntry_numerator_le i r q,
      encodedEntry_denominator_size_le hi hr, encodedEntry_bits_le hi hr⟩

private theorem flattened_entry {n d i r q : ℕ} (hi : i < n) (hr : r < d) (hq : q < d) :
    ((List.range n).flatMap fun i => (List.range d).flatMap fun r =>
      (List.range d).map fun q => encodedEntry i r q)[i * d * d + r * d + q]? =
        some (encodedEntry i r q) := by
  have hj : r * d + q < d * d := by
    calc
      r * d + q < r * d + d := Nat.add_lt_add_left hq _
      _ = (r + 1) * d := by rw [Nat.add_mul]; omega
      _ ≤ d * d := Nat.mul_le_mul_right d (by omega)
  have hout := getElem?_flatMap_uniform (List.range n)
    (fun i => (List.range d).flatMap fun r => (List.range d).map fun q => encodedEntry i r q)
    (d * d) (fun i _ => rows_length d i) i (r * d + q) hj
  rw [List.getElem?_range hi] at hout
  simp only [Option.bind_some] at hout
  have hin := getElem?_flatMap_uniform (List.range d)
    (fun r => (List.range d).map fun q => encodedEntry i r q)
    d (by intro r _; simp) r q hq
  rw [List.getElem?_range hr] at hin
  simp only [Option.bind_some] at hin
  rw [List.getElem?_map, List.getElem?_range hq] at hin
  simp only [Option.map_some] at hin
  simpa only [Nat.mul_assoc, Nat.add_assoc] using hout.trans hin

theorem generate_entry_code {n s i r q : ℕ} (hi : i < n)
    (hr : r < dimension n s) (hq : q < dimension n s) :
    (generate n s).output[i * dimension n s * dimension n s + r * dimension n s + q]? =
      some (if n = 1 ∧ s = 1 then ⟨false, 1, 1⟩ else encodedEntry i r q) := by
  rw [generate_output]
  by_cases h : n = 1 ∧ s = 1
  · rcases h with ⟨rfl, rfl⟩
    have hi0 : i = 0 := by omega
    have hr0 : r = 0 := by simpa [dimension] using hr
    have hq0 : q = 0 := by simpa [dimension] using hq
    subst i
    subst r
    subst q
    simp [encodedOutput, dimension]
  · have hd : dimension n s = 2 * n * s ^ 2 := by simp [dimension, h]
    rw [hd] at hr hq ⊢
    simp only [encodedOutput, ite_eq_right h]
    exact flattened_entry hi hr hq

theorem generate_entry_decode (n s : ℕ) (i : Fin n) (r q : Fin (dimension n s)) :
    decode (((generate n s).output[i.val * dimension n s * dimension n s +
      r.val * dimension n s + q.val]?).getD ⟨false, 0, 1⟩) = generator n s i r q := by
  rw [generate_entry_code i.isLt r.isLt q.isLt]
  simp only [Option.getD_some]
  by_cases h : n = 1 ∧ s = 1
  · simp [h, generator, decode]
  · simp only [generator, ite_eq_right h]
    exact decode_encodedEntry i.val r.val q.val

end NCHitting

end OAI
