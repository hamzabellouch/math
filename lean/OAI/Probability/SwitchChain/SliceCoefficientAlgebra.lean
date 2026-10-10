import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceCoefficients

variable {V : Type*} [sectionFintypeV : Fintype V] [DecidableEq V]

def linearPair (u : V → ℝ) (i j : V) : ℝ :=
  if i = j then 0 else u i + u j

def rowSum (c : V → V → ℝ) (i : V) : ℝ := ∑ j, c i j

def outside (i j : V) : Finset V := (Finset.univ.erase i).erase j

def meetingSum (c : V → V → ℝ) (i j : V) : ℝ :=
  ∑ k ∈ outside i j, (c i k + c j k)

def disjointSum (c : V → V → ℝ) (i j : V) : ℝ :=
  (∑ k ∈ outside i j, ∑ l ∈ outside i j, c k l) / 2

theorem sum_outside (f : V → ℝ) {i j : V} (hij : i ≠ j) :
    (∑ k ∈ outside i j, f k) = (∑ k, f k) - f i - f j := by
  have hi := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hj := Finset.sum_erase_add (Finset.univ.erase i) f
    (by simp [Ne.symm hij] : j ∈ Finset.univ.erase i)
  unfold outside
  linarith

theorem linearPair_rowSum (u : V → ℝ) (hu : ∑ i, u i = 0) (i : V) :
    rowSum (linearPair u) i = ((Fintype.card V : ℝ) - 2) * u i := by
  have heq (j : V) : linearPair u i j =
      (u i + u j) - (if i = j then 2 * u i else 0) := by
    by_cases hij : i = j <;> simp [linearPair, hij] ; ring
  simp only [rowSum, heq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hu,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem meetingSum_eq (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j) :
    meetingSum c i j = rowSum c i + rowSum c j - 2 * c i j := by
  unfold meetingSum
  rw [Finset.sum_add_distrib, sum_outside _ hij, sum_outside _ hij]
  simp only [hdiag, hsym j i, rowSum]
  ring

theorem double_outside_eq (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j) :
    (∑ k ∈ outside i j, ∑ l ∈ outside i j, c k l) =
      (∑ k, rowSum c k) - 2 * rowSum c i - 2 * rowSum c j + 2 * c i j := by
  simp_rw [sum_outside (fun l => c _ l) hij]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_outside _ hij, sum_outside _ hij, sum_outside _ hij]
  have hci : (∑ k, c k i) = rowSum c i := by
    unfold rowSum
    apply Finset.sum_congr rfl
    intro k hk
    exact hsym k i
  have hcj : (∑ k, c k j) = rowSum c j := by
    unfold rowSum
    apply Finset.sum_congr rfl
    intro k hk
    exact hsym k j
  simp only [hdiag, hsym j i, hci, hcj]
  change (∑ k, rowSum c k) - rowSum c i - rowSum c j -
    (rowSum c i - 0 - c i j) - (rowSum c j - c i j - 0) = _
  ring

include sectionFintypeV in
theorem linearPair_symmetric (u : V → ℝ) (i j : V) :
    linearPair u i j = linearPair u j i := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [linearPair, eq_comm, add_comm]

include sectionFintypeV in
@[simp] theorem linearPair_diag (u : V → ℝ) (i : V) : linearPair u i i = 0 := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [linearPair]

theorem linearPair_total (u : V → ℝ) (hu : ∑ i, u i = 0) :
    ∑ i, rowSum (linearPair u) i = 0 := by
  simp_rw [linearPair_rowSum u hu, ← Finset.mul_sum, hu, mul_zero]

theorem linearPair_meetingSum (u : V → ℝ) (hu : ∑ i, u i = 0)
    {i j : V} (hij : i ≠ j) :
    meetingSum (linearPair u) i j =
      ((Fintype.card V : ℝ) - 4) * linearPair u i j := by
  rw [meetingSum_eq _ (linearPair_symmetric u) (linearPair_diag u) hij]
  simp only [linearPair_rowSum u hu, linearPair, hij, ite_false]
  ring

theorem linearPair_disjointSum (u : V → ℝ) (hu : ∑ i, u i = 0)
    {i j : V} (hij : i ≠ j) :
    disjointSum (linearPair u) i j =
      -((Fintype.card V : ℝ) - 3) * linearPair u i j := by
  unfold disjointSum
  rw [double_outside_eq _ (linearPair_symmetric u) (linearPair_diag u) hij,
    linearPair_total u hu]
  simp only [linearPair_rowSum u hu, linearPair, hij, ite_false]
  ring

theorem rowZero_meetingSum (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) {i j : V} (hij : i ≠ j) :
    meetingSum c i j = -2 * c i j := by
  rw [meetingSum_eq c hsym hdiag hij, hrow, hrow]
  ring

theorem rowZero_disjointSum (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) {i j : V} (hij : i ≠ j) :
    disjointSum c i j = c i j := by
  unfold disjointSum
  rw [double_outside_eq c hsym hdiag hij]
  simp [hrow]

theorem linearPair_injective_of_centered (hcard : 3 ≤ Fintype.card V)
    (u v : V → ℝ) (hu : ∑ i, u i = 0) (hv : ∑ i, v i = 0)
    (heq : linearPair u = linearPair v) : u = v := by
  funext i
  have hrow := congrArg (fun c => rowSum c i) heq
  rw [linearPair_rowSum u hu, linearPair_rowSum v hv] at hrow
  have hc : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
  have hn : (Fintype.card V : ℝ) - 2 ≠ 0 := by linarith
  exact mul_left_cancel₀ hn hrow

theorem linearPair_orthogonal_rowZero (u : V → ℝ) (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) :
    (∑ i, ∑ j, linearPair u i j * c i j) = 0 := by
  have heq (i j : V) : linearPair u i j * c i j =
      u i * c i j + u j * c i j := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simp only [linearPair, hij, ite_false]
      ring
  simp_rw [heq, Finset.sum_add_distrib]
  have hfirst : (∑ i, ∑ j, u i * c i j) = 0 := by
    simp_rw [← Finset.mul_sum]
    change (∑ i, u i * rowSum c i) = 0
    simp [hrow]
  have hsecond : (∑ i, ∑ j, u j * c i j) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hcol (j : V) : (∑ i, c i j) = 0 := by
      calc
        (∑ i, c i j) = rowSum c j := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hsym i j
        _ = 0 := hrow j
    simp [hcol]
  rw [hfirst, hsecond, add_zero]

theorem linearPair_row_sq (u : V → ℝ) (hu : ∑ i, u i = 0) (i : V) :
    (∑ j, linearPair u i j ^ 2) =
      ((Fintype.card V : ℝ) - 4) * u i ^ 2 + ∑ j, u j ^ 2 := by
  have heq (j : V) : linearPair u i j ^ 2 =
      (u i ^ 2 + 2 * u i * u j + u j ^ 2) -
        (if i = j then 4 * u i ^ 2 else 0) := by
    by_cases hij : i = j <;> simp [linearPair, hij] <;> ring
  simp only [heq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, hu, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  ring

theorem linearPair_norm_sq (u : V → ℝ) (hu : ∑ i, u i = 0) :
    (∑ i, ∑ j, linearPair u i j ^ 2) / 2 =
      ((Fintype.card V : ℝ) - 2) * ∑ i, u i ^ 2 := by
  simp only [linearPair_row_sq u hu, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

def constantPair (a : ℝ) (i j : V) : ℝ := if i = j then 0 else a

include sectionFintypeV in
@[simp] theorem constantPair_diag (a : ℝ) (i : V) : constantPair a i i = 0 := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [constantPair]

include sectionFintypeV in
theorem constantPair_symmetric (a : ℝ) (i j : V) :
    constantPair a i j = constantPair a j i := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [constantPair, eq_comm]

theorem constantPair_rowSum (a : ℝ) (i : V) :
    rowSum (constantPair a) i = ((Fintype.card V : ℝ) - 1) * a := by
  have heq (j : V) : constantPair a i j = a - (if i = j then a else 0) := by
    by_cases h : i = j <;> simp [constantPair, h]
  simp only [rowSum, heq, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem exists_coefficient_decomposition (hcard : 3 ≤ Fintype.card V)
    (c : V → V → ℝ) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) :
    ∃ a : ℝ, ∃ u : V → ℝ, ∃ z : V → V → ℝ,
      (∑ i, u i) = 0 ∧ (∀ i, rowSum z i = 0) ∧
      (∀ i j, z i j = z j i) ∧ (∀ i, z i i = 0) ∧
      (∀ i j, c i j = constantPair a i j + linearPair u i j + z i j) := by
  let N : ℝ := Fintype.card V
  let C : ℝ := ∑ i, rowSum c i
  let a : ℝ := C / (N * (N - 1))
  let u : V → ℝ := fun i => (rowSum c i - C / N) / (N - 2)
  let z : V → V → ℝ := fun i j => c i j - constantPair a i j - linearPair u i j
  have hN3 : 3 ≤ N := by
    dsimp [N]
    exact_mod_cast hcard
  have hN : N ≠ 0 := by linarith
  have hN1 : N - 1 ≠ 0 := by linarith
  have hN2 : N - 2 ≠ 0 := by linarith
  have hu : (∑ i, u i) = 0 := by
    simp only [u, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    change (C - N * C / N) / (N - 2) = 0
    field_simp
    ring
  have hzrow (i : V) : rowSum z i = 0 := by
    change (∑ j, (c i j - constantPair a i j - linearPair u i j)) = 0
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    change rowSum c i - rowSum (constantPair a) i - rowSum (linearPair u) i = 0
    rw [constantPair_rowSum, linearPair_rowSum u hu]
    change rowSum c i - (N - 1) * (C / (N * (N - 1))) -
      (N - 2) * ((rowSum c i - C / N) / (N - 2)) = 0
    field_simp
    ring
  refine ⟨a, u, z, hu, hzrow, ?_, ?_, ?_⟩
  · intro i j
    simp only [z, hsym i j, constantPair_symmetric a i j, linearPair_symmetric u i j]
  · intro i
    simp [z, hdiag]
  · intro i j
    dsimp [z]
    ring

def intersectionAction (a b d : ℝ) (c : V → V → ℝ) (i j : V) : ℝ :=
  if i = j then 0 else a * c i j + b * meetingSum c i j + d * disjointSum c i j

theorem intersectionAction_linearPair (a b d : ℝ) (u : V → ℝ)
    (hu : ∑ i, u i = 0) (i j : V) :
    intersectionAction a b d (linearPair u) i j =
      (a + ((Fintype.card V : ℝ) - 4) * b -
        ((Fintype.card V : ℝ) - 3) * d) * linearPair u i j := by
  by_cases hij : i = j
  · subst j
    simp [intersectionAction]
  · simp only [intersectionAction, hij, ite_false,
      linearPair_meetingSum u hu hij, linearPair_disjointSum u hu hij]
    ring

theorem intersectionAction_rowZero (a b d : ℝ) (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) (i j : V) :
    intersectionAction a b d c i j = (a - 2 * b + d) * c i j := by
  by_cases hij : i = j
  · subst j
    simp [intersectionAction, hdiag]
  · simp only [intersectionAction, hij, ite_false,
      rowZero_meetingSum c hsym hdiag hrow hij,
      rowZero_disjointSum c hsym hdiag hrow hij]
    ring

end Problem315.SliceCoefficients

end

end OAI
