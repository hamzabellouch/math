import OAI.Algebra.DepthFive.TraceComplexification

namespace OAI

/-! Elimination of the second source index in the four-path trace formula. -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {I P G : Type*} [Fintype I] [AddCommGroup G] [DecidableEq G]

/-- Extending finite source weights by zero gives the unique weight at a
specified occupation vector; this lemma also handles invalid occupations. -/
theorem sum_source_eq_zeroExtend {I : Type u_1} {G : Type u_3}
    [Fintype I] [AddCommGroup G] [DecidableEq G] (occupation : I → G)
    (hinj : Function.Injective occupation) (weight : I → ℝ) (x : G) :
    (∑ k, if occupation k = x then weight k else 0) =
      Function.extend occupation weight (fun _ => 0) x := by
  classical
  by_cases hx : ∃ k, occupation k = x
  · obtain ⟨k, rfl⟩ := hx
    rw [hinj.extend_apply]
    simp [hinj.eq_iff]
  · rw [Function.extend_apply' _ _ _ hx]
    apply Finset.sum_eq_zero
    intro k hk
    simp [show occupation k ≠ x from fun h => hx ⟨k, h⟩]

/-- The second source in a compatible four-path term is uniquely determined.
The zero extension records absent (invalid) source occupations exactly. -/
theorem fourPath_eliminate_source (occupation : I → G)
    (hinj : Function.Injective occupation) (wq ws : I → ℝ)
    (M ep eq er es : G) (A C : ℝ) :
    (∑ k, if M + ep = occupation k + eq ∧ M + er = occupation k + es then
      A * wq k * C * ws k else 0) =
      if ep - eq = er - es then
        A * Function.extend occupation wq (fun _ => 0) (M + ep - eq) * C *
          Function.extend occupation ws (fun _ => 0) (M + ep - eq)
      else 0 := by
  classical
  let x := M + ep - eq
  have hfirst (k : I) : M + ep = occupation k + eq ↔ occupation k = x := by
    dsimp [x]
    constructor
    · intro h
      exact (eq_sub_iff_add_eq).2 h.symm
    · intro h
      exact ((eq_sub_iff_add_eq).1 h).symm
  have hsecond : M + er = x + es ↔ ep - eq = er - es := by
    have hx : x + es = M + ((ep - eq) + es) := by dsimp [x]; abel
    rw [hx, add_left_cancel_iff, eq_comm, ← eq_sub_iff_add_eq]
  by_cases hx : ∃ k, occupation k = x
  · obtain ⟨k, hk⟩ := hx
    have heq (l : I) : M + ep = occupation l + eq ↔ l = k := by
      rw [hfirst, ← hk, hinj.eq_iff]
    have hsec : M + er = occupation k + es ↔ ep - eq = er - es := by
      rw [hk]
      exact hsecond
    change _ = if ep - eq = er - es then
      A * Function.extend occupation wq (fun _ => 0) x * C *
        Function.extend occupation ws (fun _ => 0) x else 0
    rw [← hk, hinj.extend_apply, hinj.extend_apply]
    rw [Finset.sum_eq_single k]
    · simp [heq, hsec]
    · intro l hl hlk
      simp [heq, hlk]
    · simp
  · have hzq := Function.extend_apply' (f := occupation) wq (fun _ => (0 : ℝ)) x hx
    change _ = if ep - eq = er - es then
      A * Function.extend occupation wq (fun _ => 0) x * C *
        Function.extend occupation ws (fun _ => 0) x else 0
    rw [hzq]
    simp only [mul_zero, zero_mul, ite_self]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : occupation k ≠ x := fun h => hx ⟨k, h⟩
    simp [hfirst, hne]

/-- The full four-path sum with the second source eliminated and invalid
source occupations retained through zero extension. -/
theorem fourPath_sum_eliminate_source [Fintype P]
    (occupation : I → G) (hinj : Function.Injective occupation)
    (eps : P → G) (weight : I → P → ℝ) :
    (∑ i, ∑ k, ∑ p, ∑ q, ∑ r, ∑ s,
      if occupation i + eps p = occupation k + eps q ∧
        occupation i + eps r = occupation k + eps s then
        weight i p * weight k q * weight i r * weight k s else 0) =
    ∑ i, ∑ p, ∑ q, ∑ r, ∑ s,
      if eps p - eps q = eps r - eps s then
        weight i p * Function.extend occupation (fun k => weight k q) (fun _ => 0)
          (occupation i + eps p - eps q) * weight i r *
        Function.extend occupation (fun k => weight k s) (fun _ => 0)
          (occupation i + eps p - eps q) else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  exact fourPath_eliminate_source occupation hinj (fun k => weight k q)
    (fun k => weight k s) (occupation i) (eps p) (eps q) (eps r) (eps s)
    (weight i p) (weight i r)

/-- The complex four-path trace with its second source removed. The signed
shift identity is required only for nonzero path weights, so invalid-path
fallback target indices do not affect the identity. -/
theorem complex_path_second_trace_eliminate_source
    {J : Type*} [Fintype J] [Fintype P] [DecidableEq I] [DecidableEq J]
    (occupation : I → G) (hinj : Function.Injective occupation)
    (targetOccupation : J → G) (htarget : Function.Injective targetOccupation)
    (eps : P → G) (shift : I → P → J) (weight : I → P → ℝ)
    (hshift : ∀ i p, weight i p ≠ 0 →
      targetOccupation (shift i p) = occupation i + eps p) :
    let A := pathShiftMatrix shift (fun i p => (weight i p : ℂ))
    ((A.conjTranspose * A) ^ 2).trace.re =
      ∑ i, ∑ p, ∑ q, ∑ r, ∑ s,
        if eps p - eps q = eps r - eps s then
          weight i p * Function.extend occupation (fun k => weight k q) (fun _ => 0)
            (occupation i + eps p - eps q) * weight i r *
          Function.extend occupation (fun k => weight k s) (fun _ => 0)
            (occupation i + eps p - eps q) else 0 := by
  classical
  dsimp
  rw [complex_path_second_trace_four_paths, ← fourPath_sum_eliminate_source occupation hinj]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hz : weight i p * weight k q * weight i r * weight k s = 0
  · simp [hz]
  · have hp' : weight i p ≠ 0 := by intro h; simp [h] at hz
    have hq' : weight k q ≠ 0 := by intro h; simp [h] at hz
    have hr' : weight i r ≠ 0 := by intro h; simp [h] at hz
    have hs' : weight k s ≠ 0 := by intro h; simp [h] at hz
    have h₁ : shift i p = shift k q ↔ occupation i + eps p = occupation k + eps q := by
      rw [← htarget.eq_iff, hshift i p hp', hshift k q hq']
    have h₂ : shift i r = shift k s ↔ occupation i + eps r = occupation k + eps s := by
      rw [← htarget.eq_iff, hshift i r hr', hshift k s hs']
    simp only [h₁, h₂]

end Problem335

end

end OAI
