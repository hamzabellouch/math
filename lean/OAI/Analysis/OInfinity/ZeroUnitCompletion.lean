import OAI.Analysis.OInfinity.NegativeBinary

namespace OAI

/-! # Finite range completion in a zero unit corner

A proper finite row and an orthogonal spare are combined with a concrete
coisometric row. The resulting isometry fills exactly the missing range.
The construction is algebraic and does not use projection classification.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Turn a coisometry into an isometry by moving its initial support into
one specified isometric range. -/
lemma coisometry_range_filler (A y : E)
    (hA : A * star A = 1) (hy : star y * y = 1)
    (hpy : (star A * A) * y = y) :
    let C := 1 - star A * A + y * A
    star C * C = 1 ∧ C * star C = 1 - star A * A + y * star y := by
  intro C
  let p := star A * A
  let e := 1 - p
  have hp : star p = p := by simp only [p, star_mul, star_star]
  have hpp : p * p = p := by
    change (star A * A) * (star A * A) = star A * A
    calc
      _ = star A * (A * star A) * A := by noncomm_ring
      _ = _ := by rw [hA, mul_one]
  have he : star e = e := by simp only [e, star_sub, star_one, hp]
  have hee : e * e = e := by dsimp only [e]; noncomm_ring [hpp]
  have hey : e * y = 0 := by
    change (1 - p) * y = 0
    rw [sub_mul, one_mul, hpy, sub_self]
  have hAe : A * e = 0 := by
    have hAp : A * p = A := by
      change A * (star A * A) = A
      rw [← mul_assoc, hA, one_mul]
    dsimp only [e]
    rw [mul_sub, mul_one, hAp, sub_self]
  have h1 : e * (y * A) = 0 := by rw [← mul_assoc, hey, zero_mul]
  have h2 : star (y * A) * e = 0 := by
    have hh := congrArg star h1
    simpa only [star_mul, he, star_zero] using hh
  have h3 : (y * A) * e = 0 := by rw [mul_assoc, hAe, mul_zero]
  have h4 : e * star (y * A) = 0 := by
    have hh := congrArg star h3
    simpa only [star_mul, he, star_zero] using hh
  have hyy : star (y * A) * (y * A) = p := by
    rw [star_mul]
    calc
      _ = star A * (star y * y) * A := by noncomm_ring
      _ = p := by rw [hy, mul_one]
  have haa : (y * A) * star (y * A) = y * star y := by
    rw [star_mul]
    calc
      _ = y * (A * star A) * star y := by noncomm_ring
      _ = _ := by rw [hA, mul_one]
  constructor
  · change star (e + y * A) * (e + y * A) = 1
    rw [star_add, he, add_mul, mul_add, mul_add, hee, h1, h2, hyy]
    dsimp only [e]
    noncomm_ring
  · change (e + y * A) * star (e + y * A) = e + y * star y
    rw [star_add, he, add_mul, mul_add, mul_add, hee, h4, h3, haa]
    abel

/-- A full finite target row fills the defect of an arbitrary finite
proper row with its given orthogonal spare. -/
lemma finite_zero_unit_range_completion {n : ℕ}
    (x : Fin n → E) (y : E) (a : Fin (n + 1) → E)
    (hx : ∀ i j, star (x i) * x j = if i = j then 1 else 0)
    (hy : star y * y = 1) (hyx : ∀ i, star y * x i = 0)
    (ha : ∀ i j, star (a i) * a j = if i = j then 1 else 0)
    (has : (∑ i, a i * star (a i)) = 1) :
    ∃ C : E, star C * C = 1 ∧
      C * star C = 1 - ∑ i, x i * star (x i) := by
  let r : Fin (n + 1) → E := Fin.cons y x
  have hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0 := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [r, Fin.cons_zero, ite_true] using hy
    · simp only [r, Fin.cons_zero, Fin.cons_succ, hyx, (Fin.succ_ne_zero j).symm, ite_false]
    · have hh := congrArg star (hyx i)
      simpa only [r, Fin.cons_zero, Fin.cons_succ, star_mul, star_star, star_zero,
        Fin.succ_ne_zero, ite_false] using hh
    · simpa only [r, Fin.cons_succ, Fin.succ_inj] using hx i j
  let A := finiteCuntzTransfer r a 1
  have hAst : star A = finiteCuntzTransfer a r 1 := by
    simpa only [A, star_one] using finiteCuntzTransfer_star r a 1
  have hAA : A * star A = 1 := by
    have hh := finiteCuntzTransfer_star_mul a r hr 1
    rw [← hAst, star_star] at hh
    simpa only [star_one, one_mul, mul_one, has] using hh
  have hAA' : star A * A = ∑ i, r i * star (r i) := by
    simpa only [A, star_one, one_mul, mul_one] using
      finiteCuntzTransfer_star_mul r a ha 1
  have hpy : (star A * A) * y = y := by
    rw [hAA']
    have hh := finiteRowPermutation_mul_row 1 r (by simp) (by simp) hr 1 0
    simpa only [finiteRowPermutation, Equiv.Perm.one_apply, r, Fin.cons_zero] using hh
  obtain ⟨hC, hC'⟩ := coisometry_range_filler A y hAA hy hpy
  refine ⟨1 - star A * A + y * A, hC, ?_⟩
  rw [hC', hAA', Fin.sum_univ_succ]
  simp only [r, Fin.cons_zero, Fin.cons_succ]
  abel

/-- A coisometric binary pair supplies every finite target size, so only
an actual orthogonal spare is needed to fill the prescribed proper row. -/
lemma finite_zero_unit_completion_from_binary {n : ℕ}
    (x : Fin n → E) (y a b : E)
    (hx : ∀ i j, star (x i) * x j = if i = j then 1 else 0)
    (hy : star y * y = 1) (hyx : ∀ i, star y * x i = 0)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hsum : a * star a + b * star b = 1) :
    ∃ C : E, star C * C = 1 ∧
      C * star C = 1 - ∑ i, x i * star (x i) := by
  exact finite_zero_unit_range_completion x y (zeroCornerRow 1 a b n) hx hy hyx
    (zeroCornerRow_gram 1 a b (star_one _) (one_mul _) ha hb hab
      (one_mul _) (one_mul _) (mul_one _) n)
    (zeroCornerRow_range_sum 1 a b (star_one _) (one_mul _) (mul_one _) hsum n)

/-- Appending the concrete missing-range isometry gives a full finite row. -/
lemma finite_zero_unit_full_row {n : ℕ}
    (x : Fin n → E) (y a b : E)
    (hx : ∀ i j, star (x i) * x j = if i = j then 1 else 0)
    (hy : star y * y = 1) (hyx : ∀ i, star y * x i = 0)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hsum : a * star a + b * star b = 1) :
    ∃ r : Fin (n + 1) → E,
      (∀ i : Fin n, r i.succ = x i) ∧
      (∀ i j, star (r i) * r j = if i = j then 1 else 0) ∧
      (∑ i, r i * star (r i)) = 1 := by
  obtain ⟨C, hC, hCr⟩ := finite_zero_unit_completion_from_binary x y a b
    hx hy hyx ha hb hab hsum
  have hPx (i : Fin n) : (∑ j, x j * star (x j)) * x i = x i := by
    simpa only [finiteRowPermutation, Equiv.Perm.one_apply] using
      finiteRowPermutation_mul_row 1 x (by simp) (by simp) hx 1 i
  have horth (i : Fin n) : star C * x i = 0 := by
    have hr : (C * star C) * x i = 0 := by
      rw [hCr, sub_mul, one_mul, hPx, sub_self]
    have hh := congrArg (fun z => star C * z) hr
    simpa only [← mul_assoc, hC, one_mul, mul_zero] using hh
  let r : Fin (n + 1) → E := Fin.cons C x
  refine ⟨r, fun i => rfl, ?_, ?_⟩
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [r, Fin.cons_zero, ite_true] using hC
    · simp only [r, Fin.cons_zero, Fin.cons_succ, horth, (Fin.succ_ne_zero j).symm, ite_false]
    · have hh := congrArg star (horth i)
      simpa only [r, Fin.cons_zero, Fin.cons_succ, star_mul, star_star, star_zero,
        Fin.succ_ne_zero, ite_false] using hh
    · simpa only [r, Fin.cons_succ, Fin.succ_inj] using hx i j
  · rw [Fin.sum_univ_succ]
    simp only [r, Fin.cons_zero, Fin.cons_succ, hCr]
    abel

/-- A countable orthogonal row in a zero-unit algebra has an exact binary
encoding of each prescribed finite prefix. The next row element is the spare. -/
lemma exists_zero_unit_binary_encoding
    (x : ℕ → E)
    (hx : ∀ i j, star (x i) * x j = if i = j then 1 else 0)
    (a b : E) (ha : star a * a = 1) (hb : star b * b = 1)
    (hab : star a * b = 0) (hsum : a * star a + b * star b = 1) (m : ℕ) :
    ∃ A B : E, star A * A = 1 ∧ star B * B = 1 ∧ star A * B = 0 ∧
      A * star A + B * star B = 1 ∧ ∀ i ≤ m, A ^ i * B = x i := by
  have fill (n : ℕ) : ∃ r : Fin (n + 1) → E,
      (∀ i : Fin n, r i.succ = x i) ∧
      (∀ i j, star (r i) * r j = if i = j then 1 else 0) ∧
      (∑ i, r i * star (r i)) = 1 := by
    refine finite_zero_unit_full_row (fun i : Fin n => x i) (x n) a b
      ?_ ?_ ?_ ha hb hab hsum
    · intro i j
      simpa only [Fin.ext_iff] using hx i j
    · simpa only [ite_true] using hx n n
    · intro i
      have hne : n ≠ (i : ℕ) := Nat.ne_of_gt i.isLt
      simpa only [hne, ite_false] using hx n i
  obtain ⟨r, hrleaf, hr, hrs⟩ := fill m
  obtain ⟨R, hRleaf, hR, hRs⟩ := fill (m + 1)
  obtain ⟨A, B, hA, hB, hAB, hsum', hB0, hstep⟩ :=
    successive_full_rows_binary m r R hr hR hrs hRs
  have hBx : B = x 0 := hB0.trans (hRleaf 0)
  refine ⟨A, B, hA, hB, hAB, hsum', ?_⟩
  intro i
  induction i with
  | zero => intro _; simpa only [pow_zero, one_mul] using hBx
  | succ i ih =>
    intro hi
    rw [pow_succ', mul_assoc, ih (by omega)]
    have h := hstep (⟨i, by omega⟩ : Fin m)
    rw [hrleaf, hRleaf] at h
    exact h

/-- The same explicit filler in a supported corner with its actual unit
`q`. No relation between `q` and the ambient identity is needed. -/
lemma relative_zero_unit_completion {n : ℕ}
    (q : E) (hq : star q = q) (hqq : q * q = q)
    (x : Fin n → E) (y a b : E)
    (hxs : ∀ i, q * x i = x i ∧ x i * q = x i)
    (hys : q * y = y ∧ y * q = y)
    (hx : ∀ i j, star (x i) * x j = if i = j then q else 0)
    (hy : star y * y = q) (hyx : ∀ i, star y * x i = 0)
    (ha : star a * a = q) (hb : star b * b = q) (hab : star a * b = 0)
    (hsum : a * star a + b * star b = q) :
    ∃ C : E, q * C = C ∧ C * q = C ∧ star C * C = q ∧
      C * star C = q - ∑ i, x i * star (x i) := by
  obtain ⟨hqa, haq, hqb, hbq⟩ := relativeCuntzPair_support q a b hq hqq ha hb hab hsum
  let x' : Fin n → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (x i) (hxs i)
  let y' : ProjectionCorner q hq hqq := projectionCornerElement q hq hqq y hys
  let a' : ProjectionCorner q hq hqq := projectionCornerElement q hq hqq a ⟨hqa, haq⟩
  let b' : ProjectionCorner q hq hqq := projectionCornerElement q hq hqq b ⟨hqb, hbq⟩
  have hx' : ∀ i j, star (x' i) * x' j = if i = j then 1 else 0 :=
    projectionCornerElement_gram q hq hqq x hxs hx
  have hy' : star y' * y' = 1 := Subtype.ext hy
  have hyx' (i : Fin n) : star y' * x' i = 0 := Subtype.ext (hyx i)
  have ha' : star a' * a' = 1 := Subtype.ext ha
  have hb' : star b' * b' = 1 := Subtype.ext hb
  have hab' : star a' * b' = 0 := Subtype.ext hab
  have hsum' : a' * star a' + b' * star b' = 1 := Subtype.ext hsum
  obtain ⟨C, hC, hCC⟩ := finite_zero_unit_completion_from_binary x' y' a' b'
    hx' hy' hyx' ha' hb' hab' hsum'
  refine ⟨C, C.property.1, C.property.2,
    congrArg (fun z : ProjectionCorner q hq hqq => (z : E)) hC, ?_⟩
  have h := congrArg (projectionCornerInclusion q hq hqq) hCC
  simp only [map_sub, map_sum, map_mul, map_star, projectionCornerInclusion_one] at h
  exact h

/-- Exact finite binary encoding in the given corner. The countable
proper row supplies its own next unused isometry at every finite stage. -/
lemma exists_relative_zero_unit_binary_encoding
    (q : E) (hq : star q = q) (hqq : q * q = q)
    (x : ℕ → E) (a b : E)
    (hxs : ∀ i, q * x i = x i ∧ x i * q = x i)
    (hx : ∀ i j, star (x i) * x j = if i = j then q else 0)
    (ha : star a * a = q) (hb : star b * b = q) (hab : star a * b = 0)
    (hsum : a * star a + b * star b = q) (m : ℕ) :
    ∃ A B : E, q * A = A ∧ A * q = A ∧ q * B = B ∧ B * q = B ∧
      star A * A = q ∧ star B * B = q ∧ star A * B = 0 ∧
      A * star A + B * star B = q ∧ ∀ i ≤ m, A ^ i * B = x i := by
  obtain ⟨hqa, haq, hqb, hbq⟩ := relativeCuntzPair_support q a b hq hqq ha hb hab hsum
  let x' : ℕ → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (x i) (hxs i)
  let a' : ProjectionCorner q hq hqq := projectionCornerElement q hq hqq a ⟨hqa, haq⟩
  let b' : ProjectionCorner q hq hqq := projectionCornerElement q hq hqq b ⟨hqb, hbq⟩
  have hx' (i j : ℕ) : star (x' i) * x' j = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      apply Subtype.ext
      change star (x i) * x j = q
      simpa only [ite_eq_left hij] using hx i j
    · rw [ite_eq_right hij]
      apply Subtype.ext
      change star (x i) * x j = 0
      simpa only [ite_eq_right hij] using hx i j
  obtain ⟨A, B, hA, hB, hAB, hsum', hencode⟩ := exists_zero_unit_binary_encoding x' hx' a' b'
    (Subtype.ext ha) (Subtype.ext hb) (Subtype.ext hab) (Subtype.ext hsum) m
  refine ⟨A, B, A.property.1, A.property.2, B.property.1, B.property.2,
    congrArg (fun z : ProjectionCorner q hq hqq => (z : E)) hA,
    congrArg (fun z : ProjectionCorner q hq hqq => (z : E)) hB,
    congrArg (fun z : ProjectionCorner q hq hqq => (z : E)) hAB,
    congrArg (fun z : ProjectionCorner q hq hqq => (z : E)) hsum', ?_⟩
  have hpow (i : ℕ) : ((A ^ i * B : ProjectionCorner q hq hqq) : E) =
      (A : E) ^ i * (B : E) := by
    induction i with
    | zero => simp only [pow_zero, one_mul]
    | succ i ih =>
      rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
      change (A : E) * ((A ^ i * B : ProjectionCorner q hq hqq) : E) = _
      rw [ih]
  intro i hi
  have h := congrArg (fun z : ProjectionCorner q hq hqq => (z : E)) (hencode i hi)
  rw [hpow] at h
  exact h

/-- On elements commuting with the initial projection, the filler has
an exact two-corner formula. This records the term that must be controlled
by the canonical-shift implementer. -/
lemma coisometry_range_filler_conjugation (A y x : E)
    (hA : A * star A = 1) (hx : Commute (star A * A) x) :
    let C := 1 - star A * A + y * A
    C * x * star C = (1 - star A * A) * x + y * (A * x * star A) * star y := by
  intro C
  let p := star A * A
  let e := 1 - p
  have hp : star p = p := by simp only [p, star_mul, star_star]
  have hpp : p * p = p := by
    change (star A * A) * (star A * A) = star A * A
    calc
      _ = star A * (A * star A) * A := by noncomm_ring
      _ = _ := by rw [hA, mul_one]
  have he : star e = e := by simp only [e, star_sub, star_one, hp]
  have hee : e * e = e := by dsimp only [e]; noncomm_ring [hpp]
  have hex : Commute e x := (Commute.one_left x).sub_left hx
  have hAe : A * e = 0 := by
    have hAp : A * p = A := by
      change A * (star A * A) = A
      rw [← mul_assoc, hA, one_mul]
    dsimp only [e]
    rw [mul_sub, mul_one, hAp, sub_self]
  have hestar : e * star A = 0 := by
    simpa only [star_mul, he, star_zero] using congrArg star hAe
  have hexe : e * x * e = e * x := by
    rw [hex.eq, mul_assoc, hee, ← hex.eq]
  have hexA : e * x * star A = 0 := by
    rw [hex.eq, mul_assoc, hestar, mul_zero]
  have hAxe : A * x * e = 0 := by
    rw [mul_assoc, ← hex.eq, ← mul_assoc, hAe, zero_mul]
  change (e + y * A) * x * star (e + y * A) = e * x + y * (A * x * star A) * star y
  rw [star_add, star_mul, he]
  calc
    _ = e * x * e + (e * x * star A) * star y +
        y * (A * x * e) + y * (A * x * star A) * star y := by noncomm_ring
    _ = _ := by rw [hexe, hexA, hAxe]; simp only [zero_mul, mul_zero, add_zero]

/-- The concrete binary shift filler accepts any unitary inserted before
the coisometry. Its final projection is independent of that insertion. -/
lemma binary_shift_shrink_products (r a : Fin 2 → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (ha : ∀ i j, star (a i) * a j = if i = j then 1 else 0)
    (has : (∑ i, a i * star (a i)) = 1) (u : unitary E) :
    let v := (u : E) * finiteCuntzTransfer r a 1
    let C := 1 - star v * v + r 1 * v
    star C * C = 1 ∧ C * star C = 1 - r 0 * star (r 0) := by
  intro v C
  let A := finiteCuntzTransfer r a 1
  have hAs : star A = finiteCuntzTransfer a r 1 := by
    simpa only [A, star_one] using finiteCuntzTransfer_star r a 1
  have hAA : A * star A = 1 := by
    have hh := finiteCuntzTransfer_star_mul a r hr 1
    rw [← hAs, star_star] at hh
    simpa only [star_one, one_mul, mul_one, has] using hh
  have hAp : star A * A = ∑ i, r i * star (r i) := by
    simpa only [A, star_one, one_mul, mul_one] using
      finiteCuntzTransfer_star_mul r a ha 1
  have hvv : v * star v = 1 := by
    change ((u : E) * A) * star ((u : E) * A) = 1
    rw [star_mul]
    calc
      _ = (u : E) * (A * star A) * star (u : E) := by noncomm_ring
      _ = 1 := by rw [hAA, mul_one, u.property.2]
  have hvp : star v * v = ∑ i, r i * star (r i) := by
    change star ((u : E) * A) * ((u : E) * A) = _
    rw [star_mul]
    calc
      _ = star A * (star (u : E) * (u : E)) * A := by noncomm_ring
      _ = _ := by rw [u.property.1, mul_one, hAp]
  have hv1 : (star v * v) * r 1 = r 1 := by
    rw [hvp]
    simpa only [finiteRowPermutation, Equiv.Perm.one_apply] using
      finiteRowPermutation_mul_row 1 r (by simp) (by simp) hr 1 1
  obtain ⟨hC, hCC⟩ := coisometry_range_filler v (r 1) hvv
    (by simpa only [ite_true] using hr 1 1) hv1
  refine ⟨hC, ?_⟩
  rw [hCC, hvp, Fin.sum_univ_two]
  abel

end WeakPureInfiniteness

end

end OAI
