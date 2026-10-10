import OAI.Analysis.OInfinity.ZeroUnitComparison

namespace OAI

/-! # Finite proper-row comparison through the zero-unit buffer

Only one unused row element is needed for the finite binary encoding.
The unit and complementary isometries remain explicit throughout.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- The binary encoding construction needs only the tested finite prefix
and its next unused isometry, rather than a countable row extension. -/
lemma exists_finite_zero_unit_binary_encoding (n : ℕ)
    (x : Fin (n + 2) → E)
    (hx : ∀ i j, star (x i) * x j = if i = j then 1 else 0)
    (a b : E) (ha : star a * a = 1) (hb : star b * b = 1)
    (hab : star a * b = 0) (hsum : a * star a + b * star b = 1) :
    ∃ A B : E, star A * A = 1 ∧ star B * B = 1 ∧ star A * B = 0 ∧
      A * star A + B * star B = 1 ∧
      ∀ i : Fin (n + 1), A ^ (i : ℕ) * B = x i.castSucc := by
  have fill (l : ℕ) (hl : l ≤ n + 1) :
      ∃ r : Fin (l + 1) → E,
        (∀ i : Fin l, r i.succ = x ⟨i, by omega⟩) ∧
        (∀ i j, star (r i) * r j = if i = j then 1 else 0) ∧
        (∑ i, r i * star (r i)) = 1 := by
    refine finite_zero_unit_full_row (fun i : Fin l => x ⟨i, by omega⟩)
      (x ⟨l, by omega⟩) a b ?_ ?_ ?_ ha hb hab hsum
    · intro i j
      simpa only [Fin.mk.injEq, Fin.ext_iff] using hx ⟨i, by omega⟩ ⟨j, by omega⟩
    · simpa only [ite_true] using hx ⟨l, by omega⟩ ⟨l, by omega⟩
    · intro i
      have hne : (⟨l, by omega⟩ : Fin (n + 2)) ≠ ⟨i, by omega⟩ := by
        intro h
        have he := congrArg Fin.val h
        change l = (i : ℕ) at he
        have hi := i.isLt
        omega
      simpa only [ite_eq_right hne] using hx ⟨l, by omega⟩ ⟨i, by omega⟩
  obtain ⟨r, hrleaf, hr, hrs⟩ := fill n (by omega)
  obtain ⟨R, hRleaf, hR, hRs⟩ := fill (n + 1) (by omega)
  obtain ⟨A, B, hA, hB, hAB, hsum', hB0, hstep⟩ :=
    successive_full_rows_binary n r R hr hR hrs hRs
  have hencode (i : ℕ) (hi : i ≤ n) : A ^ i * B = x ⟨i, by omega⟩ := by
    induction i with
    | zero => simpa only [pow_zero, one_mul, Fin.val_zero] using hB0.trans (hRleaf 0)
    | succ i ih =>
      rw [pow_succ', mul_assoc, ih (by omega)]
      have h := hstep (⟨i, by omega⟩ : Fin n)
      rw [hrleaf, hRleaf] at h
      exact h
  refine ⟨A, B, hA, hB, hAB, hsum', fun i => ?_⟩
  exact hencode i (by omega)

/-- Finite encoding in an actual projection corner. In particular this
applies to a proper prefix of the finite coisometric vacuum-split row. -/
lemma exists_relative_finite_zero_unit_binary_encoding (n : ℕ)
    (q : E) (hq : star q = q) (hqq : q * q = q)
    (x : Fin (n + 2) → E) (a b : E)
    (hxs : ∀ i, q * x i = x i ∧ x i * q = x i)
    (hx : ∀ i j, star (x i) * x j = if i = j then q else 0)
    (ha : star a * a = q) (hb : star b * b = q) (hab : star a * b = 0)
    (hsum : a * star a + b * star b = q) :
    ∃ A B : E, q * A = A ∧ A * q = A ∧ q * B = B ∧ B * q = B ∧
      star A * A = q ∧ star B * B = q ∧ star A * B = 0 ∧
      A * star A + B * star B = q ∧
      ∀ i : Fin (n + 1), A ^ (i : ℕ) * B = x i.castSucc := by
  obtain ⟨hqa, haq, hqb, hbq⟩ := relativeCuntzPair_support q a b hq hqq ha hb hab hsum
  let x' : Fin (n + 2) → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (x i) (hxs i)
  let a' : ProjectionCorner q hq hqq := projectionCornerElement q hq hqq a ⟨hqa, haq⟩
  let b' : ProjectionCorner q hq hqq := projectionCornerElement q hq hqq b ⟨hqb, hbq⟩
  have hx' : ∀ i j, star (x' i) * x' j = if i = j then 1 else 0 :=
    projectionCornerElement_gram q hq hqq x hxs hx
  obtain ⟨A, B, hA, hB, hAB, hsum', he⟩ := exists_finite_zero_unit_binary_encoding n x' hx'
    a' b' (Subtype.ext ha) (Subtype.ext hb) (Subtype.ext hab) (Subtype.ext hsum)
  refine ⟨A, B, A.property.1, A.property.2, B.property.1, B.property.2,
    congrArg (fun z : ProjectionCorner q hq hqq => (z : E)) hA,
    congrArg (fun z : ProjectionCorner q hq hqq => (z : E)) hB,
    congrArg (fun z : ProjectionCorner q hq hqq => (z : E)) hAB,
    congrArg (fun z : ProjectionCorner q hq hqq => (z : E)) hsum', fun i => ?_⟩
  let f := projectionCornerInclusion q hq hqq
  have hh := congrArg f (he i)
  rw [nonunital_map_pow_mul] at hh
  exact hh

/-- A finite proper row in the buffer commutant has a connected ambient
comparison with the corresponding negative buffer prefix. Its initial unit
is carried to the buffer unit exactly. -/
lemma exists_finite_zeroUnit_buffer_comparison [Nontrivial E]
    (r : ℕ → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (q w z : StarSubalgebra.centralizer ℂ (Set.range r))
    (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (hw : star w * w = 1) (hww : w * star w = 1 - q)
    (hz : star z * z = 1) (hqz : q * z = z)
    (n : ℕ) (x : Fin (n + 2) → StarSubalgebra.centralizer ℂ (Set.range r))
    (hxs : ∀ i, q * x i = x i ∧ x i * q = x i)
    (hx : ∀ i j, star (x i) * x j = if i = j then q else 0)
    (a b : StarSubalgebra.centralizer ℂ (Set.range r))
    (ha : star a * a = q) (hb : star b * b = q) (hab : star a * b = 0)
    (hsum : a * star a + b * star b = q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) * (q : E) * star (u : E) = canonicalTailProjection r 1 ∧
      ∀ i : Fin (n + 1), ‖(u : E) * (x i.castSucc : E) * star (u : E) -
        canonicalNegativeRow r i‖ < ε := by
  let C := StarSubalgebra.centralizer ℂ (Set.range r)
  let : IsClosed (C : Set E) := Set.isClosed_centralizer _
  obtain ⟨A, B, _hAl, _hAr, _hBl, _hBr, hA, hB, hAB, hsum', he⟩ :=
    exists_relative_finite_zero_unit_binary_encoding n q hq hqq x a b hxs hx ha hb hab hsum
  let c : Fin 2 → C := ![A, B]
  have hBA : star B * A = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hAB
  have hc (i j : Fin 2) : star (c i) * c j = if i = j then q else 0 := by
    fin_cases i <;> fin_cases j <;> simp [c, hA, hB, hAB, hBA]
  have hcs : (∑ i, c i * star (c i)) = q := by
    simpa only [Fin.sum_univ_two, c, Matrix.cons_val_zero, Matrix.cons_val_one] using hsum'
  obtain ⟨u, hu, huq, huclose⟩ := exists_zeroUnit_buffer_comparison_with_unit
    r hr q w z hq hqq hq0 hw hww hz hqz c hc hcs n ε hε
  refine ⟨u, hu, huq, fun i => ?_⟩
  have heE : (A : E) ^ (i : ℕ) * (B : E) = (x i.castSucc : E) := by
    have hh := congrArg C.subtype (he i)
    simpa only [map_pow, map_mul, StarSubalgebra.subtype_apply] using hh
  have hh := huclose i (by omega)
  simpa only [c, Matrix.cons_val_zero, Matrix.cons_val_one, heE] using hh

end WeakPureInfiniteness

end

end OAI
