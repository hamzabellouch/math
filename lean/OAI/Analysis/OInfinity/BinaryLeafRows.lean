import OAI.Analysis.OInfinity.ConnectedCocycleGluing
import OAI.Analysis.OInfinity.VacuumSplit

namespace OAI

/-! # The finite prefix rows used in the canonical vacuum split

The finite coisometric rows in the explicit split are prefix words in a
relative binary pair. Binary conjugacy therefore controls them with a
linear word-length loss. The ambient complementary corner remains fixed.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma zeroCornerRow_perturbation (q a b A B : E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hq : ‖q‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hA : ‖A‖ ≤ 1)
    (hAa : ‖a - A‖ ≤ δ) (hBb : ‖b - B‖ ≤ δ) :
    ∀ n i, ‖zeroCornerRow q a b n i - zeroCornerRow q A B n i‖ ≤ n * δ := by
  intro n
  induction n with
  | zero => intro i; simp only [zeroCornerRow, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change ‖b - B‖ ≤ _
      have hn := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hδ
      exact hBb.trans (by push_cast; linarith)
    · change ‖a * zeroCornerRow q a b n j - A * zeroCornerRow q A B n j‖ ≤ _
      have hid : a * zeroCornerRow q a b n j - A * zeroCornerRow q A B n j =
          (a - A) * zeroCornerRow q a b n j +
            A * (zeroCornerRow q a b n j - zeroCornerRow q A B n j) := by noncomm_ring
      rw [hid]
      calc
        _ ≤ ‖(a - A) * zeroCornerRow q a b n j‖ +
            ‖A * (zeroCornerRow q a b n j - zeroCornerRow q A B n j)‖ := norm_add_le _ _
        _ ≤ ‖a - A‖ * ‖zeroCornerRow q a b n j‖ +
            ‖A‖ * ‖zeroCornerRow q a b n j - zeroCornerRow q A B n j‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ δ * 1 + 1 * (n * δ) := add_le_add
          (mul_le_mul hAa (zeroCornerRow_norm_le q a b hq ha hb n j) (norm_nonneg _) hδ)
          (mul_le_mul hA (ih j) (norm_nonneg _) zero_le_one)
        _ = _ := by push_cast; ring

lemma zeroCornerRow_conjugate (u : unitary E) (a b : E) :
    ∀ n i, (u : E) * zeroCornerRow 1 a b n i * star (u : E) =
      zeroCornerRow 1 ((u : E) * a * star (u : E)) ((u : E) * b * star (u : E)) n i := by
  intro n
  induction n with
  | zero => intro i; simp only [zeroCornerRow, mul_one, u.property.2]
  | succ n ih =>
    intro i
    refine Fin.cases rfl (fun j => ?_) i
    change (u : E) * (a * zeroCornerRow 1 a b n j) * star (u : E) =
      ((u : E) * a * star (u : E)) *
        zeroCornerRow 1 ((u : E) * a * star (u : E)) ((u : E) * b * star (u : E)) n j
    rw [← ih j]
    calc
      _ = (u : E) * a * (star (u : E) * (u : E)) *
          zeroCornerRow 1 a b n j * star (u : E) := by rw [u.property.1]; noncomm_ring
      _ = _ := by noncomm_ring

/-- The actual binary theorem controls every finite prefix row, not just
the two generating isometries. -/
lemma exists_connected_binary_leaf_conjugacy [Nontrivial E]
    (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hcomm : bergRowsCommute s t) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧ ∀ i,
      ‖(u : E) * zeroCornerRow 1 (s 0) (s 1) n i * star (u : E) -
        zeroCornerRow 1 (t 0) (t 1) n i‖ < ε := by
  let δ := ε / ((n : ℝ) + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨u, hu, hclose⟩ := exists_connected_binary_row_conjugacy s t hs ht hsum htsum
    hcomm δ hδ
  have hnorm (x : E) (hx : star x * x = 1) : ‖x‖ ≤ 1 := by
    have hh := congrArg norm hx
    rw [CStarRing.norm_star_mul_self, norm_one] at hh
    nlinarith [norm_nonneg x]
  have hsn (i : Fin 2) : ‖s i‖ ≤ 1 := hnorm _ (by simpa using hs i i)
  have htn (i : Fin 2) : ‖t i‖ ≤ 1 := hnorm _ (by simpa using ht i i)
  have hun (i : Fin 2) : ‖(u : E) * s i * star (u : E)‖ ≤ 1 := by
    rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
    change ‖s i * (star u : unitary E)‖ ≤ 1
    rw [CStarRing.norm_mul_coe_unitary]
    exact hsn i
  refine ⟨u, hu, fun i => ?_⟩
  rw [zeroCornerRow_conjugate]
  apply (zeroCornerRow_perturbation 1 _ _ _ _ δ hδ.le (by simp)
    (hun 0) (hun 1) (htn 0) (hclose 0).le (hclose 1).le n i).trans_lt
  have he : ((n : ℝ) + 1) * δ = ε := by
    dsimp only [δ]
    field_simp
  nlinarith

lemma projectionCornerUnitary_conjugate (q : E) (hq : star q = q) (hqq : q * q = q)
    (u : unitary (ProjectionCorner q hq hqq)) (x : ProjectionCorner q hq hqq) :
    (projectionCornerUnitary q hq hqq u : E) * (x : E) *
        star (projectionCornerUnitary q hq hqq u : E) =
      ((u : ProjectionCorner q hq hqq) * x * star (u : ProjectionCorner q hq hqq) :
        ProjectionCorner q hq hqq) := by
  change ((((u : ProjectionCorner q hq hqq) : E) + (1 - q)) * (x : E)) *
      star (((u : ProjectionCorner q hq hqq) : E) + (1 - q)) = _
  rw [add_mul, sub_mul, one_mul, x.property.1, sub_self, add_zero,
    star_add, star_sub, star_one, hq, mul_add, mul_sub, mul_one,
    mul_assoc _ (x : E) q, x.property.2, sub_self, add_zero]
  rfl

lemma projectionCorner_zeroCornerRow (q : E) (hq : star q = q) (hqq : q * q = q)
    (a b : ProjectionCorner q hq hqq) :
    ∀ n i, ((zeroCornerRow 1 a b n i : ProjectionCorner q hq hqq) : E) =
      zeroCornerRow q (a : E) (b : E) n i := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
    intro i
    refine Fin.cases rfl (fun j => ?_) i
    change (a : E) * ((zeroCornerRow 1 a b n j : ProjectionCorner q hq hqq) : E) = _
    rw [ih j]
    rfl

/-- Relative binary rows give finite prefix-row conjugacies inside their
actual shared corner. The complementary identity is retained exactly. -/
lemma exists_relative_binary_leaf_conjugacy
    (q : E) (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q)
    (hcomm : bergRowsCommute s t) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) * (1 - q) = 1 - q ∧ (1 - q) * (u : E) = 1 - q ∧
      ∀ i, ‖(u : E) * zeroCornerRow q (s 0) (s 1) n i * star (u : E) -
        zeroCornerRow q (t 0) (t 1) n i‖ < ε := by
  let : NeZero q := ⟨hq0⟩
  have hsp (i : Fin 2) : q * s i = s i ∧ s i * q = s i :=
    ⟨finiteRow_left_support q s hq hqq hs hsum i,
      finiteRow_right_support q s hq hqq hs i⟩
  have htp (i : Fin 2) : q * t i = t i ∧ t i * q = t i :=
    ⟨finiteRow_left_support q t hq hqq ht htsum i,
      finiteRow_right_support q t hq hqq ht i⟩
  let S : Fin 2 → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (s i) (hsp i)
  let T : Fin 2 → ProjectionCorner q hq hqq := fun i =>
    projectionCornerElement q hq hqq (t i) (htp i)
  have hS := projectionCornerElement_gram q hq hqq s hsp hs
  have hT := projectionCornerElement_gram q hq hqq t htp ht
  have hSs := projectionCornerElement_range_sum q hq hqq s hsp hsum
  have hTs := projectionCornerElement_range_sum q hq hqq t htp htsum
  have hST : bergRowsCommute S T := by
    intro i j
    constructor
    · change S i * T j = T j * S i
      apply Subtype.ext
      exact (hcomm i j).1.eq
    · change S i * star (T j) = star (T j) * S i
      apply Subtype.ext
      exact (hcomm i j).2.eq
  obtain ⟨v, hv, hclose⟩ := exists_connected_binary_leaf_conjugacy S T hS hT hSs hTs hST n ε hε
  let u := projectionCornerUnitary q hq hqq v
  have hu : Joined (1 : unitary E) u := by
    simpa only [projectionCornerUnitary_one] using
      hv.map (projectionCornerUnitary_continuous q hq hqq)
  refine ⟨u, hu, (projectionCornerUnitary_complement q hq hqq v).1,
    (projectionCornerUnitary_complement q hq hqq v).2, fun i => ?_⟩
  have hc := hclose i
  change ‖(((v : ProjectionCorner q hq hqq) * zeroCornerRow 1 (S 0) (S 1) n i *
    star (v : ProjectionCorner q hq hqq) : ProjectionCorner q hq hqq) : E) -
    ((zeroCornerRow 1 (T 0) (T 1) n i : ProjectionCorner q hq hqq) : E)‖ < ε at hc
  rw [← projectionCornerUnitary_conjugate, projectionCorner_zeroCornerRow,
    projectionCorner_zeroCornerRow] at hc
  exact hc

end WeakPureInfiniteness

end

end OAI
