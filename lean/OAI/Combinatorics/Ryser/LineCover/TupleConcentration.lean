import OAI.Combinatorics.Ryser.LineCover.Definitions
import OAI.Combinatorics.Ryser.LineCover.CountConcentration
import Mathlib.Tactic.Positivity

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

def countTailConstant (D H : ℕ) (δ : ℝ) : ℝ :=
  min (δ ^ 2 / (16 * (D : ℝ) ^ 2 * ((D : ℝ) * (H : ℝ)) ^ 2))
    (δ / (16 * ((D : ℝ) * (H : ℝ))))

def tupleTailConstant (D h : ℕ) (δ : ℝ) : ℝ :=
  countTailConstant D (2 * D * h) δ

theorem countTailConstant_pos {D H : ℕ} {δ : ℝ}
    (hD : 0 < D) (hH : 0 < H) (hδ : 0 < δ) :
    0 < countTailConstant D H δ := by
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  unfold countTailConstant
  apply lt_min <;> positivity

theorem tupleTailConstant_pos {D h : ℕ} {δ : ℝ}
    (hD : 0 < D) (hh : 0 < h) (hδ : 0 < δ) :
    0 < tupleTailConstant D h δ :=
  countTailConstant_pos hD
    (Nat.mul_pos (Nat.mul_pos (by decide) hD) hh) hδ

private theorem variance_budget_real (n D q C t : ℝ)
    (hD : 0 ≤ D) (hq : 0 < q) (hn : n ≤ D * q) :
    n * C ^ 2 * (t ^ 2 * (D / q)) ≤ D ^ 2 * C ^ 2 * t ^ 2 := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hscale : 0 ≤ C ^ 2 * (t ^ 2 * (D / q)) :=
    mul_nonneg (sq_nonneg C)
      (mul_nonneg (sq_nonneg t) (div_nonneg hD (le_of_lt hq)))
  calc
    n * C ^ 2 * (t ^ 2 * (D / q)) =
        n * (C ^ 2 * (t ^ 2 * (D / q))) := by ring
    _ ≤ (D * q) * (C ^ 2 * (t ^ 2 * (D / q))) :=
      mul_le_mul_of_nonneg_right hn hscale
    _ = D ^ 2 * C ^ 2 * t ^ 2 := by
      field_simp [hq0]

private theorem tail_exponent_identity (D C T δ : ℝ)
    (hD : 0 < D) (hC : 0 < C) (hT : 0 < T) :
    -(1 / 4 : ℝ) *
        min (((δ * T ^ 2 / 2) ^ 2) / (D ^ 2 * C ^ 2 * T ^ 2))
          ((δ * T ^ 2 / 2) / (2 * C)) =
      -(min (δ ^ 2 / (16 * D ^ 2 * C ^ 2))
          (δ / (16 * C))) * T ^ 2 := by
  let a : ℝ := δ ^ 2 / (16 * D ^ 2 * C ^ 2)
  let b : ℝ := δ / (16 * C)
  have hA :
      ((δ * T ^ 2 / 2) ^ 2) / (D ^ 2 * C ^ 2 * T ^ 2) =
        4 * a * T ^ 2 := by
    dsimp [a]
    field_simp [ne_of_gt hD, ne_of_gt hC, ne_of_gt hT]; ring
  have hB : (δ * T ^ 2 / 2) / (2 * C) = 4 * b * T ^ 2 := by
    dsimp [b]
    field_simp [ne_of_gt hC]; ring
  change -(1 / 4 : ℝ) * min _ _ = -(min a b) * T ^ 2
  rw [hA, hB]
  rcases le_total a b with h | h
  · have hs : 4 * a * T ^ 2 ≤ 4 * b * T ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4))
        (sq_nonneg T)
    rw [min_eq_left hs, min_eq_left h]
    ring
  · have hs : 4 * b * T ^ 2 ≤ 4 * a * T ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4))
        (sq_nonneg T)
    rw [min_eq_right hs, min_eq_right h]
    ring

section General

variable {P : Type*} [Fintype P] [DecidableEq P]
  {shapes : Finset (Finset P)} {D n : ℕ}

theorem retainedCount_square_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (ignore : Finset (Finset P)) (test : Finset P) (H q t : ℕ) (δ : ℝ)
    (hD : 0 < D) (hH : 0 < H) (hq : 0 < q) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * q) (hcard : test.card = t * t)
    (hshape : ∀ L ∈ shapes, L ∉ ignore → (L ∩ test).card ≤ H)
    (hpoint : ∀ i x, x ∈ test →
      (μ i).prob (fun a => x ∈ deleted ∅ a) ≤ (D : ℝ) / (q : ℝ))
    (hbase : ∀ x ∈ test,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob
        (fun ω => retainedCount ignore test ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * Real.exp (-(countTailConstant D H δ) * (t : ℝ) ^ 2) := by
  let C : ℝ := (D : ℝ) * (H : ℝ)
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have htr : 0 < (t : ℝ) := by exact_mod_cast ht
  have hC : 0 < C := mul_pos hDr hHr
  have hnr : (n : ℝ) ≤ (D : ℝ) * (q : ℝ) := by exact_mod_cast hn
  have hcardReal : (test.card : ℝ) = (t : ℝ) ^ 2 := by
    rw [hcard, Nat.cast_mul, pow_two]
  have hpointIgnore : ∀ i x, x ∈ test →
      (μ i).prob (fun a => x ∈ deleted ignore a) ≤ (D : ℝ) / (q : ℝ) := by
    intro i x hx
    calc
      _ ≤ (μ i).prob (fun a => x ∈ deleted ∅ a) := by
        apply (μ i).prob_mono
        intro a hxa
        rcases mem_deleted.mp hxa with ⟨L, hL, hnot, hxL⟩
        exact mem_deleted.mpr ⟨L, hL, by simp, hxL⟩
      _ ≤ _ := hpoint i x hx
  have hCV : (n : ℝ) * C ^ 2 * ((test.card : ℝ) * ((D : ℝ) / (q : ℝ))) ≤
      (D : ℝ) ^ 2 * C ^ 2 * (t : ℝ) ^ 2 := by
    rw [hcardReal]
    exact variance_budget_real (n : ℝ) (D : ℝ) (q : ℝ) C (t : ℝ)
      hDr.le hqr hnr
  have hmean0 := expectation_retainedCount_ge_of_base_survival μ ignore test δ hbase
  rw [hcardReal] at hmean0
  have hmean : 2 * (δ * (t : ℝ) ^ 2 / 2) ≤
      (FiniteLaw.pi μ).expectation (retainedCount ignore test) := by
    calc
      _ = δ * (t : ℝ) ^ 2 := by ring
      _ ≤ _ := hmean0
  have htail := retainedCount_rare_lower_tail μ ignore test H hshape
    ((D : ℝ) / (q : ℝ)) hpointIgnore
    (2 * C) ((D : ℝ) ^ 2 * C ^ 2 * (t : ℝ) ^ 2)
    (δ * (t : ℝ) ^ 2 / 2)
    (by positivity) (by positivity) (by positivity)
    (le_of_eq (by dsimp [C]; ring)) hCV hmean
  apply htail.trans_eq
  apply congrArg (fun z : ℝ => 2 * Real.exp z)
  simpa only [countTailConstant, C] using
    tail_exponent_identity (D : ℝ) C (t : ℝ) δ hDr hC htr

end General

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n h t : ℕ}

theorem admissibleTuple_lower_tail
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (a : LineTuple F t) (ha : AdmissibleTuple shapes D h a)
    (δ : ℝ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * Fintype.card F)
    (hpoint : ∀ i x,
      (μ i).prob (fun b => x ∈ deleted ∅ b) ≤ (D : ℝ) / (Fintype.card F : ℝ))
    (hbase : ∀ x,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob (fun ω =>
        retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  have hH : 0 < 2 * D * h := Nat.mul_pos (Nat.mul_pos (by decide) hD) hh
  have hq : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
  simpa only [tupleTailConstant] using retainedCount_square_lower_tail
    μ (tupleShapes a) (crossPoints a) (2 * D * h) (Fintype.card F) t δ
    hD hH hq ht hδ hn ha.2.1 ha.2.2
    (fun i x _ => hpoint i x) (fun x _ => hbase x)

theorem prob_exists_admissibleTuple_bad_le
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (δ : ℝ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * Fintype.card F)
    (hpoint : ∀ i x,
      (μ i).prob (fun b => x ∈ deleted ∅ b) ≤ (D : ℝ) / (Fintype.card F : ℝ))
    (hbase : ∀ x,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * (Fintype.card (LineTuple F t) : ℝ) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  classical
  calc
    _ ≤ ∑ a : LineTuple F t, (FiniteLaw.pi μ).prob (fun ω =>
        AdmissibleTuple shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) :=
      (FiniteLaw.pi μ).prob_exists_le _
    _ ≤ ∑ _a : LineTuple F t,
        2 * Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : AdmissibleTuple shapes D h a
      · calc
          _ ≤ (FiniteLaw.pi μ).prob (fun ω =>
              retainedCount (tupleShapes a) (crossPoints a) ω <
                δ * (t : ℝ) ^ 2 / 2) := by
            apply (FiniteLaw.pi μ).prob_mono
            intro ω hω
            exact hω.2
          _ ≤ _ := admissibleTuple_lower_tail μ a ha δ hD hh ht hδ hn hpoint hbase
      · simp only [ha, false_and, FiniteLaw.prob_false]
        positivity
    _ = _ := by simp [mul_assoc, mul_comm]

theorem card_lineTuple_le (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (t : ℕ) :
    Fintype.card (LineTuple F t) ≤
      (Fintype.card F * (Fintype.card F + 1)) ^ (2 * t) := by
  classical
  calc
    Fintype.card (LineTuple F t) ≤
        Fintype.card ((Fin t ⊕ Fin t) → AffineLine F) :=
      Fintype.card_le_of_injective
        (fun a : LineTuple F t =>
          (a : (Fin t ⊕ Fin t) → AffineLine F))
        Function.Embedding.coe_injective
    _ = _ := by
      rw [Fintype.card_fun]
      simp [AffineLine, Direction, two_mul, Nat.mul_comm]

theorem prob_exists_admissibleTuple_bad_le_card_bound
    (μ : Fin n → FiniteLaw (Outcome shapes D))
    (δ : ℝ) (hD : 0 < D) (hh : 0 < h) (ht : 0 < t) (hδ : 0 < δ)
    (hn : n ≤ D * Fintype.card F)
    (hpoint : ∀ i x,
      (μ i).prob (fun b => x ∈ deleted ∅ b) ≤ (D : ℝ) / (Fintype.card F : ℝ))
    (hbase : ∀ x,
      δ ≤ (FiniteLaw.pi μ).prob (fun ω => x ∈ survivors ∅ ω)) :
    (FiniteLaw.pi μ).prob (fun ω => ∃ a : LineTuple F t,
        AdmissibleTuple shapes D h a ∧
          retainedCount (tupleShapes a) (crossPoints a) ω < δ * (t : ℝ) ^ 2 / 2) ≤
      2 * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ^ (2 * t) *
        Real.exp (-(tupleTailConstant D h δ) * (t : ℝ) ^ 2) := by
  have hcard : (Fintype.card (LineTuple F t) : ℝ) ≤
      ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ^ (2 * t) := by
    exact_mod_cast card_lineTuple_le F t
  apply (prob_exists_admissibleTuple_bad_le μ δ hD hh ht hδ hn hpoint hbase).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 2))
    (Real.exp_pos _).le

end RyserCoveringCounterexample.LineCover

end

end OAI
