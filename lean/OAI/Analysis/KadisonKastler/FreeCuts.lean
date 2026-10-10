import OAI.Analysis.KadisonKastler.FreeWordConstants

namespace OAI

/-!
# Creation, preservation, and annihilation cuts

The algebraic relations record the first-copy restrictions of the Fock
operators. They imply an exact cut decomposition for words in distinct
copy positions. The norm estimate is then a finite recurrence.
-/

namespace KadisonKastler

noncomputable section

section Algebra

variable {ι B : Type*} [Semiring B]

def annihilationProduct (A : ι → B) (l : List ι) : B := (l.map A).prod

def centeredLetterProduct (C D A : ι → B) (l : List ι) : B :=
  (l.map (fun i => C i + D i + A i)).prod

def freeCutSum (C D A : ι → B) : List ι → B
  | [] => 1
  | i :: l => C i * freeCutSum C D A l +
      D i * annihilationProduct A l + A i * annihilationProduct A l

/-- An annihilation or preservation operator from a different copy kills
the creation and preservation terms of the first tail letter. -/
theorem mul_freeCutSum_eq_mul_annihilationProduct (C D A : ι → B) (x : B) (l : List ι)
    (hC : ∀ i ∈ l, x * C i = 0) (hD : ∀ i ∈ l, x * D i = 0) :
    x * freeCutSum C D A l = x * annihilationProduct A l := by
  cases l with
  | nil => rfl
  | cons i l =>
    simp only [freeCutSum, annihilationProduct, List.map_cons, List.prod_cons,
      mul_add, ← mul_assoc, hC i (List.mem_cons_self), hD i (List.mem_cons_self),
      zero_mul, zero_add]

/-- The centered word is exactly the sum of its creation/annihilation
cuts and its cuts with one preservation. -/
theorem centeredLetterProduct_eq_freeCutSum (C D A : ι → B)
    (hAC : ∀ i j, i ≠ j → A i * C j = 0)
    (hAD : ∀ i j, i ≠ j → A i * D j = 0)
    (hDC : ∀ i j, i ≠ j → D i * C j = 0)
    (hDD : ∀ i j, i ≠ j → D i * D j = 0)
    (l : List ι) (hl : l.Nodup) :
    centeredLetterProduct C D A l = freeCutSum C D A l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
    have hij : ∀ j ∈ l, i ≠ j := by
      intro j hj h
      subst j
      exact hi hj
    have hD := mul_freeCutSum_eq_mul_annihilationProduct C D A (D i) l
      (fun j hj => hDC i j (hij j hj)) (fun j hj => hDD i j (hij j hj))
    have hA := mul_freeCutSum_eq_mul_annihilationProduct C D A (A i) l
      (fun j hj => hAC i j (hij j hj)) (fun j hj => hAD i j (hij j hj))
    change (C i + D i + A i) * centeredLetterProduct C D A l = _
    rw [ih hl, add_mul, add_mul, hD, hA]
    rfl

end Algebra

section Norm

variable {ι B : Type*} [NormedRing B]

theorem norm_annihilationProduct_le (A : ι → B) {t : ℝ} (ht : 0 ≤ t)
    (hone : ‖(1 : B)‖ ≤ 1) (hA : ∀ i, ‖A i‖ ≤ t) (l : List ι) :
    ‖annihilationProduct A l‖ ≤ t ^ l.length := by
  induction l with
  | nil => simpa only [annihilationProduct, List.map_nil, List.prod_nil, List.length_nil,
      pow_zero] using hone
  | cons i l ih =>
    change ‖A i * annihilationProduct A l‖ ≤ t ^ (l.length + 1)
    calc
      _ ≤ ‖A i‖ * ‖annihilationProduct A l‖ := norm_mul_le _ _
      _ ≤ t * t ^ l.length := mul_le_mul (hA i) ih (norm_nonneg _) ht
      _ = _ := by rw [pow_succ']

/-- The cut recurrence has `n` preservation terms and `n+1` terms without
preservation. Its bound includes the empty word. -/
theorem norm_freeCutSum_le (C D A : ι → B) {t : ℝ} (ht : 0 ≤ t)
    (hone : ‖(1 : B)‖ ≤ 1) (hC : ∀ i, ‖C i‖ ≤ t)
    (hD : ∀ i, ‖D i‖ ≤ 1) (hA : ∀ i, ‖A i‖ ≤ t) (l : List ι) :
    ‖freeCutSum C D A l‖ ≤
      (l.length : ℝ) * t ^ (l.length - 1) + (l.length + 1 : ℝ) * t ^ l.length := by
  induction l with
  | nil => simpa only [freeCutSum, List.length_nil, Nat.cast_zero, zero_mul, zero_add,
      pow_zero, one_mul] using hone
  | cons i l ih =>
    have hp := norm_annihilationProduct_le A ht hone hA l
    have hc : ‖C i * freeCutSum C D A l‖ ≤
        t * ((l.length : ℝ) * t ^ (l.length - 1) + (l.length + 1 : ℝ) * t ^ l.length) :=
      (norm_mul_le _ _).trans (mul_le_mul (hC i) ih (norm_nonneg _) ht)
    have hd : ‖D i * annihilationProduct A l‖ ≤ t ^ l.length := by
      exact (norm_mul_le _ _).trans (by
        simpa only [one_mul] using mul_le_mul (hD i) hp (norm_nonneg _) zero_le_one)
    have ha : ‖A i * annihilationProduct A l‖ ≤ t * t ^ l.length :=
      (norm_mul_le _ _).trans (mul_le_mul (hA i) hp (norm_nonneg _) ht)
    have htriangle := (norm_add_le (C i * freeCutSum C D A l + D i * annihilationProduct A l)
      (A i * annihilationProduct A l)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    change ‖C i * freeCutSum C D A l + D i * annihilationProduct A l +
      A i * annihilationProduct A l‖ ≤ _
    calc
      _ ≤ t * ((l.length : ℝ) * t ^ (l.length - 1) +
          (l.length + 1 : ℝ) * t ^ l.length) + t ^ l.length + t * t ^ l.length :=
        htriangle.trans (add_le_add (add_le_add hc hd) ha)
      _ = _ := by
        cases hlen : l.length with
        | zero => simp only [List.length_cons, hlen, Nat.cast_zero, Nat.cast_one,
            Nat.cast_add, Nat.zero_sub, pow_zero]; ring
        | succ n => simp only [List.length_cons, hlen,
            Nat.succ_sub_one, Nat.cast_succ, pow_succ]; ring

/-- The single-centered-word bound from the actual algebraic cut
decomposition, conditional only on its four explicit zero-product
relations and the individual letter bounds. -/
theorem norm_centeredLetterProduct_le (C D A : ι → B)
    (hAC : ∀ i j, i ≠ j → A i * C j = 0)
    (hAD : ∀ i j, i ≠ j → A i * D j = 0)
    (hDC : ∀ i j, i ≠ j → D i * C j = 0)
    (hDD : ∀ i j, i ≠ j → D i * D j = 0)
    {t : ℝ} (ht : 0 ≤ t) (hone : ‖(1 : B)‖ ≤ 1)
    (hC : ∀ i, ‖C i‖ ≤ t) (hD : ∀ i, ‖D i‖ ≤ 1) (hA : ∀ i, ‖A i‖ ≤ t)
    (l : List ι) (hl : l.Nodup) :
    ‖centeredLetterProduct C D A l‖ ≤
      (l.length : ℝ) * t ^ (l.length - 1) + (l.length + 1 : ℝ) * t ^ l.length := by
  rw [centeredLetterProduct_eq_freeCutSum C D A hAC hAD hDC hDD l hl]
  exact norm_freeCutSum_le C D A ht hone hC hD hA l

theorem sqrt_nat_pow {d : ℝ} (hd : 0 ≤ d) (n : ℕ) :
    Real.sqrt (d ^ n) = Real.sqrt d ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hd _), ih, pow_succ]

/-- The preceding actual cut decomposition gives the single-word
estimate used in the scalar-restoration calculation. -/
theorem norm_centeredLetterProduct_le_inv_sqrt (C D A : ι → B)
    (hAC : ∀ i j, i ≠ j → A i * C j = 0)
    (hAD : ∀ i j, i ≠ j → A i * D j = 0)
    (hDC : ∀ i j, i ≠ j → D i * C j = 0)
    (hDD : ∀ i j, i ≠ j → D i * D j = 0)
    {d : ℝ} (hd : 1 ≤ d) (hone : ‖(1 : B)‖ ≤ 1)
    (hC : ∀ i, ‖C i‖ ≤ (Real.sqrt d)⁻¹)
    (hD : ∀ i, ‖D i‖ ≤ 1)
    (hA : ∀ i, ‖A i‖ ≤ (Real.sqrt d)⁻¹)
    (l : List ι) (hl : l.Nodup) :
    ‖centeredLetterProduct C D A l‖ ≤
      (2 * l.length + 1 : ℝ) / Real.sqrt (d ^ (l.length - 1)) := by
  have ht : 0 ≤ (Real.sqrt d)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg d)
  have h := norm_centeredLetterProduct_le C D A hAC hAD hDC hDD ht hone hC hD hA l hl
  apply single_centered_word_constant hd l.length
  simpa only [inv_pow, ← sqrt_nat_pow (zero_le_one.trans hd), div_eq_mul_inv] using h

end Norm

end

end KadisonKastler

end OAI
