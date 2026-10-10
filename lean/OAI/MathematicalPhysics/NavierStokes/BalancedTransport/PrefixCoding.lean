import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RecorderRules

namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*}

namespace Exec

variable {M : Machine Q Γ}

theorem single {source target : Configuration Q Γ} (step : Step M source target) :
    Exec M 1 source target :=
  .cons step (.refl target)

theorem trans {firstLength secondLength : ℕ} {source middle target : Configuration Q Γ}
    (first : Exec M firstLength source middle) (second : Exec M secondLength middle target) :
    Exec M (firstLength + secondLength) source target := by
  induction first with
  | refl => simpa using second
  | cons step _ inductionHypothesis =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Exec.cons step (inductionHypothesis second))

end Exec

variable (M : Machine Q Γ)
open Letter Control

theorem preparation (q : Q) (hq : q ≠ M.halt) (a : Γ) (w : List Γ)
    (L B J : Stream' (Letter Q Γ)) :
    Exec M (2 * w.length + 3)
      ⟨ready q, L, work a :: (w.map work ++ₛ (boundary :: work M.blank :: B)), J⟩
      ⟨execute q, L, work a :: (w.map work ++ₛ (boundary :: B)), work M.blank :: J⟩ := by
  have h₁ := row_step M (.enter q a) hq
    ⟨L, w.map work ++ₛ (boundary :: work M.blank :: B), J⟩
  have h₂ := outward_scan M q hq w (marked a :: L) (boundary :: work M.blank :: B) J
  have h₃ := row_step M (.supply q) hq
    ⟨w.reverse.map work ++ₛ (marked a :: L), B, J⟩
  have h₄ := returning_scan M q hq w.reverse (marked a :: L)
    (boundary :: B) (work M.blank :: J)
  have h₅ := row_step M (.restore q a) hq
    ⟨L, w.map work ++ₛ (boundary :: B), work M.blank :: J⟩
  simp only [List.reverse_reverse, List.length_reverse] at h₄
  have h₁' := Exec.single h₁
  have h₃' := Exec.single h₃
  have h₅' := Exec.single h₅
  simp only [Row.instruction, Instruction.source, Instruction.target,
    Stream'.appendStream'] at h₁' h₃' h₅'
  have hh := (((h₁'.trans h₂).trans h₃').trans h₄).trans h₅'
  convert hh using 1
  omega

theorem preparation_blank_tail (q : Q) (hq : q ≠ M.halt) (a : Γ) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) :
    Exec M (2 * w.length + 3)
      ⟨ready q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩
      ⟨execute q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        work M.blank :: J⟩ := by
  have hh := preparation M q hq a w L (Stream'.const (work M.blank)) J
  have hb : (work M.blank :: Stream'.const (work M.blank) : Stream' (Letter Q Γ)) =
      Stream'.const (work M.blank) := by
    ext n
    cases n <;> rfl
  simpa only [hb] using hh

theorem checkpoint_length (q : Q) (hq : q ≠ M.halt) (a : Γ) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) (d : Configuration Q Γ)
    (hd : Step M
      ⟨execute q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        work M.blank :: J⟩ d) :
    Exec M (2 * (w.length + 1) + 2)
      ⟨ready q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩ d := by
  have hh := (preparation_blank_tail M q hq a w L J).trans (Exec.single hd)
  convert hh using 1

theorem checkpoint_stay (q : Q) (hq : q ≠ M.halt) (a : Γ)
    (hm : (M.transition q a).move = .stay) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) :
    Exec M (2 * (w.length + 1) + 2)
      ⟨ready q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩
      ⟨ready (M.transition q a).state, L,
        work (M.transition q a).write ::
          (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        record (.stay q a) :: J⟩ := by
  apply checkpoint_length M q hq a w L J
  exact row_step M (.stay q a) ⟨hq, hm⟩
    ⟨L, w.map work ++ₛ (boundary :: Stream'.const (work M.blank)), J⟩

theorem checkpoint_left (q : Q) (hq : q ≠ M.halt) (a c : Γ)
    (hm : (M.transition q a).move = .left) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) :
    Exec M (2 * (w.length + 1) + 2)
      ⟨ready q, work c :: L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩
      ⟨ready (M.transition q a).state, L,
        work c :: work (M.transition q a).write ::
          (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        record (.left q a c) :: J⟩ := by
  apply checkpoint_length M q hq a w (work c :: L) J
  exact row_step M (.left q a c) ⟨hq, hm⟩
    ⟨L, w.map work ++ₛ (boundary :: Stream'.const (work M.blank)), J⟩

theorem checkpoint_right (q : Q) (hq : q ≠ M.halt) (a c : Γ)
    (hm : (M.transition q a).move = .right) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) :
    Exec M (2 * (w.length + 2) + 2)
      ⟨ready q, L,
        work a :: work c :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩
      ⟨ready (M.transition q a).state, work (M.transition q a).write :: L,
        work c :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        record (.right q a c) :: J⟩ := by
  have hh := checkpoint_length M q hq a (c :: w) L J _
    (row_step M (.right q a c) ⟨hq, hm⟩
      ⟨L, w.map work ++ₛ (boundary :: Stream'.const (work M.blank)), J⟩)
  simpa [Nat.add_assoc, Row.instruction, Instruction.target, Stream'.appendStream'] using hh

theorem checkpoint_extend (q : Q) (hq : q ≠ M.halt) (a : Γ)
    (hm : (M.transition q a).move = .right) (L J : Stream' (Letter Q Γ)) :
    Exec M 4
      ⟨ready q, L, work a :: boundary :: Stream'.const (work M.blank), J⟩
      ⟨ready (M.transition q a).state, work (M.transition q a).write :: L,
        work M.blank :: boundary :: Stream'.const (work M.blank),
        record (.extend q a) :: J⟩ := by
  apply checkpoint_length M q hq a [] L J
  have hh := row_step M (.extend q a) ⟨hq, hm⟩
    ⟨L, Stream'.const (work M.blank), J⟩
  have hb : (work M.blank :: Stream'.const (work M.blank) : Stream' (Letter Q Γ)) =
      Stream'.const (work M.blank) := by
    ext n
    cases n <;> rfl
  simpa [Row.instruction, Instruction.source, Instruction.target,
    Stream'.appendStream', hb] using hh

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

def word (r : ℝ) (digit : S → ℝ) : List S → ℝ
  | [] => 0
  | a :: w => r * (digit a + word r digit w)

def prefixPoint (r : ℝ) (digit : S → ℝ) (w : List S) (z : ℝ) : ℝ :=
  word r digit w + r ^ w.length * z

def interval (r : ℝ) (digit : S → ℝ) (w : List S) : Set ℝ :=
  Set.Icc (word r digit w) (word r digit w + r ^ w.length)

@[simp] theorem word_nil (r : ℝ) (digit : S → ℝ) : word r digit [] = 0 := rfl

@[simp] theorem prefix_nil (r : ℝ) (digit : S → ℝ) (z : ℝ) :
    prefixPoint r digit [] z = z := by simp [prefixPoint]

@[simp] theorem prefix_cons (r : ℝ) (digit : S → ℝ) (a : S)
    (w : List S) (z : ℝ) :
    prefixPoint r digit (a :: w) z = r * (digit a + prefixPoint r digit w z) := by
  simp only [prefixPoint, word, List.length_cons, pow_succ]
  ring

theorem word_append (r : ℝ) (digit : S → ℝ) (u v : List S) :
    word r digit (u ++ v) = word r digit u + r ^ u.length * word r digit v := by
  induction u with
  | nil => simp
  | cons a u ih =>
      simp only [List.cons_append, word, List.length_cons, pow_succ, ih]
      ring

theorem prefix_append (r : ℝ) (digit : S → ℝ) (u v : List S) (z : ℝ) :
    prefixPoint r digit (u ++ v) z = prefixPoint r digit u (prefixPoint r digit v z) := by
  simp only [prefixPoint, word_append, List.length_append, pow_add]
  ring

theorem prefix_mem_interval {r : ℝ} (hr : 0 ≤ r) (digit : S → ℝ)
    (w : List S) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    prefixPoint r digit w z ∈ interval r digit w := by
  have hpow := pow_nonneg hr w.length
  dsimp [prefixPoint, interval]
  constructor
  · linarith [mul_nonneg hpow hz.1]
  · nlinarith [hz.2]

theorem interval_eq_image {r : ℝ} (hr : 0 < r) (digit : S → ℝ) (w : List S) :
    interval r digit w = prefixPoint r digit w '' Set.Icc (0 : ℝ) 1 := by
  ext y
  constructor
  · intro hy
    have hp : 0 < r ^ w.length := pow_pos hr _
    refine ⟨(y - word r digit w) / r ^ w.length, ?_, ?_⟩
    · constructor
      · exact div_nonneg (sub_nonneg.mpr hy.1) hp.le
      · apply (div_le_one hp).mpr
        exact sub_le_iff_le_add.mpr (by simpa [add_comm] using hy.2)
    · dsimp [prefixPoint]
      field_simp
      ring
  · rintro ⟨z, hz, rfl⟩
    exact prefix_mem_interval hr.le digit w hz

def replacement (r : ℝ) (digit : S → ℝ) (u v : List S) (x : ℝ) : ℝ :=
  word r digit v + (r ^ v.length / r ^ u.length) * (x - word r digit u)

theorem replacement_prefix {r : ℝ} (hr : r ≠ 0) (digit : S → ℝ)
    (u v : List S) (z : ℝ) :
    replacement r digit u v (prefixPoint r digit u z) = prefixPoint r digit v z := by
  dsimp [replacement, prefixPoint]
  field_simp
  ring

theorem replacement_interval {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (u v : List S) :
    replacement r digit u v '' interval r digit u = interval r digit v := by
  rw [interval_eq_image hr digit u, interval_eq_image hr digit v, Set.image_image]
  congr 1
  funext z
  exact replacement_prefix hr.ne' digit u v z

def scales (r : ℝ) (u v : Fin 3 → List S) : Fin 3 → ℝ :=
  fun i => r ^ (v i).length / r ^ (u i).length

theorem determinant_one {r : ℝ} (hr : r ≠ 0) (u v : Fin 3 → List S)
    (h : ∑ i, (u i).length = ∑ i, (v i).length) :
    Matrix.det (Matrix.diagonal (scales r u v)) = 1 := by
  rw [Matrix.det_diagonal]
  simp only [scales, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rw [h]
  exact div_self (pow_ne_zero _ hr)

theorem scales_positive {r : ℝ} (hr : 0 < r) (u v : Fin 3 → List S) (i : Fin 3) :
    0 < scales r u v i := div_pos (pow_pos hr _) (pow_pos hr _)

def stream {B : ℕ} (digit : S → Fin B) (s : Stream' S) : ℝ :=
  Real.ofDigits (fun n => digit (s n))

theorem stream_mem_unit {B : ℕ} (digit : S → Fin B) (s : Stream' S) :
    stream digit s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem stream_cons {B : ℕ} (digit : S → Fin B) (a : S) (s : Stream' S) :
    stream digit (a :: s) = (B : ℝ)⁻¹ * ((digit a : ℝ) + stream digit s) := by
  have hh := Real.ofDigits_eq_sum_add_ofDigits (fun n => digit ((a :: s) n)) 1
  simpa [stream, Real.ofDigitsTerm, Stream'.cons, mul_add, mul_comm] using hh

theorem stream_append {B : ℕ} (digit : S → Fin B) (w : List S) (s : Stream' S) :
    stream digit (w ++ₛ s) =
      prefixPoint (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) w (stream digit s) := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [Stream'.appendStream', stream_cons, ih, prefix_cons]

theorem stream_append_mem_interval {B : ℕ} (digit : S → Fin B)
    (w : List S) (s : Stream' S) :
    stream digit (w ++ₛ s) ∈ interval (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) w := by
  rw [stream_append]
  exact prefix_mem_interval (inv_nonneg.mpr (Nat.cast_nonneg _)) _ _ (stream_mem_unit _ _)

theorem replacement_stream {B : ℕ} (hB : B ≠ 0) (digit : S → Fin B)
    (u v : List S) (s : Stream' S) :
    replacement (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) u v (stream digit (u ++ₛ s)) =
      stream digit (v ++ₛ s) := by
  rw [stream_append, stream_append]
  exact replacement_prefix (inv_ne_zero (Nat.cast_ne_zero.mpr hB)) _ _ _ _

theorem stream_mem_interior {B : ℕ} (hB : 0 < B) (digit : S → Fin B)
    (hlo : ∀ a, 0 < (digit a : ℝ)) (hhi : ∀ a, (digit a : ℝ) + 1 < B)
    (s : Stream' S) : stream digit s ∈ Set.Ioo (0 : ℝ) 1 := by
  have hb : 0 < (B : ℝ) := Nat.cast_pos.mpr hB
  have hs : s = s.head :: s.tail := by
    funext n
    cases n <;> rfl
  rw [hs, stream_cons]
  have htail := stream_mem_unit digit s.tail
  constructor
  · exact mul_pos (inv_pos.mpr hb) (by linarith [hlo s.head, htail.1])
  · rw [mul_comm, ← div_eq_mul_inv]
    apply (div_lt_one hb).mpr
    linarith [hhi s.head, htail.2]

theorem prefix_mem_unit {r : ℝ} (hr : 0 ≤ r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (w : List S) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    prefixPoint r digit w z ∈ Set.Icc (0 : ℝ) 1 := by
  induction w with
  | nil => simpa using hz
  | cons a w ih =>
      rw [prefix_cons]
      exact ⟨mul_nonneg hr (add_nonneg (hd₀ a) ih.1),
        (mul_le_mul_of_nonneg_left (show digit a + prefixPoint r digit w z ≤
          digit a + 1 by linarith [ih.2]) hr).trans (hd₁ a)⟩

theorem interval_subset_unit {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (w : List S) : interval r digit w ⊆ Set.Icc (0 : ℝ) 1 := by
  rw [interval_eq_image hr]
  rintro _ ⟨z, hz, rfl⟩
  exact prefix_mem_unit hr.le digit hd₀ hd₁ w hz

theorem prefix_gap {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (p u v : List S) (a b : S) {x y : ℝ}
    (hx : x ∈ interval r digit (p ++ a :: u))
    (hy : y ∈ interval r digit (p ++ b :: v)) :
    r ^ (p.length + 1) * (digit b - digit a - 1) ≤ y - x := by
  rw [interval_eq_image hr] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  have hs' := prefix_mem_unit hr.le digit hd₀ hd₁ u hs
  have ht' := prefix_mem_unit hr.le digit hd₀ hd₁ v ht
  rw [prefix_append, prefix_append, prefix_cons, prefix_cons]
  dsimp [prefixPoint]
  have hn : 0 ≤ r ^ p.length * r := mul_nonneg (pow_nonneg hr.le _) hr.le
  have hh : 0 ≤ r ^ p.length * r *
      (prefixPoint r digit v t - prefixPoint r digit u s + 1) :=
    mul_nonneg hn (by linarith [hs'.2, ht'.1])
  dsimp [prefixPoint] at hh
  rw [pow_succ]
  nlinarith only [hh]

end BalancedTransport.Coding
end

end OAI
