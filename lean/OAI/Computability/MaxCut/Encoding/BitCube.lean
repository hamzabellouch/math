import Mathlib
import OAI.Computability.MaxCut.Estimates.Density

namespace OAI

noncomputable section
namespace OptimalMaxCut.GaussianBellman
open scoped BigOperators
open Set Finset
abbrev BitCube (n : ℕ) := Fin n → Bool

noncomputable def corrAverage (t : ℝ) : (n : ℕ) → (BitCube n → BitCube n → ℝ) → ℝ
  | 0, F => F default default
  | n + 1, F => corrAverage t n (fun x y =>
      ∑ a : Bool, ∑ b : Bool, bitPairWeight t a b * F (Fin.cons a x) (Fin.cons b y))

noncomputable def midpointSection {n : ℕ} (f : BitCube (n + 1) → ℝ) (x : BitCube n) : ℝ :=
  (f (Fin.cons false x) + f (Fin.cons true x)) / 2

noncomputable def slopeSection {n : ℕ} (f : BitCube (n + 1) → ℝ) (x : BitCube n) : ℝ :=
  (f (Fin.cons false x) - f (Fin.cons true x)) / 2

 theorem section_decomposition {n : ℕ} (f : BitCube (n + 1) → ℝ) (x : BitCube n) (a : Bool) :
    f (Fin.cons a x) = midpointSection f x + sign a * slopeSection f x := by
  cases a <;> simp only [midpointSection, slopeSection, sign, Bool.false_eq_true, ↓reduceIte] <;> ring

 theorem midpointSection_mem {n : ℕ} {f : BitCube (n + 1) → ℝ} {l u : ℝ}
    (hf : ∀ x, f x ∈ Icc l u) (x : BitCube n) : midpointSection f x ∈ Icc l u := by
  have h0 := hf (Fin.cons false x)
  have h1 := hf (Fin.cons true x)
  dsimp [midpointSection]
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

 theorem expect_section {n : ℕ} (f : BitCube (n + 1) → ℝ) :
    (𝔼 x, f x) = 𝔼 x, midpointSection f x := by
  have he := (Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
    (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)).symm
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm] at he
  rw [he]
  apply Finset.expect_congr rfl
  intro x _
  rw [Fintype.expect_eq_sum_div_card]
  simp [midpointSection, add_comm]

 theorem corrAverage_mono {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (n : ℕ)
    {F G : BitCube n → BitCube n → ℝ} (h : ∀ x y, F x y ≤ G x y) :
    corrAverage t n F ≤ corrAverage t n G := by
  induction n with
  | zero => exact h _ _
  | succ n ih =>
    apply ih
    intro x y
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    exact mul_le_mul_of_nonneg_left (h _ _) (bitPairWeight_nonneg ht a b)

 theorem corrAverage_add (t : ℝ) (n : ℕ) (F G : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => F x y + G x y) = corrAverage t n F + corrAverage t n G := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [corrAverage, mul_add, Finset.sum_add_distrib, ih]

 theorem corrAverage_mul_const (t c : ℝ) (n : ℕ) (F : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => F x y * c) = corrAverage t n F * c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [corrAverage, ← mul_assoc, ← Finset.sum_mul, ih]

 theorem corrAverage_const_mul (t c : ℝ) (n : ℕ) (F : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => c * F x y) = c * corrAverage t n F := by
  simpa only [mul_comm] using corrAverage_mul_const t c n F

 theorem expect_zero_cube (f : BitCube 0 → ℝ) : (𝔼 x, f x) = f default := by
  have hf : f = fun _ => f default := funext (fun x => congrArg f (Subsingleton.elim x default))
  rw [hf, Fintype.expect_const]

 theorem corrAverage_fst (t : ℝ) (n : ℕ) (f : BitCube n → ℝ) :
    corrAverage t n (fun x _ => f x) = 𝔼 x, f x := by
  induction n with
  | zero => exact (expect_zero_cube f).symm
  | succ n ih =>
    have hp (x : BitCube n) :
        (∑ a : Bool, ∑ b : Bool, bitPairWeight t a b * f (Fin.cons a x)) = midpointSection f x := by
      simp only [Fintype.sum_bool, bitPairWeight, sign, Bool.false_eq_true, ↓reduceIte, midpointSection]
      ring
    simp only [corrAverage, hp]
    rw [ih, expect_section]

 theorem corrAverage_snd (t : ℝ) (n : ℕ) (f : BitCube n → ℝ) :
    corrAverage t n (fun _ y => f y) = 𝔼 y, f y := by
  induction n with
  | zero => exact (expect_zero_cube f).symm
  | succ n ih =>
    have hp (y : BitCube n) :
        (∑ a : Bool, ∑ b : Bool, bitPairWeight t a b * f (Fin.cons b y)) = midpointSection f y := by
      simp only [Fintype.sum_bool, bitPairWeight, sign, Bool.false_eq_true, ↓reduceIte, midpointSection]
      ring
    simp only [corrAverage, hp]
    rw [ih, expect_section]

noncomputable def cubicCost : (n : ℕ) → (BitCube n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, f => (𝔼 x, |slopeSection f x| ^ 3) + cubicCost n (midpointSection f)

 theorem finite_bellman_tensorization {t C l u : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (J : ℝ → ℝ → ℝ)
    (hJ : ∀ x y a b : ℝ,
      (∀ e : Bool, x + sign e * a ∈ Icc l u) →
      (∀ e : Bool, y + sign e * b ∈ Icc l u) →
      (∑ e : Bool, ∑ f : Bool, bitPairWeight t e f * J (x + sign e * a) (y + sign f * b)) ≤
      J x y + C * (|a| ^ 3 + |b| ^ 3))
    (n : ℕ) (f g : BitCube n → ℝ) (hf : ∀ x, f x ∈ Icc l u) (hg : ∀ x, g x ∈ Icc l u) :
    corrAverage t n (fun x y => J (f x) (g y)) ≤
      J (𝔼 x, f x) (𝔼 y, g y) + C * (cubicCost n f + cubicCost n g) := by
  induction n with
  | zero => simp only [corrAverage, cubicCost, expect_zero_cube, add_zero, mul_zero, le_refl]
  | succ n ih =>
    have hlocal (x y : BitCube n) :
        (∑ a : Bool, ∑ b : Bool, bitPairWeight t a b * J (f (Fin.cons a x)) (g (Fin.cons b y))) ≤
        J (midpointSection f x) (midpointSection g y) +
          C * (|slopeSection f x| ^ 3 + |slopeSection g y| ^ 3) := by
      simpa only [← section_decomposition] using hJ (midpointSection f x) (midpointSection g y)
        (slopeSection f x) (slopeSection g y)
        (fun e => by rw [← section_decomposition]; exact hf _)
        (fun e => by rw [← section_decomposition]; exact hg _)
    have hb := corrAverage_mono ht n hlocal
    rw [corrAverage_add, corrAverage_const_mul, corrAverage_add, corrAverage_fst, corrAverage_snd] at hb
    have hi := ih (midpointSection f) (midpointSection g) (midpointSection_mem hf) (midpointSection_mem hg)
    rw [expect_section f, expect_section g]
    simp only [corrAverage, cubicCost]
    linarith

noncomputable def gradient {n : ℕ} (f : BitCube n → ℝ) (i : Fin n) (x : BitCube n) : ℝ :=
  (f x - f (Function.update x i (!x i))) / 2

 theorem gradient_cons_zero {n : ℕ} (f : BitCube (n + 1) → ℝ) (a : Bool) (x : BitCube n) :
    gradient f 0 (Fin.cons a x) = sign a * slopeSection f x := by
  cases a <;> simp [gradient, sign, slopeSection] ; ring

 theorem gradient_midpoint {n : ℕ} (f : BitCube (n + 1) → ℝ) (i : Fin n) (x : BitCube n) :
    gradient (midpointSection f) i x = midpointSection (gradient f i.succ) x := by
  simp only [gradient, midpointSection, Fin.cons_succ, ← Fin.cons_update]
  ring

 theorem abs_midpoint_cube_le (a b : ℝ) :
    |(a + b) / 2| ^ 3 ≤ (|a| ^ 3 + |b| ^ 3) / 2 := by
  have h := abs_add_le a b
  have hpow : |a + b| ^ 3 ≤ (|a| + |b|) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h 3
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_pow]
  have hm := mul_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b)) (sq_nonneg (|a| - |b|))
  nlinarith

 theorem midpoint_cubic_contract {n : ℕ} (f : BitCube (n + 1) → ℝ) :
    (𝔼 x, |midpointSection f x| ^ 3) ≤ 𝔼 x, |f x| ^ 3 := by
  rw [expect_section (fun x => |f x| ^ 3)]
  apply Finset.expect_le_expect
  intro x _
  exact abs_midpoint_cube_le _ _

 theorem gradient_zero_cubic {n : ℕ} (f : BitCube (n + 1) → ℝ) :
    (𝔼 x, |gradient f 0 x| ^ 3) = 𝔼 x, |slopeSection f x| ^ 3 := by
  rw [expect_section]
  apply Finset.expect_congr rfl
  intro x _
  simp [midpointSection, gradient_cons_zero, sign]

 theorem cubicCost_le_gradients (n : ℕ) (f : BitCube n → ℝ) :
    cubicCost n f ≤ ∑ i, 𝔼 x, |gradient f i x| ^ 3 := by
  induction n with
  | zero => simp [cubicCost]
  | succ n ih =>
    rw [cubicCost, Fin.sum_univ_succ, gradient_zero_cubic]
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ i, 𝔼 x, |gradient (midpointSection f) i x| ^ 3 := ih _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        simp only [gradient_midpoint]
        exact midpoint_cubic_contract _

 theorem gradient_lipschitz {n : ℕ} (F : ℝ → ℝ)
    (hF : ∀ a b, |F a - F b| ≤ |a - b|) (f : BitCube n → ℝ) (i : Fin n) (x : BitCube n) :
    |gradient (fun x => F (f x)) i x| ≤ |gradient f i x| := by
  simp only [gradient, abs_div]
  exact div_le_div_of_nonneg_right (hF _ _) (abs_nonneg _)

end OptimalMaxCut.GaussianBellman

end

end OAI
