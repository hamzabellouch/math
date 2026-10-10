import Mathlib
import OAI.Computability.MinUncut.PCP.CayleySpectral

namespace OAI

section
open scoped BigOperators

namespace MinUncutGames.Foundations.PCP.Overlay

open PoweringWalks SpectralReturn

variable {V D E A : Type*}

def originalPortGraph (G : ConstraintGraph V (V × D) A) : PortGraph V D where
  rot := G.reverse
  rot_involutive := G.reverse_involutive

def rotate (G : PortGraph V D) (H : PortGraph V E) :
    V × (D ⊕ E) → V × (D ⊕ E)
  | (v, Sum.inl d) => ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2)
  | (v, Sum.inr e) => ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2)

theorem rotate_involutive (G : PortGraph V D) (H : PortGraph V E) :
    Function.Involutive (rotate G H) := by
  rintro ⟨v, p⟩
  rcases p with d | e
  · exact congrArg (fun a : V × D => (a.1, (Sum.inl a.2 : D ⊕ E)))
      (G.rot_involutive (v, d))
  · exact congrArg (fun a : V × E => (a.1, (Sum.inr a.2 : D ⊕ E)))
      (H.rot_involutive (v, e))

def portGraph (G : PortGraph V D) (H : PortGraph V E) : PortGraph V (D ⊕ E) where
  rot :=
    { toFun := rotate G H
      invFun := rotate G H
      left_inv := rotate_involutive G H
      right_inv := rotate_involutive G H }
  rot_involutive := rotate_involutive G H

@[simp] theorem portGraph_rot_inl (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (d : D) :
    (portGraph G H).rot (v, Sum.inl d) =
      ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2) := rfl

@[simp] theorem portGraph_rot_inr (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (e : E) :
    (portGraph G H).rot (v, Sum.inr e) =
      ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2) := rfl

def constraintGraph (G : ConstraintGraph V (V × D) A) (H : PortGraph V E) :
    ConstraintGraph V (V × (D ⊕ E)) A where
  reverse := (portGraph (originalPortGraph G) H).rot
  reverse_involutive := (portGraph (originalPortGraph G) H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl d => G.accepts (p.1, d) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v, p⟩ a b
    rcases p with d | e
    · exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) : (constraintGraph G H).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) :
    originalPortGraph (constraintGraph G H) = portGraph (originalPortGraph G) H := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (htail : G.tail = Prod.fst)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inl d) =
      G.edgeSatisfied labeling (v, d) := by
  change G.accepts (v, d) (labeling v) (labeling (G.reverse (v, d)).1) =
    G.accepts (v, d) (labeling (G.tail (v, d)))
      (labeling (G.tail (G.reverse (v, d))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (labeling : V → A) (v : V) (e : E) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inr e) = true := rfl

theorem complete (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) (labeling : V → A)
    (h : ∀ a, G.edgeSatisfied labeling a = true) :
    ∀ a, (constraintGraph G H).edgeSatisfied labeling a = true := by
  rintro ⟨v, p⟩
  rcases p with d | e
  · rw [edgeSatisfied_inl G H htail]
    exact h (v, d)
  · rfl

theorem satisfiable_iff (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) :
    (constraintGraph G H).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling, h⟩
    refine ⟨labeling, ?_⟩
    rintro ⟨v, d⟩
    rw [← edgeSatisfied_inl G H htail]
    exact h (v, Sum.inl d)
  · rintro ⟨labeling, h⟩
    exact ⟨labeling, complete G H htail labeling h⟩

theorem rejectionCount_eq [Fintype V] [Fintype D] [Fintype E]
    (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) (labeling : V → A) :
    (constraintGraph G H).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  simp [edgeSatisfied_inl G H htail]

theorem card_ports [Fintype D] [Fintype E] :
    Fintype.card (D ⊕ E) = Fintype.card D + Fintype.card E := Fintype.card_sum

theorem card_darts [Fintype V] [Fintype D] [Fintype E] :
    Fintype.card (V × (D ⊕ E)) =
      Fintype.card (V × D) + Fintype.card (V × E) := by
  simp only [Fintype.card_prod, Fintype.card_sum, Nat.mul_add]

section Averages

variable [Fintype V] [Fintype D] [Fintype E]

omit [Fintype V] in

theorem operator_mix [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph V E) (f : V → ℝ) (v : V) :
    averagingOperator (portGraph G H) f v =
      (Fintype.card D : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E) *
        averagingOperator G f v +
      (Fintype.card E : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E) *
        averagingOperator H f v := by
  have hd : (0 : ℝ) < Fintype.card D := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have he : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  change mean (fun p : D ⊕ E => f ((portGraph G H).rot (v, p)).1) = _
  rw [mean_eq_sum_div_card]
  simp only [Fintype.sum_sum_type, Fintype.card_sum, Nat.cast_add,
    portGraph_rot_inl, portGraph_rot_inr]
  unfold averagingOperator
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  field_simp [hd.ne', he.ne', (add_pos hd he).ne']

theorem energy_convex_mix (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (f g : V → ℝ) :
    energy (fun v => a * f v + b * g v) ≤ a * energy f + b * energy g := by
  calc
    energy (fun v => a * f v + b * g v) ≤
        mean (fun v => a * (f v) ^ 2 + b * (g v) ^ 2) := by
      apply mean_mono
      intro v
      have hnormalize := congrArg (fun t : ℝ => t * (a * (f v) ^ 2 + b * (g v) ^ 2)) hab
      have hnonneg := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (f v - g v))
      nlinarith
    _ = a * energy f + b * energy g := by
      rw [mean_add, mean_mul_left, mean_mul_left]
      rfl

theorem energy_bound [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph V E) (lambda : ℝ)
    (certificate : SpectralCertificate H lambda) (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (portGraph G H) f) ≤
      ((Fintype.card D : ℝ) + (Fintype.card E : ℝ) * lambda ^ 2) /
        ((Fintype.card D : ℝ) + Fintype.card E) * energy f := by
  let a : ℝ := (Fintype.card D : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E)
  let b : ℝ := (Fintype.card E : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E)
  have hd : (0 : ℝ) < Fintype.card D := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have he : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  have hden : (0 : ℝ) < (Fintype.card D : ℝ) + Fintype.card E := add_pos hd he
  have ha : 0 ≤ a := div_nonneg hd.le hden.le
  have hb : 0 ≤ b := div_nonneg he.le hden.le
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← add_div, div_self hden.ne']
  have hop : averagingOperator (portGraph G H) f =
      fun v => a * averagingOperator G f v + b * averagingOperator H f v := by
    funext v
    exact operator_mix G H f v
  calc
    energy (averagingOperator (portGraph G H) f) ≤
        a * energy (averagingOperator G f) + b * energy (averagingOperator H f) := by
      rw [hop]
      exact energy_convex_mix a b ha hb hab _ _
    _ ≤ a * energy f + b * (lambda ^ 2 * energy f) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (ZigzagSpectral.averaging_energy_le G f) ha)
        (mul_le_mul_of_nonneg_left (certificate.contraction f hf) hb)
    _ = _ := by
      dsimp [a, b]
      ring

theorem energy_bound_three_quarters [Nonempty V]
    (G : PortGraph V D) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ))
    (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (portGraph G H) f) ≤ (3 / 4 : ℝ) * energy f := by
  let _ : Nonempty E := Fintype.card_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_one hpositive)
  let _ : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  have he : (1 : ℝ) ≤ Fintype.card E := by exact_mod_cast hpositive
  have hd : (Fintype.card D : ℝ) = (Fintype.card E : ℝ) + 1 := by exact_mod_cast hdegree
  have hden : (0 : ℝ) < (Fintype.card D : ℝ) + Fintype.card E := by linarith
  have hcoefficient :
      ((Fintype.card D : ℝ) + (Fintype.card E : ℝ) * (1 / 2 : ℝ) ^ 2) /
        ((Fintype.card D : ℝ) + Fintype.card E) ≤ (3 / 4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact (energy_bound G H (1 / 2) certificate f hf).trans
    (mul_le_mul_of_nonneg_right hcoefficient (energy_nonnegative f))

theorem spectralCertificate_seven_eighths [Nonempty V]
    (G : PortGraph V D) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ)) :
    SpectralCertificate (portGraph G H) (7 / 8 : ℝ) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction := by
    intro f hf
    exact (energy_bound_three_quarters G H hdegree hpositive certificate f hf).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (3 / 4 : ℝ) ≤ (7 / 8 : ℝ) ^ 2)
        (energy_nonnegative f))

theorem constraintGraph_spectralCertificate [Nonempty V]
    (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ)) :
    SpectralCertificate (originalPortGraph (constraintGraph G H)) (7 / 8 : ℝ) := by
  rw [constraintGraph_portGraph]
  exact spectralCertificate_seven_eighths (originalPortGraph G) H
    hdegree hpositive certificate

end Averages

end MinUncutGames.Foundations.PCP.Overlay

end
section
namespace MinUncutGames.Foundations.PCP.LazySmoothing

open scoped BigOperators

def bitCount {n : ℕ} (tape : Fin n → Bool) : ℕ :=
  ∑ i, if tape i then 1 else 0

noncomputable def binomialMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  Finset.univ.expect (fun tape : Fin n → Bool => g (bitCount tape))

def splitTape (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Bool × (Fin n → Bool)) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv _ := rfl

theorem bitCount_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    bitCount x = (if x 0 then 1 else 0) + bitCount (fun i => x i.succ) := by
  exact Fin.sum_univ_succ _

theorem mean_congr {n : ℕ} {f g : ℕ → ℝ} (h : ∀ k, f k = g k) :
    binomialMean n f = binomialMean n g := by
  unfold binomialMean
  exact Finset.expect_congr rfl (fun x _ => h (bitCount x))

@[simp] theorem mean_const (n : ℕ) (c : ℝ) :
    binomialMean n (fun _ => c) = c := Fintype.expect_const c

theorem mean_add (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k + g k) = binomialMean n f + binomialMean n g :=
  Finset.expect_add_distrib _ _ _

theorem mean_sub (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k - g k) = binomialMean n f - binomialMean n g :=
  Finset.expect_sub_distrib _ _ _

theorem mean_mul (n : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    binomialMean n (fun k => c * f k) = c * binomialMean n f := by
  exact (Finset.mul_expect Finset.univ (fun x : Fin n → Bool => f (bitCount x)) c).symm

@[simp] theorem mean_zero (g : ℕ → ℝ) : binomialMean 0 g = g 0 := by
  simp [binomialMean, bitCount]

theorem expect_bool (f : Bool → ℝ) : Finset.univ.expect f = (f false + f true) / 2 := by
  rw [Finset.expect_eq_sum_div_card]
  simp [Fintype.univ_bool, add_comm]

theorem mean_succ (n : ℕ) (g : ℕ → ℝ) :
    binomialMean (n + 1) g =
      (binomialMean n g + binomialMean n (fun k => g (k + 1))) / 2 := by
  unfold binomialMean
  rw [Fintype.expect_equiv (splitTape n)
    (fun x => g (bitCount x))
    (fun x => g ((if x.1 then 1 else 0) + bitCount x.2))
    (fun x => congrArg g (bitCount_succ x))]
  rw [← Finset.univ_product_univ, Finset.expect_product, expect_bool]
  simp [Nat.add_comm]

def score (n k : ℕ) : ℝ := (n : ℝ) - 2 * (k : ℝ)

noncomputable def scoreMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  binomialMean n (fun k => score n k * g k)

@[simp] theorem scoreMean_zero (g : ℕ → ℝ) : scoreMean 0 g = 0 := by
  simp [scoreMean, score]

theorem scoreMean_succ (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g =
      ((scoreMean n g + binomialMean n g) +
       (scoreMean n (fun k => g (k + 1)) -
        binomialMean n (fun k => g (k + 1)))) / 2 := by
  unfold scoreMean
  rw [mean_succ]
  have h₁ : (fun k => score (n + 1) k * g k) =
      (fun k => score n k * g k + g k) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  have h₂ : (fun k => score (n + 1) (k + 1) * g (k + 1)) =
      (fun k => score n k * g (k + 1) - g (k + 1)) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  rw [h₁, h₂, mean_add, mean_sub]

theorem score_identity (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) / 2 *
      (binomialMean n g - binomialMean n (fun k => g (k + 1))) := by
  induction n generalizing g with
  | zero => simp [scoreMean_succ]; ring
  | succ n ih =>
    rw [scoreMean_succ, ih g, ih (fun k => g (k + 1))]
    simp only [mean_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem score_mean_zero (n : ℕ) : binomialMean n (score n) = 0 := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (fun _ => 1)
    simpa [scoreMean] using h

theorem score_second_moment (n : ℕ) :
    binomialMean n (fun k => score n k ^ 2) = (n : ℝ) := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (score (n + 1))
    have hd : binomialMean n (score (n + 1)) -
        binomialMean n (fun k => score (n + 1) (k + 1)) = 2 := by
      rw [← mean_sub]
      calc
        _ = binomialMean n (fun _ => 2) := by
          apply mean_congr
          intro k
          simp only [score, Nat.cast_add, Nat.cast_one]
          ring
        _ = 2 := mean_const _ _
    rw [hd] at h
    simpa [scoreMean, pow_two] using h

theorem score_difference (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) := by
  rw [score_identity, mean_succ]
  ring

theorem adjacent_difference_sq (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    4 * ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) ^ 2 ≤ 1 := by
  have hc : binomialMean (n + 1)
      (fun k => score (n + 1) k * (g k - 1 / 2)) = scoreMean (n + 1) g := by
    calc
      _ = binomialMean (n + 1) (fun k =>
          score (n + 1) k * g k - (1 / 2) * score (n + 1) k) := by
        apply mean_congr
        intro k
        ring
      _ = scoreMean (n + 1) g := by
        rw [mean_sub, mean_mul, score_mean_zero]
        simp [scoreMean]
  have hv : binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) ≤ 1 / 4 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro tape _
    have h₀ := (hg (bitCount tape)).1
    have h₁ := (hg (bitCount tape)).2
    have hp := mul_nonneg h₀ (sub_nonneg.mpr h₁)
    nlinarith
  have hcs : (binomialMean (n + 1)
        (fun k => score (n + 1) k * (g k - 1 / 2))) ^ 2 ≤
      binomialMean (n + 1) (fun k => score (n + 1) k ^ 2) *
        binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) :=
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ _ _
  rw [hc, score_difference, score_second_moment] at hcs
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hv (le_of_lt hn)
  simp only [Nat.cast_add, Nat.cast_one] at hcs
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

theorem adjacent_difference_le (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean n g - binomialMean (n + 1) g| ≤ 1 / r := by
  have hs := adjacent_difference_sq n g hg
  have hd := sq_nonneg (binomialMean n g - binomialMean (n + 1) g)
  have hh := mul_le_mul_of_nonneg_right hrn hd
  rw [le_div_iff₀ hr]
  have ha := sq_abs (binomialMean n g - binomialMean (n + 1) g)
  have hp : 0 ≤ |binomialMean n g - binomialMean (n + 1) g| * r :=
    mul_nonneg (abs_nonneg _) (le_of_lt hr)
  nlinarith [sq_nonneg (|binomialMean n g - binomialMean (n + 1) g| * r - 1)]

theorem mean_shift_le (n d : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean (n + d) g - binomialMean n g| ≤ (d : ℝ) / r := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hrnd : r ^ 2 ≤ 4 * ((n + d : ℕ) + 1 : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith
    have ha := adjacent_difference_le (n + d) g hg r hr hrnd
    rw [abs_sub_comm] at ha
    calc
      _ ≤ |binomialMean (n + d + 1) g - binomialMean (n + d) g| +
          |binomialMean (n + d) g - binomialMean n g| := abs_sub_le _ _ _
      _ ≤ 1 / r + (d : ℝ) / r := add_le_add ha ih
      _ = ((d + 1 : ℕ) : ℝ) / r := by push_cast; ring

theorem mean_ordered_difference_le (m n : ℕ) (hmn : m ≤ n) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1)) :
    |binomialMean n g - binomialMean m g| ≤ ((n - m : ℕ) : ℝ) / r := by
  simpa [Nat.add_sub_of_le hmn] using mean_shift_le m (n - m) g hg r hr hrm

theorem mean_window_le (N M m : ℕ) (hlo : N - M ≤ m) (hhi : m ≤ N + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (r : ℝ) (hr : 0 < r) (hbase : r ^ 2 ≤ 4 * (((N - M : ℕ) : ℝ) + 1)) :
    |binomialMean m g - binomialMean N g| ≤ (M : ℝ) / r := by
  by_cases hmN : m ≤ N
  · have hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlo
      linarith
    have h := mean_ordered_difference_le m N hmN g hg r hr hrm
    rw [abs_sub_comm] at h
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : N - m ≤ M := by omega
    exact_mod_cast this
  · have hNm : N ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmN)
    have hrN : r ^ 2 ≤ 4 * ((N : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N M
      linarith
    have h := mean_ordered_difference_le N m hNm g hg r hr hrN
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : m - N ≤ M := by omega
    exact_mod_cast this

theorem square_window_le (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    |binomialMean m g - binomialMean ((4 * q * M) ^ 2) g| ≤ 1 / (4 * (q : ℝ)) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR : (4 : ℝ) * M ≤ ((4 * q * M : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hRM : (M : ℝ) ≤ (((4 * q * M : ℕ) : ℝ)) ^ 2 := by nlinarith
  have hMN : M ≤ (4 * q * M) ^ 2 := by exact_mod_cast hRM
  have hr : (0 : ℝ) < ((4 * q * M : ℕ) : ℝ) := by linarith
  have hb : (((4 * q * M : ℕ) : ℝ)) ^ 2 ≤
      4 * (((((4 * q * M) ^ 2 - M : ℕ)) : ℝ) + 1) := by
    rw [Nat.cast_sub hMN, Nat.cast_pow]
    nlinarith
  have h := mean_window_le ((4 * q * M) ^ 2) M m hlo hhi g hg
    ((4 * q * M : ℕ) : ℝ) hr hb
  have he : (M : ℝ) / ((4 * q * M : ℕ) : ℝ) = 1 / (4 * (q : ℝ)) := by
    push_cast
    have hq0 : (q : ℝ) ≠ 0 := by linarith
    have hM0 : (M : ℝ) ≠ 0 := by linarith
    field_simp
  rw [he] at h
  exact h

theorem modal_transfer (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (hmodal : 1 / (q : ℝ) ≤ binomialMean ((4 * q * M) ^ 2) g) :
    1 / (2 * (q : ℝ)) ≤ binomialMean m g := by
  have h := square_window_le q M m hq hM hlo hhi g hg
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hrec : 0 < 1 / (q : ℝ) := one_div_pos.mpr hqR
  have he₁ : 1 / (4 * (q : ℝ)) = (1 / (q : ℝ)) / 4 := by ring
  have he₂ : 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) / 2 := by ring
  rw [he₁] at h
  rw [he₂]
  have hl := (abs_le.mp h).1
  linarith

end MinUncutGames.Foundations.PCP.LazySmoothing

end
section
namespace MinUncutGames.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def lazyRotate (G : PortGraph V D) : Edge V (Bool × D) → Edge V (Bool × D)
  | (v, (false, d)) => (v, (false, d))
  | (v, (true, d)) => ((G.rot (v, d)).1, (true, (G.rot (v, d)).2))

theorem lazyRotate_involutive (G : PortGraph V D) :
    Function.Involutive (lazyRotate G) := by
  rintro ⟨v, b, d⟩
  cases b with
  | false => rfl
  | true =>
    exact congrArg (fun e : V × D => (e.1, (true, e.2))) (rot_rot G (v, d))

def lazyGraph (G : PortGraph V D) : PortGraph V (Bool × D) where
  rot := {
    toFun := lazyRotate G
    invFun := lazyRotate G
    left_inv := lazyRotate_involutive G
    right_inv := lazyRotate_involutive G }
  rot_involutive := lazyRotate_involutive G

@[simp] theorem lazyGraph_rot_false (G : PortGraph V D) (v : V) (d : D) :
    (lazyGraph G).rot (v, (false, d)) = (v, (false, d)) := rfl

@[simp] theorem lazyGraph_rot_true (G : PortGraph V D) (v : V) (d : D) :
    (lazyGraph G).rot (v, (true, d)) = ((G.rot (v, d)).1, (true, (G.rot (v, d)).2)) := rfl

end MinUncutGames.Foundations.PCP.PoweringWalks

namespace MinUncutGames.Foundations.PCP.PoweringLazy

open PoweringWalks SpectralReturn

variable {V D : Type*}

theorem operator_binomialMean [Fintype D] (G : PortGraph V D)
    (n : Nat) (g : Nat → V → ℝ) (v : V) :
    averagingOperator G (fun w => LazySmoothing.binomialMean n (fun k => g k w)) v =
      LazySmoothing.binomialMean n (fun k => averagingOperator G (g k) v) := by
  unfold averagingOperator LazySmoothing.binomialMean
  exact Finset.expect_comm Finset.univ Finset.univ
    (fun d tape => g (LazySmoothing.bitCount tape) (G.rot (v, d)).1)

theorem averagingOperator_lazy [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) (v : V) :
    averagingOperator (lazyGraph G) f v = (f v + averagingOperator G f v) / 2 := by
  change mean (fun bd : Bool × D => f ((lazyGraph G).rot (v, bd)).1) = _
  rw [mean_prod]
  change Finset.univ.expect (fun b : Bool =>
    mean (fun d : D => f ((lazyGraph G).rot (v, (b, d))).1)) = _
  rw [LazySmoothing.expect_bool]
  simp only [lazyGraph_rot_false, lazyGraph_rot_true]
  rw [mean_const]
  rfl

theorem iterate_lazy_eq_binomialMean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (f : V → ℝ) :
    iterateOperator (lazyGraph G) n f =
      fun v => LazySmoothing.binomialMean n (fun k => iterateOperator G k f v) := by
  induction n with
  | zero =>
    funext v
    simp [iterateOperator]
  | succ n ih =>
    funext v
    change averagingOperator (lazyGraph G) (iterateOperator (lazyGraph G) n f) v = _
    rw [ih, averagingOperator_lazy, operator_binomialMean, LazySmoothing.mean_succ]
    rfl

theorem iterate_mem_Icc [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) (hf : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1)
    (n : Nat) (v : V) : iterateOperator G n f v ∈ Set.Icc (0 : ℝ) 1 := by
  induction n generalizing v with
  | zero => exact hf v
  | succ n ih =>
    change mean (fun d : D => iterateOperator G n f (G.rot (v, d)).1) ∈ Set.Icc (0 : ℝ) 1
    constructor
    · exact mean_nonnegative _ (fun d => (ih ((G.rot (v, d)).1)).1)
    · calc
        mean (fun d : D => iterateOperator G n f (G.rot (v, d)).1) ≤
            mean (fun _ : D => (1 : ℝ)) :=
          mean_mono (fun d => (ih ((G.rot (v, d)).1)).2)
        _ = 1 := mean_const _

theorem lazy_endpoint_modal_transfer [Fintype D] [Nonempty D]
    (G : PortGraph V D) (q M m : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (f : V → ℝ) (hf : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1) (v : V)
    (hmodal : 1 / (q : ℝ) ≤ iterateOperator (lazyGraph G) ((4 * q * M) ^ 2) f v) :
    1 / (2 * (q : ℝ)) ≤ iterateOperator (lazyGraph G) m f v := by
  rw [iterate_lazy_eq_binomialMean] at hmodal ⊢
  exact LazySmoothing.modal_transfer q M m hq hM hlo hhi
    (fun k => iterateOperator G k f v) (fun k => iterate_mem_Icc G f hf k v) hmodal

end MinUncutGames.Foundations.PCP.PoweringLazy

end
section
namespace MinUncutGames.Foundations.PCP.LazyConstraint

open scoped BigOperators
open PoweringWalks

variable {V D A : Type*}

def constraintGraph (G : ConstraintGraph V (V × D) A) :
    ConstraintGraph V (V × (Bool × D)) A where
  reverse := (lazyGraph (Overlay.originalPortGraph G)).rot
  reverse_involutive := (lazyGraph (Overlay.originalPortGraph G)).rot_involutive
  tail := Prod.fst
  accepts e a b := if e.2.1 then G.accepts (e.1,e.2.2) a b else true
  reverse_accepts := by
    rintro ⟨v,b,d⟩ a c
    cases b with
    | false => rfl
    | true => exact G.reverse_accepts (v,d) a c

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_reverse (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).reverse = (lazyGraph (Overlay.originalPortGraph G)).rot := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A) :
    Overlay.originalPortGraph (constraintGraph G) =
      lazyGraph (Overlay.originalPortGraph G) := rfl

@[simp] theorem edgeSatisfied_false (G : ConstraintGraph V (V × D) A)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(false,d)) = true := rfl

@[simp] theorem edgeSatisfied_true (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(true,d)) =
      G.edgeSatisfied labeling (v,d) := by
  change G.accepts (v,d) (labeling v) (labeling (G.reverse (v,d)).1) =
    G.accepts (v,d) (labeling (G.tail (v,d)))
      (labeling (G.tail (G.reverse (v,d))))
  rw [htail]

theorem complete (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ e, (constraintGraph G).edgeSatisfied labeling e = true := by
  rintro ⟨v,b,d⟩
  cases b with
  | false => rfl
  | true =>
    rw [edgeSatisfied_true G htail]
    exact h (v,d)

theorem complete_iff (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    (∀ e, (constraintGraph G).edgeSatisfied labeling e = true) ↔
      ∀ e, G.edgeSatisfied labeling e = true := by
  constructor
  · intro h
    rintro ⟨v,d⟩
    rw [← edgeSatisfied_true G htail]
    exact h (v,(true,d))
  · exact complete G htail labeling

theorem satisfiable_iff (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst) :
    (constraintGraph G).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling,h⟩
    exact ⟨labeling, (complete_iff G htail labeling).mp h⟩
  · rintro ⟨labeling,h⟩
    exact ⟨labeling, complete G htail labeling h⟩

theorem rejectionCount_eq [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    (constraintGraph G).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [edgeSatisfied_true G htail]

theorem card_ports [Fintype D] :
    Fintype.card (Bool × D) = 2 * Fintype.card D := by
  simp

theorem card_darts [Fintype V] [Fintype D] :
    Fintype.card (V × (Bool × D)) = 2 * Fintype.card (V × D) := by
  simp [Fintype.card_prod, Nat.mul_left_comm]

theorem rejection_density_eq_half [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    ((constraintGraph G).rejectionCount labeling : ℝ) /
        (Fintype.card (V × (Bool × D)) : ℝ) =
      ((G.rejectionCount labeling : ℝ) / (Fintype.card (V × D) : ℝ)) / 2 := by
  rw [rejectionCount_eq G htail, card_darts]
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev]
  ring

end MinUncutGames.Foundations.PCP.LazyConstraint

end

end OAI
