import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace BinPackingGap

theorem nat_size_mono {a b : ℕ} (h : a ≤ b) : Nat.size a ≤ Nat.size b :=
  Nat.size_le_size h

theorem nat_size_mul_le (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  simpa only [Nat.pow_add] using
    Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem nat_size_pow_succ_le (a m : ℕ) :
    Nat.size (a ^ (m + 1)) ≤ (m + 1) * Nat.size a := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      Nat.size (a ^ (m + 1 + 1)) = Nat.size (a ^ (m + 1) * a) := by rw [Nat.pow_succ]
      _ ≤ Nat.size (a ^ (m + 1)) + Nat.size a := nat_size_mul_le _ _
      _ ≤ (m + 1) * Nat.size a + Nat.size a := Nat.add_le_add_right ih _
      _ = (m + 1 + 1) * Nat.size a := by simp only [Nat.add_mul, Nat.one_mul]

theorem nat_size_pow_le_of_pos (a m : ℕ) (hm : 0 < m) :
    Nat.size (a ^ m) ≤ m * Nat.size a := by
  cases m with
  | zero => omega
  | succ m => exact nat_size_pow_succ_le a m

theorem nat_size_pow_le (a m : ℕ) :
    Nat.size (a ^ m) ≤ m * Nat.size a + 1 := by
  cases m with
  | zero => simp [Nat.size_one]
  | succ m => exact Nat.le_trans (nat_size_pow_succ_le a m) (Nat.le_succ _)

theorem nat_size_add_le_max (a b : ℕ) :
    Nat.size (a + b) ≤ max (Nat.size a) (Nat.size b) + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ max (Nat.size a) (Nat.size b) :=
    Nat.size_le.mp (Nat.le_max_left _ _)
  have hb : b < 2 ^ max (Nat.size a) (Nat.size b) :=
    Nat.size_le.mp (Nat.le_max_right _ _)
  calc
    a + b < 2 ^ max (Nat.size a) (Nat.size b) +
        2 ^ max (Nat.size a) (Nat.size b) := Nat.add_lt_add ha hb
    _ = 2 ^ (max (Nat.size a) (Nat.size b) + 1) := by
      rw [Nat.pow_succ]
      omega

theorem nat_size_add_le (a b : ℕ) :
    Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  have h := nat_size_add_le_max a b
  omega

theorem nat_size_le_self (n : ℕ) : Nat.size n ≤ n :=
  Nat.size_le.mpr Nat.lt_two_pow_self

theorem nat_size_sub_le (a b : ℕ) : Nat.size (a - b) ≤ Nat.size a :=
  nat_size_mono (Nat.sub_le a b)

theorem nat_size_succ_le (a : ℕ) : Nat.size (a + 1) ≤ Nat.size a + 1 := by
  cases a with
  | zero => simp [Nat.size_zero, Nat.size_one]
  | succ a =>
    have hpos : 1 ≤ Nat.size (a + 1) := Nat.size_pos.mpr (Nat.succ_pos a)
    have h := nat_size_add_le_max (a + 1) 1
    simpa only [Nat.size_one, Nat.max_eq_left hpos] using h

end BinPackingGap

namespace BinPackingGap.GraphPackingBounds

def repetitionCoefficient (P K : ℕ) : ℕ := 100 * (P + K + 1)

def binCoefficient (P K t d : ℕ) : ℕ := t + 4 * d * repetitionCoefficient P K

def widthCoefficient (P K T P₀ : ℕ) : ℕ :=
  repetitionCoefficient P K + Nat.size T + Nat.size P₀ +
    Nat.size 160 + Nat.size 1000000000 + 5

theorem one_le_input_square (s : ℕ) : 1 ≤ (s + 1) ^ 2 :=
  Nat.pow_pos (Nat.succ_pos s)

theorem input_le_input_square (s : ℕ) : s + 1 ≤ (s + 1) ^ 2 := by nlinarith

theorem constant_le_quadratic (c s : ℕ) : c ≤ c * (s + 1) ^ 2 := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left c (one_le_input_square s)

theorem linear_le_quadratic (c s : ℕ) :
    c * (s + 1) ≤ c * (s + 1) ^ 2 :=
  Nat.mul_le_mul_left c (input_le_input_square s)

theorem repetitions_le_linear (P K n s : ℕ) (hn : n ≤ s) :
    100 * (P + n * K + 1) ≤ repetitionCoefficient P K * (s + 1) := by
  have hnk := Nat.mul_le_mul_right K hn
  unfold repetitionCoefficient
  nlinarith [Nat.zero_le (P * s)]

theorem bins_le_quadratic (P K n m t d s : ℕ) (hn : n ≤ s) (hm : m ≤ s) :
    n * t + 4 * d * m * (100 * (P + n * K + 1)) ≤
      binCoefficient P K t d * (s + 1) ^ 2 := by
  let c := repetitionCoefficient P K
  have hR := repetitions_le_linear P K n s hn
  have hmul := Nat.mul_le_mul (show m ≤ s + 1 by omega) hR
  have hmul' : m * (100 * (P + n * K + 1)) ≤ c * (s + 1) ^ 2 := by
    dsimp [c]
    nlinarith [hmul]
  have hnt : n * t ≤ t * (s + 1) ^ 2 := by
    have hn' : n ≤ (s + 1) ^ 2 := by
      exact hn.trans ((Nat.le_succ s).trans (input_le_input_square s))
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right t hn'
  have hrest := Nat.mul_le_mul_left (4 * d) hmul'
  unfold binCoefficient
  dsimp [c] at hrest
  nlinarith

theorem size_repetitions_le_linear (P K n s : ℕ) (hn : n ≤ s) :
    Nat.size (100 * (P + n * K + 1)) ≤
      repetitionCoefficient P K * (s + 1) :=
  (nat_size_le_self _).trans (repetitions_le_linear P K n s hn)

theorem size_bin_count_le_quadratic (P K n m t d s : ℕ)
    (hn : n ≤ s) (hm : m ≤ s) :
    Nat.size (n * t + 4 * d * m * (100 * (P + n * K + 1))) ≤
      binCoefficient P K t d * (s + 1) ^ 2 :=
  (nat_size_le_self _).trans (bins_le_quadratic P K n m t d s hn hm)

theorem size_radix_le_linear (P K n s : ℕ) (hn : n ≤ s) :
    Nat.size (100 * (P + n * K + 1) + 1) ≤
      (repetitionCoefficient P K + 1) * (s + 1) := by
  have h := (nat_size_le_self _).trans
    (Nat.add_le_add_right (repetitions_le_linear P K n s hn) 1)
  nlinarith

theorem size_edge_power_le_quadratic (P K n m s : ℕ) (hn : n ≤ s) (hm : m ≤ s) :
    Nat.size ((100 * (P + n * K + 1) + 1) ^ m) ≤
      (repetitionCoefficient P K + 2) * (s + 1) ^ 2 := by
  have hpow := nat_size_pow_le (100 * (P + n * K + 1) + 1) m
  have hradix := size_radix_le_linear P K n s hn
  have hm' : m ≤ s + 1 := by omega
  have hprod := Nat.mul_le_mul hm' hradix
  have hsq := one_le_input_square s
  nlinarith

theorem size_vertex_power_le_linear (n s : ℕ) (hn : n ≤ s) :
    Nat.size (3 ^ n) ≤ 3 * (s + 1) := by
  have h := nat_size_pow_le 3 n
  have hthree : Nat.size 3 ≤ 2 := by decide
  have hp := Nat.mul_le_mul_left n hthree
  omega

theorem size_geometry_denominator_le_quadratic (P K T n m s : ℕ)
    (hn : n ≤ s) (hm : m ≤ s) :
    Nat.size (160 * (100 * (P + n * K + 1) + 1) ^ m * T) ≤
      (repetitionCoefficient P K + 2 + Nat.size 160 + Nat.size T) *
        (s + 1) ^ 2 := by
  have hmul₁ := nat_size_mul_le 160 ((100 * (P + n * K + 1) + 1) ^ m)
  have hmul₂ := nat_size_mul_le (160 * (100 * (P + n * K + 1) + 1) ^ m) T
  have hp := size_edge_power_le_quadratic P K n m s hn hm
  have hc₁ := constant_le_quadratic (Nat.size 160) s
  have hc₂ := constant_le_quadratic (Nat.size T) s
  nlinarith

theorem size_size_denominator_le_quadratic (P K T P₀ n m s : ℕ)
    (hn : n ≤ s) (hm : m ≤ s) :
    Nat.size (1000000000 * P₀ * 3 ^ n *
      (160 * (100 * (P + n * K + 1) + 1) ^ m * T)) ≤
      widthCoefficient P K T P₀ * (s + 1) ^ 2 := by
  have hmul₁ := nat_size_mul_le 1000000000 P₀
  have hmul₂ := nat_size_mul_le (1000000000 * P₀) (3 ^ n)
  have hmul₃ := nat_size_mul_le (1000000000 * P₀ * 3 ^ n)
    (160 * (100 * (P + n * K + 1) + 1) ^ m * T)
  have hgeom := size_geometry_denominator_le_quadratic P K T n m s hn hm
  have hQ := (size_vertex_power_le_linear n s hn).trans (linear_le_quadratic 3 s)
  have hc₁ := constant_le_quadratic (Nat.size 1000000000) s
  have hc₂ := constant_le_quadratic (Nat.size P₀) s
  unfold widthCoefficient
  nlinarith

theorem size_le_scaled_size_denominator (P K T P₀ n m s c v : ℕ)
    (hn : n ≤ s) (hm : m ≤ s)
    (hv : v ≤ c * (1000000000 * P₀ * 3 ^ n *
      (160 * (100 * (P + n * K + 1) + 1) ^ m * T))) :
    Nat.size v ≤ (Nat.size c + widthCoefficient P K T P₀) * (s + 1) ^ 2 := by
  have hvsize := nat_size_mono hv
  have hmul := nat_size_mul_le c (1000000000 * P₀ * 3 ^ n *
    (160 * (100 * (P + n * K + 1) + 1) ^ m * T))
  have hden := size_size_denominator_le_quadratic P K T P₀ n m s hn hm
  have hc := constant_le_quadratic (Nat.size c) s
  nlinarith

theorem construction_cost_le_degree_eight
    (s operations arithmetic width scan finish bins scratch : ℕ) :
    operations * (s + 1) ^ 2 *
        (arithmetic * (width * (s + 1) ^ 2 + 1) ^ 2 + scan * (s + 1) ^ 2) +
      finish * (5 * (bins * (s + 1) ^ 2) * (width * (s + 1) ^ 2 + 1) +
        scratch * (s + 1) ^ 4 + 1) ≤
    (operations * (arithmetic * (width + 1) ^ 2 + scan) +
      finish * (5 * bins * (width + 1) + scratch + 1)) * (s + 1) ^ 8 := by
  let S := s + 1
  have hS : 0 < S := by dsimp [S]; omega
  have h1 : 1 ≤ S ^ 2 := by dsimp [S]; exact one_le_input_square s
  have h24 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  have h48 : S ^ 4 ≤ S ^ 8 := Nat.pow_le_pow_right hS (by decide)
  have h68 : S ^ 6 ≤ S ^ 8 := Nat.pow_le_pow_right hS (by decide)
  have hw : width * S ^ 2 + 1 ≤ (width + 1) * S ^ 2 := by nlinarith
  have hw2 : (width * S ^ 2 + 1) ^ 2 ≤ (width + 1) ^ 2 * S ^ 4 := by
    calc
      _ ≤ ((width + 1) * S ^ 2) ^ 2 := Nat.pow_le_pow_left hw 2
      _ = _ := by ring
  have hbody : arithmetic * (width * S ^ 2 + 1) ^ 2 + scan * S ^ 2 ≤
      (arithmetic * (width + 1) ^ 2 + scan) * S ^ 4 := by
    have ha := Nat.mul_le_mul_left arithmetic hw2
    have hb := Nat.mul_le_mul_left scan h24
    nlinarith
  have hmain : operations * S ^ 2 *
      (arithmetic * (width * S ^ 2 + 1) ^ 2 + scan * S ^ 2) ≤
      (operations * (arithmetic * (width + 1) ^ 2 + scan)) * S ^ 8 := by
    calc
      _ ≤ operations * S ^ 2 *
          ((arithmetic * (width + 1) ^ 2 + scan) * S ^ 4) :=
        Nat.mul_le_mul_left (operations * S ^ 2) hbody
      _ = (operations * (arithmetic * (width + 1) ^ 2 + scan)) * S ^ 6 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h68
  have hitems : 5 * (bins * S ^ 2) * (width * S ^ 2 + 1) ≤
      (5 * bins * (width + 1)) * S ^ 4 := by
    have h := Nat.mul_le_mul_left (5 * (bins * S ^ 2)) hw
    nlinarith
  have hfinish : finish * (5 * (bins * S ^ 2) * (width * S ^ 2 + 1) +
        scratch * S ^ 4 + 1) ≤
      (finish * (5 * bins * (width + 1) + scratch + 1)) * S ^ 8 := by
    have hinside : 5 * (bins * S ^ 2) * (width * S ^ 2 + 1) + scratch * S ^ 4 + 1 ≤
        (5 * bins * (width + 1) + scratch + 1) * S ^ 4 := by
      nlinarith [h1.trans h24]
    calc
      _ ≤ finish * ((5 * bins * (width + 1) + scratch + 1) * S ^ 4) :=
        Nat.mul_le_mul_left finish hinside
      _ = (finish * (5 * bins * (width + 1) + scratch + 1)) * S ^ 4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h48
  change operations * S ^ 2 *
      (arithmetic * (width * S ^ 2 + 1) ^ 2 + scan * S ^ 2) +
      finish * (5 * (bins * S ^ 2) * (width * S ^ 2 + 1) + scratch * S ^ 4 + 1) ≤ _
  calc
    _ ≤ (operations * (arithmetic * (width + 1) ^ 2 + scan)) * S ^ 8 +
        (finish * (5 * bins * (width + 1) + scratch + 1)) * S ^ 8 :=
      Nat.add_le_add hmain hfinish
    _ = _ := by dsimp [S]; ring

end BinPackingGap.GraphPackingBounds

end OAI
