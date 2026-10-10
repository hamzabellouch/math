import OAI.Combinatorics.CliqueFree.EdgeState
import OAI.Combinatorics.CliqueFree.VariationalCross

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
universe u
variable {V : Type u} [Fintype V]

/-- A logarithm estimate with `log 2 ≤ 1` already applied. -/
lemma log_multiplier_le (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log (1 + Real.exp (4*x) * multiplierBound k (Real.exp (-8*x))) ≤
      (5 + 10*(k:ℝ) + (k:ℝ)^2)*x := by
  have hx0 : 0 ≤ x := by linarith
  have hε : Real.exp (-8*x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hb := multiplierBound_ge_one k (Real.exp_pos _) hε
  have he : 1 ≤ Real.exp (4*x) := Real.one_le_exp_iff.2 (by linarith)
  have hprod : 1 ≤ Real.exp (4*x) * multiplierBound k (Real.exp (-8*x)) :=
    one_le_mul_of_one_le_of_one_le he hb
  have hm := Real.log_le_log (by positivity : 0 < 1 + Real.exp (4*x) *
      multiplierBound k (Real.exp (-8*x)))
    (show 1 + Real.exp (4*x) * multiplierBound k (Real.exp (-8*x)) ≤
      2 * (Real.exp (4*x) * multiplierBound k (Real.exp (-8*x))) by linarith)
  have hbpos := multiplierBound_pos k (Real.exp_pos (-8*x))
  have hlogb : Real.log (multiplierBound k (Real.exp (-8*x))) =
      (((k:ℝ)+2)*k)*Real.log 2 + 8*(k:ℝ)*x := by
    unfold multiplierBound
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_exp]
    push_cast
    ring
  rw [Real.log_mul (by norm_num) (mul_pos (Real.exp_pos _) hbpos).ne',
    Real.log_mul (Real.exp_ne_zero _) hbpos.ne', Real.log_exp,hlogb] at hm
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ (1 + ((k:ℝ)+2)*k) := by positivity
  have haux := mul_le_mul_of_nonneg_left hlog2 hc
  have hxaux := mul_le_mul_of_nonneg_left hx hc
  nlinarith

lemma cross_error_le {s t x : ℝ} (hx : 1 ≤ x) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hslo : Real.exp (-x) ≤ s) (hsup : s ≤ Real.exp x) (htup : t ≤ Real.exp x) :
    s^2 + t^2/2 + t ≤ 3 * Real.exp (4*x) * x * s := by
  have hx0 : 0 ≤ x := by linarith
  have h1 : s ≤ Real.exp (4*x) := hsup.trans (Real.exp_le_exp.2 (by linarith))
  have hss : s^2 ≤ Real.exp (4*x)*s := by nlinarith [mul_le_mul_of_nonneg_right h1 hs]
  have hks : Real.exp (3*x) ≤ Real.exp (4*x)*s := by
    calc
      _ = Real.exp (4*x)*Real.exp (-x) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hslo (Real.exp_pos _).le
  have ht1 : t ≤ Real.exp (4*x)*s :=
    htup.trans ((Real.exp_le_exp.2 (by linarith : x ≤ 3*x)).trans hks)
  have ht2 : t^2 ≤ Real.exp (4*x)*s := by
    calc
      _ ≤ (Real.exp x)^2 := sq_le_sq₀ ht (Real.exp_pos x).le |>.2 htup
      _ = Real.exp (2*x) := by rw [sq,← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (3*x) := Real.exp_le_exp.2 (by linarith)
      _ ≤ _ := hks
  have hscale := mul_le_mul_of_nonneg_left hx (mul_nonneg (Real.exp_pos (4*x)).le hs)
  nlinarith

lemma optimizer_cross_disjoint_moderate (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : IsOptimizer G w) (S D : Finset V) (hSD : Disjoint S D)
    (hfree : G.CliqueFreeOn (↑S) (k+2)) {x : ℝ} (hx : 1 ≤ x)
    (hslo : Real.exp (-x) ≤ mass w S) (hsup : mass w S ≤ Real.exp x)
    (htup : mass w D ≤ Real.exp x) :
    crossMass G w S D ≤ (8 + 10*(k:ℝ) + (k:ℝ)^2)*x*mass w S := by
  have hwpos := fun v ↦ (optimizer_stationary hw v).1
  have hεhalf : Real.exp (-8*x) ≤ 1/2 := by
    have hl : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
      _ = 1/2 := by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num
  obtain ⟨L,hp,hb,hm,he⟩ := sparse_multipliers_on k G hwpos S hfree (Real.exp_pos (-8*x)) hεhalf
  have h := variational_cross_lottery G hw S D hSD L hp (Real.exp_pos (4*x)).le hb hm he
  have hcancel : (Real.exp (4*x))^2 * Real.exp (-8*x) = 1 := by
    rw [sq,← Real.exp_add,← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  rw [hcancel,one_mul] at h
  have hlog := log_multiplier_le k hx
  have hw0 := fun v ↦ (hwpos v).le
  have hs := mass_nonneg hw0 S
  have ht := mass_nonneg hw0 D
  have hlogs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog (Real.exp_pos (4*x)).le) hs
  have herr := cross_error_le hx hs ht hslo hsup htup
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (4*x))).1
  nlinarith only [h,hlogs,herr]

end CliqueFreeIndependence.WeightedGraph

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

lemma optimizer_cross_disjoint (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : IsOptimizer G w) (S D : Finset V) (hSD : Disjoint S D)
    (hfree : G.CliqueFreeOn (↑S) (k+2)) {x : ℝ} (hx : 1 ≤ x)
    (hsup : mass w S ≤ Real.exp x) (htup : mass w D ≤ Real.exp x) :
    crossMass G w S D ≤ (4*((k:ℝ)+2)^2)*growth x (mass w S) := by
  have hw0 := fun v ↦ (optimizer_stationary hw v).1.le
  have hs := mass_nonneg hw0 S
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hcoeff : 8+10*(k:ℝ)+(k:ℝ)^2 ≤ 4*((k:ℝ)+2)^2 := by nlinarith
  have hcoeff0 : 0 ≤ 8+10*(k:ℝ)+(k:ℝ)^2 := by positivity
  rcases hs.eq_or_lt with hs | hs
  · have hc := crossMass_le_product G hw0 S D
    simpa [← hs] using hc
  by_cases hlo : Real.exp (-x) ≤ mass w S
  · have h := optimizer_cross_disjoint_moderate k G hw S D hSD hfree hx hlo hsup htup
    have hg : x*mass w S ≤ growth x (mass w S) := by
      unfold growth
      nlinarith [mul_nonneg hs.le (le_max_left 0 (Real.log (1/mass w S)))]
    calc
      _ ≤ (8+10*(k:ℝ)+(k:ℝ)^2)*(x*mass w S) := by nlinarith only [h]
      _ ≤ (8+10*(k:ℝ)+(k:ℝ)^2)*growth x (mass w S) := mul_le_mul_of_nonneg_left hg hcoeff0
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (growth_nonneg (by linarith) hs.le)
  · let y := Real.log (1/mass w S)
    have hxy : x ≤ y := by
      have hlog := Real.log_le_log hs (le_of_not_ge hlo)
      rw [Real.log_exp] at hlog
      dsimp [y]
      rw [one_div,Real.log_inv]
      linarith
    have hy : 1 ≤ y := hx.trans hxy
    have hsy : Real.exp (-y) = mass w S := by
      dsimp [y]
      rw [one_div,Real.log_inv,neg_neg,Real.exp_log hs]
    have h := optimizer_cross_disjoint_moderate k G hw S D hSD hfree hy hsy.le
      (hsup.trans (Real.exp_le_exp.2 hxy)) (htup.trans (Real.exp_le_exp.2 hxy))
    have hg : y*mass w S ≤ growth x (mass w S) := by
      unfold growth
      have hmax := le_max_right 0 y
      change y*mass w S ≤ mass w S*(x+max 0 y)
      nlinarith [mul_le_mul_of_nonneg_right hmax hs.le]
    calc
      _ ≤ (8+10*(k:ℝ)+(k:ℝ)^2)*(y*mass w S) := by nlinarith only [h]
      _ ≤ (8+10*(k:ℝ)+(k:ℝ)^2)*growth x (mass w S) := mul_le_mul_of_nonneg_left hg hcoeff0
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (growth_nonneg (by linarith) hs.le)

end CliqueFreeIndependence.WeightedGraph

end

end OAI
