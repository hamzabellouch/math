import Mathlib
import OAI.Analysis.AffineBernstein.FlatTubeEuler
import OAI.Analysis.AffineBernstein.FlatLogCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def flatLogAreaRatio (B : E → Matrix ι ι ℝ) (R : E → Matrix κ κ ℝ) (δ : ℝ) (x : E) : ℝ :=
  δ * (Real.log (B x).det - Real.log (R x).det)

lemma contDiffAt_flatLogAreaRatio {B : E → Matrix ι ι ℝ} {R : E → Matrix κ κ ℝ} {x : E}
    (hB : ContDiffAt ℝ ∞ (fun y i j => B y i j) x)
    (hR : ContDiffAt ℝ ∞ (fun y i j => R y i j) x)
    (hBd : (B x).det ≠ 0) (hRd : (R x).det ≠ 0) (δ : ℝ) :
    ContDiffAt ℝ ∞ (flatLogAreaRatio B R δ) x := by
  have hb := (continuousDetRows (ι := ι)).contDiff.contDiffAt.comp x hB
  have hr := (continuousDetRows (ι := κ)).contDiff.contDiffAt.comp x hR
  exact contDiffAt_const.mul ((hb.log hBd).sub (hr.log hRd))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma flatEulerWeights_exp {B : E → Matrix ι ι ℝ} {R : E → Matrix κ κ ℝ} {x : E}
    (hB : 0 < (B x).det) (hR : 0 < (R x).det) {δ c : ℝ} (hc : δ*c = 1-δ) :
    flatBaseEulerWeight B R δ x = -δ * Real.exp (-c * flatLogAreaRatio B R δ x) ∧
      flatAngularEulerWeight B R δ x = (1-δ) * Real.exp (flatLogAreaRatio B R δ x) := by
  unfold flatBaseEulerWeight flatAngularEulerWeight flatLogAreaRatio
  have heB (p : ℝ) : Real.rpow (B x).det p = Real.exp (Real.log (B x).det * p) :=
    Real.rpow_def_of_pos hB p
  have heR (p : ℝ) : Real.rpow (R x).det p = Real.exp (Real.log (R x).det * p) :=
    Real.rpow_def_of_pos hR p
  rw [heB,heR,heB,heR]
  constructor
  · rw [mul_assoc,← Real.exp_add]
    congr 2
    nlinarith [congrArg (fun t : ℝ => Real.log (B x).det * t) hc,
      congrArg (fun t : ℝ => Real.log (R x).det * t) hc]
  · rw [mul_assoc,← Real.exp_add]
    congr 2
    ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma flatLogAreaRatio_balance {B : E → Matrix ι ι ℝ} {R : E → Matrix κ κ ℝ} {x : E}
    (hB : 0 < (B x).det) (hR : 0 < (R x).det) {δ c : ℝ} (hc : δ*c = 1-δ) :
    (B x).det * Real.exp (-c * flatLogAreaRatio B R δ x) =
      (R x).det * Real.exp (flatLogAreaRatio B R δ x) := by
  conv_lhs => rw [← Real.exp_log hB]
  conv_rhs => rw [← Real.exp_log hR]
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  unfold flatLogAreaRatio
  nlinarith [congrArg (fun t : ℝ => Real.log (B x).det * t) hc,
    congrArg (fun t : ℝ => Real.log (R x).det * t) hc]

lemma matrix_adjugate_entry {A : Matrix ι ι ℝ} (hA : A.det ≠ 0) (i j : ι) :
    A.adjugate i j = A.det * A⁻¹ i j := by
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  rw [← mul_assoc,mul_inv_cancel₀ hA,one_mul]

def flatInverseTrace (A : Matrix ι ι ℝ) (v : ι → E) (f : E → ℝ) (x : E) : ℝ :=
  ∑ j, ∑ i, A⁻¹ i j * dirDeriv (v j) (dirDeriv (v i) f) x

def flatInversePair (A : Matrix ι ι ℝ) (v : ι → E) (f g : E → ℝ) (x : E) : ℝ :=
  ∑ j, ∑ i, A⁻¹ i j * dirDeriv (v j) f x * dirDeriv (v i) g x

/- Exact logarithmic form of the two-block Euler equation. -/
theorem flat_log_euler_of_weighted {W : Set E} (hW : IsOpen W)
    {B : E → Matrix ι ι ℝ} {R : E → Matrix κ κ ℝ}
    (hB : ∀ x ∈ W, ContDiffAt ℝ ∞ (fun y i j => B y i j) x)
    (hR : ∀ x ∈ W, ContDiffAt ℝ ∞ (fun y i j => R y i j) x)
    (hBd : ∀ x ∈ W, 0 < (B x).det) (hRd : ∀ x ∈ W, 0 < (R x).det)
    (v : ι → E) (w : κ → E) {δ c : ℝ} (hc : δ*c = 1-δ)
    (hnz : δ*c ≠ 0) {x : E} (hx : x ∈ W)
    (heuler :
      (∑ j, ∑ i, (B x).adjugate i j * dirDeriv (v j) (dirDeriv (v i) (flatBaseEulerWeight B R δ)) x) +
      (∑ j, ∑ i, (R x).adjugate i j * dirDeriv (w j) (dirDeriv (w i) (flatAngularEulerWeight B R δ)) x) = 0) :
    let t := flatLogAreaRatio B R δ
    flatInverseTrace (B x) v t x - c * flatInversePair (B x) v t t x +
      flatInverseTrace (R x) w t x + flatInversePair (R x) w t t x = 0 := by
  let t := flatLogAreaRatio B R δ
  have ht : ContDiffOn ℝ ∞ t W := fun y hy =>
    (contDiffAt_flatLogAreaRatio (hB y hy) (hR y hy) (ne_of_gt (hBd y hy))
      (ne_of_gt (hRd y hy)) δ).contDiffWithinAt
  have heB : flatBaseEulerWeight B R δ =ᶠ[𝓝 x] (fun y => -δ * Real.exp (-c*t y)) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact (flatEulerWeights_exp (hBd y hy) (hRd y hy) hc).1
  have heR : flatAngularEulerWeight B R δ =ᶠ[𝓝 x] (fun y => (1-δ) * Real.exp (t y)) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact (flatEulerWeights_exp (hBd y hy) (hRd y hy) hc).2
  have hdB (i j : ι) : dirDeriv (v j) (dirDeriv (v i) (flatBaseEulerWeight B R δ)) x =
      δ*c*Real.exp (-c*t x) * (dirDeriv (v j) (dirDeriv (v i) t) x -
        c*dirDeriv (v j) t x*dirDeriv (v i) t x) := by
    rw [second_dirDeriv_congr heB,
      second_dirDeriv_const_mul hW ((contDiffOn_const.mul ht).exp) hx,
      second_dirDeriv_expMul hW ht hx]
    ring
  have hdR (i j : κ) : dirDeriv (w j) (dirDeriv (w i) (flatAngularEulerWeight B R δ)) x =
      δ*c*Real.exp (t x) * (dirDeriv (w j) (dirDeriv (w i) t) x +
        dirDeriv (w j) t x*dirDeriv (w i) t x) := by
    rw [second_dirDeriv_congr heR,second_dirDeriv_const_mul hW ht.exp hx]
    have hh := second_dirDeriv_expMul hW ht hx 1 (w j) (w i)
    simp only [one_mul,one_pow] at hh
    rw [hh,← hc]
    ring
  have hbal := flatLogAreaRatio_balance (hBd x hx) (hRd x hx) hc
  change (B x).det * Real.exp (-c*t x) = (R x).det * Real.exp (t x) at hbal
  have hbcon : (∑ j, ∑ i, (B x).adjugate i j * dirDeriv (v j)
      (dirDeriv (v i) (flatBaseEulerWeight B R δ)) x) =
      (δ*c*(R x).det*Real.exp (t x)) *
        (flatInverseTrace (B x) v t x - c*flatInversePair (B x) v t t x) := by
    unfold flatInverseTrace flatInversePair
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hdB,matrix_adjugate_entry (ne_of_gt (hBd x hx))]
    calc
      _ = δ*c*((B x).det*Real.exp (-c*t x)) *
        ((B x)⁻¹ i j * dirDeriv (v j) (dirDeriv (v i) t) x -
          c*((B x)⁻¹ i j*dirDeriv (v j) t x*dirDeriv (v i) t x)) := by ring
      _ = _ := by rw [hbal]; ring
  have hrcon : (∑ j, ∑ i, (R x).adjugate i j * dirDeriv (w j)
      (dirDeriv (w i) (flatAngularEulerWeight B R δ)) x) =
      (δ*c*(R x).det*Real.exp (t x)) *
        (flatInverseTrace (R x) w t x + flatInversePair (R x) w t t x) := by
    unfold flatInverseTrace flatInversePair
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hdR,matrix_adjugate_entry (ne_of_gt (hRd x hx))]
    ring
  rw [hbcon,hrcon,← mul_add] at heuler
  have hz := (mul_eq_zero.mp heuler).resolve_left
    (mul_ne_zero (mul_ne_zero hnz (ne_of_gt (hRd x hx))) (Real.exp_ne_zero _))
  dsimp only
  dsimp only [t] at hz
  linarith

end AffineBernstein
end

end OAI
