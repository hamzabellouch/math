import OAI.NumberTheory.JointDickman.Counting.SamplingTransfer
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! # Exponential moments of the bounded auxiliary-root fluctuations -/

namespace JointDickman
open Finset
open PublishedInputs

theorem exp_le_one_add_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1+x+x^2 := by
  have h := (le_abs_self (Real.exp x-1-x)).trans (Real.abs_exp_sub_one_sub_id_le hx)
  linarith only [h]

theorem bounded_root_centered_mgf {Ω : Type*} [Fintype Ω]
    (w Y : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hwone : (∑ x, w x) = 1)
    {a : ℝ} (ha : 0 ≤ a) (hY : ∀ x, 0 ≤ Y x ∧ Y x ≤ a)
    {σ t : ℝ} (hσ : |σ| ≤ 2) (ht : 0 ≤ t) (hsmall : 2*t*a ≤ 1) :
    finiteExpectation w (fun x => Real.exp (t*(σ*(Y x-finiteExpectation w Y)))) ≤
      Real.exp (4*t^2*a*finiteExpectation w Y) := by
  let μ := finiteExpectation w Y
  have hμ0 : 0 ≤ μ := finiteExpectation_nonneg w Y hw (fun x => (hY x).1)
  have hμa : μ ≤ a := by
    have h := finiteExpectation_mono w hw (fun x => (hY x).2)
    simpa only [finiteExpectation_const w hwone] using h
  have hdelta (x : Ω) : |Y x-μ| ≤ a := by
    rw [abs_le]
    constructor <;> linarith [hY x]
  have harg (x : Ω) : |t*(σ*(Y x-μ))| ≤ 1 := by
    rw [abs_mul,abs_mul,abs_of_nonneg ht]
    calc
      _ ≤ t*(2*a) := mul_le_mul_of_nonneg_left
        (mul_le_mul hσ (hdelta x) (abs_nonneg _) (by norm_num)) ht
      _ ≤ 1 := by nlinarith only [hsmall]
  have hmean : finiteExpectation w (fun x => t*(σ*(Y x-μ))) = 0 := by
    rw [finiteExpectation_const_mul,finiteExpectation_const_mul,finiteExpectation_sub,
      finiteExpectation_const w hwone]
    change t*(σ*(μ-μ)) = 0
    ring
  have hYsq : finiteExpectation w (fun x => Y x^2) ≤ a*μ := by
    have h := finiteExpectation_mono w hw (fun x =>
      show Y x^2 ≤ a*Y x by nlinarith [hY x])
    simpa only [finiteExpectation_const_mul] using h
  have hvar0 : 0 ≤ finiteExpectation w (fun x => (Y x-μ)^2) :=
    finiteExpectation_nonneg w _ hw (fun _ => sq_nonneg _)
  have hvar : finiteExpectation w (fun x => (Y x-μ)^2) ≤ a*μ := by
    rw [finiteExpectation_centered_sq w Y hwone]
    change finiteExpectation w (fun x => Y x^2)-μ^2 ≤ a*μ
    nlinarith only [hYsq,sq_nonneg μ]
  have hσsq : σ^2 ≤ 4 := by nlinarith [sq_abs σ,abs_nonneg σ]
  have hsquare : finiteExpectation w (fun x => (t*(σ*(Y x-μ)))^2) ≤ 4*t^2*a*μ := by
    calc
      _ = (t^2*σ^2)*finiteExpectation w (fun x => (Y x-μ)^2) := by
        simp only [mul_pow,finiteExpectation_const_mul,mul_assoc]
      _ ≤ (t^2*σ^2)*(a*μ) := mul_le_mul_of_nonneg_left hvar (by positivity)
      _ ≤ (t^2*4)*(a*μ) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hσsq (sq_nonneg t)) (mul_nonneg ha hμ0)
      _ = _ := by ring
  have hTaylor := finiteExpectation_mono w hw (fun x => exp_le_one_add_sq (harg x))
  rw [finiteExpectation_add,finiteExpectation_add,finiteExpectation_const w hwone,hmean] at hTaylor
  calc
    _ ≤ 1+4*t^2*a*μ := by linarith only [hTaylor,hsquare]
    _ ≤ Real.exp (4*t^2*a*μ) := by simpa only [add_comm] using Real.add_one_le_exp (4*t^2*a*μ)

end JointDickman

end OAI
