import OAI.NumberTheory.JointDickman.Amplification.FiniteProductMGF

namespace OAI

/-! # Discharge of the finite-product McDiarmid input -/
namespace JointDickman
open Finset PublishedInputs

theorem finiteProbability_le_one {A : Type*} [Fintype A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hone : ∑ a, w a = 1) (E : A → Prop) :
    finiteProbability w E ≤ 1 := by
  classical
  rw [← hone]
  apply sum_le_sum
  intro a _
  by_cases ha : E a <;> simp [ha,hw a]

theorem finite_chernoff_bound {A : Type*} [Fintype A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (f : A → ℝ) (a : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    finiteProbability w (fun x => a < f x) ≤
      Real.exp (-t*a) * finiteExpectation w (fun x => Real.exp (t*f x)) := by
  classical
  calc
    _ ≤ ∑ x, w x * (Real.exp (-t*a) * Real.exp (t*f x)) := by
      apply sum_le_sum
      intro x _
      by_cases hx : a < f x
      · simp only [hx,ite_true]
        have he : 1 ≤ Real.exp (-t*a) * Real.exp (t*f x) := by
          rw [← Real.exp_add,Real.one_le_exp_iff]
          have := mul_nonneg ht (sub_nonneg.mpr hx.le)
          nlinarith
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he (hw x)
      · simp only [hx,ite_false]
        exact mul_nonneg (hw x) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by simp only [finiteExpectation,mul_sum]; apply sum_congr rfl; intro x _; ring

theorem finiteMcDiarmidInput {A : Type*} [Fintype A] [DecidableEq A] (n : ℕ) :
    FiniteMcDiarmidInput (Fin n) A := by
  intro p hp hone f c hc hlip a ha
  have hw (x : Fin n → A) : 0 ≤ siteProductMass p x :=
    prod_nonneg (fun i _ => hp i (x i))
  by_cases hden : (n : ℝ)*c^2 = 0
  · rw [show -2*a^2/((Fintype.card (Fin n) : ℝ)*c^2) = 0 by simp [hden]]
    rw [Real.exp_zero]
    exact finiteProbability_le_one _ hw (siteProductMass_sum_one n p hone) _
  · have hdpos : 0 < (n : ℝ)*c^2 := lt_of_le_of_ne (by positivity) (Ne.symm hden)
    let t : ℝ := 4*a/((n : ℝ)*c^2)
    have ht : 0 ≤ t := (div_pos (by positivity) hdpos).le
    have hmgf := finite_product_mgf n p hp hone f hc hlip t
    calc
      _ ≤ Real.exp (-t*a) * finiteExpectation (siteProductMass p)
          (fun x => Real.exp (t*(f x-finiteExpectation (siteProductMass p) f))) :=
        finite_chernoff_bound _ hw _ a ht
      _ ≤ Real.exp (-t*a) * Real.exp ((n : ℝ)*c^2*t^2/8) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        simp only [Fintype.card_fin]
        dsimp [t]
        field_simp
        ring

end JointDickman

end OAI
