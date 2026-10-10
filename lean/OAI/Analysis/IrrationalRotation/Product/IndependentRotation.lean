import Mathlib.Data.Finsupp.Option
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Invariant233.IndependentRotation

theorem irrational_finsupp_rat_sum {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (c : ι →₀ ℚ) (hc : c ≠ 0) :
    Irrational (c.sum (fun i q => (q : ℝ) * θ i)) := by
  rintro ⟨r, hr⟩
  let l : Option ι →₀ ℚ := c.optionElim (-r)
  have hl : Finsupp.linearCombination ℚ (fun o : Option ι => o.elim 1 θ) l = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_option_index_smul]
    simp only [l, Finsupp.optionElim_apply_eq_elim, Option.elim_none,
      Finsupp.some_optionElim, Option.elim_some, Rat.smul_def, Rat.cast_neg, mul_one]
    linarith
  exact (Finsupp.optionElim_ne_zero_of_right (-r) c hc)
    ((linearIndependent_iff.mp hθ) l hl)

theorem irrational_coordinate {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ)) (i : ι) :
    Irrational (θ i) := by
  simpa using irrational_finsupp_rat_sum hθ (Finsupp.single i 1) (by simp)

theorem irrational_finsupp_int_sum {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (v : ι →₀ ℤ) (hv : v ≠ 0) :
    Irrational (v.sum (fun i n => (n : ℝ) * θ i)) := by
  let c : ι →₀ ℚ := v.mapRange (fun n : ℤ => (n : ℚ)) (by simp)
  have hc : c ≠ 0 := by
    intro h
    apply hv
    ext i
    have hi := DFunLike.congr_fun h i
    dsimp [c] at hi
    exact_mod_cast hi
  have h := irrational_finsupp_rat_sum hθ c hc
  simpa [c, Finsupp.sum_mapRange_index] using h

theorem int_mul_character_ne_integer {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (v : ι →₀ ℤ) (hv : v ≠ 0) (q : ℤ) (hq : q ≠ 0) (n : ℤ) :
    (q : ℝ) * v.sum (fun i k => (k : ℝ) * θ i) ≠ (n : ℝ) :=
  ((irrational_finsupp_int_sum hθ v hv).intCast_mul hq).ne_int n

theorem zsmul_ne_zero_of_irrational {α : ℝ} (hα : Irrational α)
    {n : ℤ} (hn : n ≠ 0) : n • (α : AddCircle (1 : ℝ)) ≠ 0 := by
  intro h
  rw [← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have heq : (n : ℝ) * α = (k : ℝ) := by simpa [zsmul_eq_mul] using hk.symm
  exact (hα.intCast_mul hn).ne_int k heq

theorem product_rotation_free {ι : Type*} [Nonempty ι] {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (n : ℤ) (hn : n ≠ 0) (x : ι → AddCircle (1 : ℝ)) :
    (fun i => x i + n • (θ i : AddCircle (1 : ℝ))) ≠ x := by
  intro h
  let i : ι := Classical.choice inferInstance
  have hi := congrFun h i
  have hz : n • (θ i : AddCircle (1 : ℝ)) = 0 := by
    apply add_left_cancel (a := x i)
    simpa using hi
  exact zsmul_ne_zero_of_irrational (irrational_coordinate hθ i) hn hz

theorem circle_exp_ne_one_of_irrational {α : ℝ} (hα : Irrational α) :
    Circle.exp (2 * Real.pi * α) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp h
  have heq : α = (n : ℝ) := by
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
    simpa only [mul_comm (n : ℝ)] using hn
  exact hα.ne_int n heq

theorem character_eigenvalue_ne_one {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (v : ι →₀ ℤ) (hv : v ≠ 0) (q : ℤ) (hq : q ≠ 0) :
    Circle.exp (2 * Real.pi * ((q : ℝ) * v.sum (fun i k => (k : ℝ) * θ i))) ≠ 1 :=
  circle_exp_ne_one_of_irrational ((irrational_finsupp_int_sum hθ v hv).intCast_mul hq)

end Invariant233.IndependentRotation

end OAI
