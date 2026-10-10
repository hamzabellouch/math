import Mathlib
import OAI.Geometry.HyperbolicGroups.Moment
import OAI.Geometry.HyperbolicGroups.Random

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α : Type*} [Fintype α]

lemma prob_mono (μ : FiniteLaw α) {E F : α → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ a, E a → F a) : μ.prob E ≤ μ.prob F := by
  apply μ.expect_mono
  intro a
  by_cases he : E a
  · simp [he,h a he]
  · simp [he]
    split_ifs <;> norm_num

lemma prob_or_le (μ : FiniteLaw α) (E F : α → Prop) [DecidablePred E] [DecidablePred F] :
    μ.prob (fun a => E a ∨ F a) ≤ μ.prob E + μ.prob F := by
  rw [prob, prob, prob, ← μ.expect_add]
  apply μ.expect_mono
  intro a
  by_cases he : E a <;> by_cases hf : F a <;> simp [he,hf]

lemma bernoulli_centered_exp_le {p t : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (ht : |t| ≤ 1) :
    (1-p)*Real.exp (t*(0-p)) + p*Real.exp (t*(1-p)) ≤ Real.exp (p*t^2) := by
  have he : Real.exp t - 1 - t ≤ t^2 :=
    (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le ht)
  calc
    _ = Real.exp (-t*p) * (1+p*(Real.exp t-1)) := by
      rw [show t*(1-p) = -t*p+t by ring, show t*(0-p) = -t*p by ring, Real.exp_add]
      ring
    _ ≤ Real.exp (-t*p) * Real.exp (p*(Real.exp t-1)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have hh := Real.add_one_le_exp (p*(Real.exp t-1))
      linarith
    _ = Real.exp (p*(Real.exp t-1-t)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he hp.1)

/-- The centered Bernoulli count in a specified trial set. Trials belonging to
other table entries are integrated out, not made dependent. -/
def centeredCount {I : Type*} [Fintype I] (p : I → ℝ) (S : Finset I) (w : I → Bool) : ℝ :=
  ∑ i ∈ S, ((if w i then (1:ℝ) else 0) - p i)

lemma centeredCount_mgf {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (S : Finset I) {t : ℝ} (ht : |t| ≤ 1) :
    (bernoulliProduct p hp).expect (fun w => Real.exp (t*centeredCount p S w)) ≤
      Real.exp ((∑ i ∈ S, p i)*t^2) := by
  classical
  have hx (w : I → Bool) : Real.exp (t*centeredCount p S w) =
      ∏ i, Real.exp (t*(if i ∈ S then (if w i then (1:ℝ) else 0)-p i else 0)) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [centeredCount,Finset.mul_sum,mul_ite,mul_zero]
    simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
  simp_rw [hx]
  rw [bernoulliProduct_expect_product p hp
    (fun i (b : Bool) => Real.exp (t*(if i ∈ S then (if b then (1:ℝ) else 0)-p i else 0)))]
  calc
    _ ≤ ∏ i, Real.exp (if i ∈ S then p i*t^2 else 0) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hp i).2) (Real.exp_pos _).le)
          (mul_nonneg (hp i).1 (Real.exp_pos _).le)
      · intro i _
        by_cases hi : i ∈ S
        · simpa [hi] using bernoulli_centered_exp_le (hp i) ht
        · simp [hi]
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp [Finset.sum_mul]

/-- Two-sided multiplicative Chernoff estimate, with an explicit constant 4.
It suffices for the simultaneous six-letter pair counts. -/
theorem centeredCount_chernoff {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (S : Finset I)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 2) :
    (bernoulliProduct p hp).prob (fun w => ε*(∑ i ∈ S, p i) ≤ |centeredCount p S w|) ≤
      2*Real.exp (-ε^2*(∑ i ∈ S, p i)/4) := by
  classical
  let μ := bernoulliProduct p hp
  let m := ∑ i ∈ S, p i
  let t := ε/2
  have ht : 0 < t := half_pos hε
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have htail (s : ℝ) (hs : |s| = t) :
      μ.prob (fun w => t*ε*m ≤ s*centeredCount p S w) ≤ Real.exp (-ε^2*m/4) := by
    have hh := μ.markov (fun w => Real.exp (s*centeredCount p S w))
      (fun _ => (Real.exp_pos _).le) (Real.exp_pos (t*ε*m))
    have hm := centeredCount_mgf p hp S (show |s| ≤ 1 by rw [hs]; exact ht1)
    have hsq : s^2 = t^2 := by rw [← sq_abs,hs]
    have he : μ.prob (fun w => t*ε*m ≤ s*centeredCount p S w) =
        μ.prob (fun w => Real.exp (t*ε*m) ≤ Real.exp (s*centeredCount p S w)) := by
      congr 1; funext w; exact propext Real.exp_le_exp.symm
    rw [he]
    apply hh.trans
    apply (div_le_div_of_nonneg_right hm (Real.exp_pos _).le).trans
    rw [← Real.exp_sub,hsq]
    apply le_of_eq
    congr 1
    dsimp [t,m]
    ring
  have hu := htail t (abs_of_pos ht)
  have hl := htail (-t) (by rw [abs_neg,abs_of_pos ht])
  have hh : μ.prob (fun w => ε*m ≤ |centeredCount p S w|) ≤
      μ.prob (fun w => t*ε*m ≤ t*centeredCount p S w ∨ t*ε*m ≤ -t*centeredCount p S w) := by
    apply μ.prob_mono
    intro w hw
    rcases le_abs.mp hw with h | h
    · left; nlinarith
    · right; nlinarith
  exact hh.trans ((μ.prob_or_le _ _).trans (by linarith))

end FiniteLaw
end HyperbolicObstruction
end
end

section

end
end

end OAI
