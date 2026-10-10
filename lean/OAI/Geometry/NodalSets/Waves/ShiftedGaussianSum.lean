import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace OAI

namespace Yau.Probability
open scoped BigOperators
noncomputable section

lemma summable_integer_exponential {a : ℝ} (ha : 0 < a) :
    Summable (fun z : ℤ ↦ Real.exp (-a * |(z:ℝ)|)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa [mul_comm] using
    (Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos ha))

lemma shifted_square_lower (x : ℝ) (z : ℤ) :
    |((z-⌊x⌋ : ℤ):ℝ)| ≤ (x-(z:ℝ))^2+2 := by
  have h0 := Int.floor_le x
  have h1 := Int.lt_floor_add_one x
  have ht : |((z-⌊x⌋ : ℤ):ℝ)| ≤ |(z:ℝ)-x|+|x-(⌊x⌋:ℝ)| := by
    simpa only [Int.cast_sub,sub_add_sub_cancel] using abs_add_le ((z:ℝ)-x) (x-(⌊x⌋:ℝ))
  rw [abs_of_nonneg (by linarith : 0 ≤ x-(⌊x⌋:ℝ))] at ht
  nlinarith [sq_nonneg (|(z:ℝ)-x|-1),sq_abs ((z:ℝ)-x)]

theorem finite_shifted_gaussian_sum {a : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∀ (x : ℝ) (s : Finset ℤ),
      ∑ z ∈ s, Real.exp (-a*(x-(z:ℝ))^2) ≤ C := by
  let f : ℤ → ℝ := fun z ↦ Real.exp (-a*|(z:ℝ)|)
  have hf : Summable f := summable_integer_exponential ha
  have hsum : 0 < ∑' z, f z := (lt_of_lt_of_le (Real.exp_pos _) (hf.le_tsum 0 (fun _ _ ↦ Real.exp_nonneg _)))
  refine ⟨Real.exp (2*a)*(∑' z, f z),mul_pos (Real.exp_pos _) hsum,?_⟩
  intro x s
  calc
    _ ≤ ∑ z ∈ s, Real.exp (2*a)*f (z-⌊x⌋) := by
      apply Finset.sum_le_sum
      intro z _
      dsimp [f]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (shifted_square_lower x z) ha.le
      nlinarith
    _ = Real.exp (2*a)*∑ z ∈ s.image (fun z ↦ z-⌊x⌋), f z := by
      rw [Finset.mul_sum,Finset.sum_image]
      intro u _ v _ huv
      exact sub_left_injective huv
    _ ≤ Real.exp (2*a)*(∑' z, f z) := by
      gcongr
      exact hf.sum_le_tsum _ (fun _ _ ↦ Real.exp_nonneg _)

theorem finite_shifted_gaussian_sum_pi {d : ℕ} {a : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∀ (x : Fin d → ℝ) (s : Finset (Fin d → ℤ)),
      ∑ z ∈ s, Real.exp (-a*∑ i, (x i-(z i:ℝ))^2) ≤ C := by
  classical
  obtain ⟨C,hC,hb⟩ := finite_shifted_gaussian_sum ha
  refine ⟨C^d,pow_pos hC d,?_⟩
  intro x s
  let t : Fin d → Finset ℤ := fun i ↦ s.image (fun z ↦ z i)
  have hsub : s ⊆ Fintype.piFinset t := by
    intro z hz
    exact Fintype.mem_piFinset.mpr (fun i ↦ Finset.mem_image.mpr ⟨z,hz,rfl⟩)
  calc
    _ = ∑ z ∈ s, ∏ i, Real.exp (-a*(x i-(z i:ℝ))^2) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum,Real.exp_sum]
    _ ≤ ∑ z ∈ Fintype.piFinset t, ∏ i, Real.exp (-a*(x i-(z i:ℝ))^2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ = ∏ i, ∑ z ∈ t i, Real.exp (-a*(x i-(z:ℝ))^2) :=
      (Finset.prod_univ_sum t (fun i z ↦ Real.exp (-a*(x i-(z:ℝ))^2))).symm
    _ ≤ ∏ _i : Fin d, C := by
      apply Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
      intro i _
      exact hb (x i) (t i)
    _ = C^d := by simp

end
end Yau.Probability

end OAI
