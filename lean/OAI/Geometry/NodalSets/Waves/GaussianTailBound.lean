import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Yau.Probability
open Filter
open scoped BigOperators Topology
noncomputable section

lemma finite_gaussian_tail {ι : Type*} [Fintype ι] (d f : ι → ℝ)
    {a R B r : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hd : ∀ i, 0 ≤ d i) (hf : ∀ i, f i ≤ R*Real.exp (-2*a*(d i)^2))
    (hs : ∑ i, Real.exp (-a*(d i)^2) ≤ B) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ r < d i), f i ≤
      R*B*Real.exp (-a*r^2) := by
  classical
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ r < d i),
        (R*Real.exp (-a*r^2))*Real.exp (-a*(d i)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hri := (Finset.mem_filter.mp hi).2.le
      apply (hf i).trans
      simp only [mul_assoc,← Real.exp_add]
      gcongr
      have hh := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hr (hd i)).2 hri) ha
      nlinarith
    _ ≤ ∑ i, (R*Real.exp (-a*r^2))*Real.exp (-a*(d i)^2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ ↦ by positivity)
    _ = (R*Real.exp (-a*r^2))*∑ i, Real.exp (-a*(d i)^2) := by rw [Finset.mul_sum]
    _ ≤ (R*Real.exp (-a*r^2))*B := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

lemma main_center_scale (N : ℝ) (hN : 0 < N) :
    N*(N^(-5/12:ℝ))^2 = N^(1/6:ℝ) := by
  calc
    _ = N^(1:ℝ)*N^(-5/6:ℝ) := by
      rw [← Real.rpow_mul_natCast hN.le]
      norm_num
    _ = _ := by rw [← Real.rpow_add hN]; norm_num

lemma tendsto_main_center_tail (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ Real.exp (-a*(n:ℝ)^(1/6:ℝ))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ (n:ℝ)^(1/6:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/6)).comp tendsto_natCast_atTop_atTop
  exact Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos ha)).mpr hpow)

end
end Yau.Probability

end OAI
