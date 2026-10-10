import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI


noncomputable section
namespace ScalarConductivity
open Finset

variable {V : Type*} [NormedAddCommGroup V]

theorem finite_moment_transfers (n : ℕ) (b : ℕ → V)
    (hz : ∑ j ∈ range n,b j=0) :
    ∃ a : ℕ → V,a 0=0 ∧ a n=0 ∧
      (∀ i<n,a (i+1)-a i=b i) ∧
      (∀ i≤n,‖a i‖≤∑ j ∈ range n,‖b j‖) := by
  let a := fun i => ∑ j ∈ range i,b j
  refine ⟨a,by simp [a],hz,?_,?_⟩
  · intro i _
    dsimp only [a]
    rw [sum_range_succ,add_sub_cancel_left]
  · intro i hi
    apply (norm_sum_le _ _).trans
    exact sum_le_sum_of_subset_of_nonneg (range_mono hi) (fun _ _ _ => norm_nonneg _)

end ScalarConductivity



namespace ScalarConductivity
open Set

variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fixed_smooth_tests_bound (g : ι → E → F)
    (hg : ∀ i,ContDiff ℝ (↑(⊤ : ℕ∞)) (g i))
    (hs : ∀ i,HasCompactSupport (g i)) (m : ℕ) :
    ∃ B : ℝ,0<B ∧ ∀ (a : ι → ℝ) (A : ℝ),0≤A →
      (∀ i,‖a i‖≤A) → ∀ x : E,
        ‖iteratedFDeriv ℝ m (fun y => ∑ i,a i • g i y) x‖≤B*A := by
  have hmn : (m : WithTop ℕ∞)≤↑(⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hn (i : ι) : ContDiff ℝ m (g i) := (hg i).of_le hmn
  choose C hC using fun i => (hs i).iteratedFDeriv m |>.exists_bound_of_continuous
    ((hg i).continuous_iteratedFDeriv hmn)
  have hC₀ (i : ι) : 0≤C i := (norm_nonneg _).trans (hC i 0)
  have hsum : 0≤∑ i,C i := Finset.sum_nonneg (fun i _ => hC₀ i)
  refine ⟨(∑ i,C i)+1,by linarith,?_⟩
  intro a A hA ha x
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((hn i).const_smul (a i)).contDiffAt)]
  simp_rw [iteratedFDeriv_const_smul_apply' (hn _).contDiffAt]
  calc
    _≤∑ i,‖a i • iteratedFDeriv ℝ m (g i) x‖ := norm_sum_le _ _
    _≤∑ i,A*C i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (ha i) (hC i x) (norm_nonneg _) hA
    _≤((∑ i,C i)+1)*A := by
      rw [←Finset.mul_sum]
      nlinarith

end ScalarConductivity

end

end OAI
