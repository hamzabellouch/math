import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductGaussWindow
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductWindowSum

namespace OAI

/-! The complete smooth Mellin complement of the Gauss polynomial follows
from the actual localized estimates and convergent smooth-window summation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem schwartz_gauss_complement_log_saving
    (hpnt : PrimaryPrimePNT) {C Mα Mβ M : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ) (hM : 0 ≤ M)
    (j dα dβ a : ℕ) (f : SchwartzMap ℝ ℂ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (P B : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ S : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^2*(1+Real.log Z)^(3*a) → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ S →
      (∀ n ∈ P, primary n ∧ 1 ≤ norm n/A ∧ norm n/A ≤ 2) →
      (∀ n ∈ B, primary n ∧ Squarefree n ∧ Z/2 ≤ norm n ∧ norm n ≤ Z) →
      (∀ n ∈ B, ‖β n‖ ≤ M) →
      (∑ n ∈ P, ‖α n‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ n ∈ B, ‖β n‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ‖∫ t : ℝ, (1-(heightPartitionBump (t/S):ℂ))*f t*
        Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
        ∑ c ∈ P, ∑ b ∈ B, α c*β b*gauss (c*b)*normTwist t (c*b)‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(S*(1+Real.log Z)^j) := by
  obtain ⟨K,Ct,hK,hbound⟩ := schwartz_gauss_window_log_saving hpnt hMV hC hHuxley
    hMα hMβ hM j dα dβ a f
  refine ⟨3*K,Ct,by positivity,?_⟩
  intro P B α β Z A X₀ S hZ hA hAu hX₀ hS hP hB hβ hαE hβE
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hS0 : 0 < S := (pow_pos hL Ct).trans_le hS
  have hAp : 0 < A := (by positivity : 0 < 2*Z^(3/2:ℝ)).trans_le hA
  let Q := fun t : ℝ => ∑ c ∈ P, ∑ b ∈ B, α c*β b*gauss (c*b)*normTwist t (c*b)
  let phase := fun t : ℝ => Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)
  let F := fun t : ℝ => f t*(phase t*Q t)
  have hi : Integrable F := by
    apply f.integrable.mul_bdd (c := ∑ c ∈ P, ∑ b ∈ B, ‖α c*β b*gauss (c*b)‖)
    · have hc : Continuous (fun t => phase t*Q t) := by
        have hq : Continuous Q := by
          dsimp only [Q]
          apply continuous_finsetSum
          intro c hc
          apply continuous_finsetSum
          intro b hb
          exact continuous_const.mul (continuous_normTwist (c*b))
        exact (show Continuous phase by dsimp only [phase]; fun_prop).mul hq
      exact hc.aestronglyMeasurable
    · filter_upwards with t
      rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
      dsimp only [Q]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro c hc
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul,norm_normTwist,mul_one]
  have hwindow (n : ℕ) :
      ‖∫ t : ℝ, heightWindow (S*(3/2:ℝ)^n) t*F t‖ ≤
        (K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j)/(S*(3/2:ℝ)^n) := by
    have ht : (1+Real.log Z)^Ct ≤ S*(3/2:ℝ)^n :=
      hS.trans (le_mul_of_one_le_right hS0.le (one_le_pow₀ (by norm_num)))
    have hh := hbound P B α β Z A X₀ (S*(3/2:ℝ)^n)
      hZ hA hAu hX₀ ht hP hB hβ hαE hβE
    have he : (fun t => heightWindow (S*(3/2:ℝ)^n) t*F t) =
        fun t => (f t*heightWindow (S*(3/2:ℝ)^n) t)*phase t*Q t := by
      funext t
      dsimp only [F]
      ring
    rw [he]
    convert hh using 1; ring
  have hb := height_window_complement_bound F hi hS0
    (show 0 ≤ K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j by positivity) hwindow
  have he : (fun t => (1-(heightPartitionBump (t/S):ℂ))*F t) =
      fun t => (1-(heightPartitionBump (t/S):ℂ))*f t*phase t*Q t := by
    funext t
    dsimp only [F]
    ring
  rw [he] at hb
  convert hb using 1; ring

end CubicFirstMoment

end

end OAI
