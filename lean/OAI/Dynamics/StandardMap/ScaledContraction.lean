import OAI.Dynamics.StandardMap.FixedPointContinuity

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma weighted_dirichlet_contraction {ι : Type*} [Fintype ι]
    (w U : ι → ℝ) (G : ι → ι → ℝ) (F : ι → ℝ → ℝ) (L : ι → ℝ) (r R : ℝ)
    (hw : ∀ i, 0 < w i) (hL : ∀ i, 0 ≤ L i)
    (hLip : ∀ i x y, |x| ≤ R/w i → |y| ≤ R/w i → |F i x-F i y| ≤ L i*|x-y|)
    (hrow : ∀ i, ∑ j, |w i*G i j| *L j/w j ≤ 1/2)
    (X Y : ι → ℝ) (hX : ‖X‖ ≤ R) (hY : ‖Y‖ ≤ R) :
    ‖(fun i => w i*U i*r+∑ j, w i*G i j*F j (X j/w j))-
      (fun i => w i*U i*r+∑ j, w i*G i j*F j (Y j/w j))‖ ≤ (1/2)*‖X-Y‖ := by
  classical
  have hcoord (Z : ι → ℝ) (hZ : ‖Z‖ ≤ R) (i : ι) : |Z i/w i| ≤ R/w i := by
    rw [abs_div,abs_of_pos (hw i)]
    exact div_le_div_of_nonneg_right ((norm_le_pi_norm Z i).trans hZ) (hw i).le
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hc (j : ι) : |X j/w j-Y j/w j| ≤ ‖X-Y‖/w j := by
    rw [← sub_div,abs_div,abs_of_pos (hw j)]
    exact div_le_div_of_nonneg_right (norm_le_pi_norm (X-Y) j) (hw j).le
  calc
    _ = |∑ j, w i*G i j*(F j (X j/w j)-F j (Y j/w j))| := by
      simp only [Pi.sub_apply,Real.norm_eq_abs,add_sub_add_left_eq_sub,← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ ∑ j, |w i*G i j| *|F j (X j/w j)-F j (Y j/w j)| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun j => w i*G i j*(F j (X j/w j)-F j (Y j/w j))) Finset.univ
    _ ≤ ∑ j, |w i*G i j| *(L j*(‖X-Y‖/w j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left ((hLip j _ _ (hcoord X hX j) (hcoord Y hY j)).trans
        (mul_le_mul_of_nonneg_left (hc j) (hL j))) (abs_nonneg _)
    _ = (∑ j, |w i*G i j| *L j/w j)*‖X-Y‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)

lemma continuousOn_weighted_fixedPoints {α ι : Type*} [TopologicalSpace α] [Fintype ι]
    (s : Set α) (w : ι → ℝ) (U : α → ι → ℝ) (G : α → ι → ι → ℝ)
    (F : α → ι → ℝ → ℝ) (L : ι → ℝ) (r : α → ℝ) (R : ℝ)
    (ξ : α → ι → ℝ) (hw : ∀ i, 0 < w i) (hR : 0 ≤ R) (hL : ∀ i, 0 ≤ L i)
    (hξb : ∀ a ∈ s, ∀ i, |ξ a i| ≤ R/w i)
    (hξ : ∀ a ∈ s, ∀ i, ξ a i=U a i*r a+∑ j, G a i j*F a j (ξ a j))
    (hLip : ∀ a ∈ s, ∀ i x y, |x| ≤ R/w i → |y| ≤ R/w i → |F a i x-F a i y| ≤ L i*|x-y|)
    (hrow : ∀ a ∈ s, ∀ i, ∑ j, |w i*G a i j| *L j/w j ≤ 1/2)
    (hUc : ∀ i, ContinuousOn (fun a => U a i) s)
    (hGc : ∀ i j, ContinuousOn (fun a => G a i j) s)
    (hFc : ∀ i x, ContinuousOn (fun a => F a i x) s)
    (hrc : ContinuousOn r s) : ContinuousOn ξ s := by
  classical
  let T : α → (ι → ℝ) → (ι → ℝ) := fun a X i =>
    w i*U a i*r a+∑ j, w i*G a i j*F a j (X j/w j)
  let p : α → (ι → ℝ) := fun a i => w i*ξ a i
  have hp : ContinuousOn p s := by
    apply continuousOn_contractive_fixedPoints s {X | ‖X‖ ≤ R} T p
    · intro a ha
      apply (pi_norm_le_iff_of_nonneg hR).mpr
      intro i
      change |w i*ξ a i| ≤ R
      rw [abs_mul,abs_of_pos (hw i)]
      simpa only [mul_comm] using (le_div_iff₀ (hw i)).mp (hξb a ha i)
    · intro a ha
      funext i
      dsimp only [T,p]
      simp only [mul_div_cancel_left₀ _ (hw _).ne']
      rw [hξ a ha i,mul_add,Finset.mul_sum]
      rw [mul_assoc]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · intro a ha X hX Y hY
      exact weighted_dirichlet_contraction w (U a) (G a) (F a) L (r a) R hw hL
        (hLip a ha) (hrow a ha) X Y hX hY
    · intro X hX
      apply continuousOn_pi.mpr
      intro i
      exact ((continuousOn_const.mul (hUc i)).mul hrc).add
        (continuousOn_finsetSum _ (fun j _ =>
          (continuousOn_const.mul (hGc i j)).mul (hFc j (X j/w j))))
  apply continuousOn_pi.mpr
  intro i
  have hi := (continuousOn_pi.mp hp i).div_const (w i)
  simpa only [p,mul_div_cancel_left₀ _ (hw i).ne'] using hi
end StandardMapEntropy

end OAI
