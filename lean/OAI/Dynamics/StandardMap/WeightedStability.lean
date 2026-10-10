import OAI.Dynamics.StandardMap.DirichletOrbit

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma weighted_convolution_difference {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (G : ι → ι → ℝ) (F : ι → ℝ → ℝ) (L ξ ζ : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hL : ∀ i, 0 ≤ L i)
    (hLip : ∀ i, |F i (ξ i)-F i (ζ i)| ≤ L i*|ξ i-ζ i|)
    (hrow : ∀ i, ∑ j, |w i*G i j| *L j/w j ≤ 1/2) :
    ‖fun i => ∑ j, w i*G i j*(F j (ξ j)-F j (ζ j))‖ ≤
      (1/2)*‖fun i => w i*(ξ i-ζ i)‖ := by
  classical
  let N := ‖fun i => w i*(ξ i-ζ i)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hc (j : ι) : |ξ j-ζ j| ≤ N/w j := by
    apply (le_div_iff₀ (hw j)).mpr
    have hh:=norm_le_pi_norm (fun i => w i*(ξ i-ζ i)) j
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (hw j),mul_comm] using hh
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    _ ≤ ∑ j, |w i*G i j| *|F j (ξ j)-F j (ζ j)| := by
      simpa only [Real.norm_eq_abs,abs_mul] using Finset.abs_sum_le_sum_abs
        (fun j => w i*G i j*(F j (ξ j)-F j (ζ j))) Finset.univ
    _ ≤ ∑ j, |w i*G i j| *(L j*(N/w j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left ((hLip j).trans
        (mul_le_mul_of_nonneg_left (hc j) (hL j))) (abs_nonneg _)
    _ = (∑ j, |w i*G i j| *L j/w j)*N := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) hN
lemma weighted_fixedPoint_stability {ι : Type*} [Fintype ι]
    (w U : ι → ℝ) (G : ι → ι → ℝ) (F : ι → ℝ → ℝ) (L ξ ζ : ι → ℝ) (r s C : ℝ)
    (hw : ∀ i, 0 < w i) (hL : ∀ i, 0 ≤ L i)
    (hLip : ∀ i, |F i (ξ i)-F i (ζ i)| ≤ L i*|ξ i-ζ i|)
    (hrow : ∀ i, ∑ j, |w i*G i j| *L j/w j ≤ 1/2)
    (hU : ‖fun i => w i*U i‖ ≤ C)
    (hξ : ∀ i, ξ i=U i*r+∑ j, G i j*F j (ξ j))
    (hζ : ∀ i, ζ i=U i*s+∑ j, G i j*F j (ζ j)) :
    ‖fun i => w i*(ξ i-ζ i)‖ ≤ 2*C*|r-s| := by
  classical
  have hnl:=weighted_convolution_difference w G F L ξ ζ hw hL hLip hrow
  have he : (fun i => w i*(ξ i-ζ i)) =
      (fun i => (r-s)*(w i*U i))+(fun i => ∑ j, w i*G i j*(F j (ξ j)-F j (ζ j))) := by
    funext i
    rw [hξ i,hζ i]
    simp only [Pi.add_apply,mul_add,mul_sub,Finset.mul_sum,Finset.sum_sub_distrib,mul_assoc]
    ring
  have hlin : ‖fun i => (r-s)*(w i*U i)‖ ≤ C*|r-s| := by
    calc
      _ = |r-s| *‖fun i => w i*U i‖ := by
        change ‖(r-s) • (fun i => w i*U i)‖= _
        rw [norm_smul,Real.norm_eq_abs]
      _ ≤ _ := by nlinarith [abs_nonneg (r-s)]
  have ht:=norm_add_le (fun i => (r-s)*(w i*U i))
    (fun i => ∑ j, w i*G i j*(F j (ξ j)-F j (ζ j)))
  rw [← he] at ht
  linarith
end StandardMapEntropy

end OAI
