import Mathlib.Analysis.InnerProductSpace.Calculus
import OAI.NumberTheory.Ostmann.SharpSieveEnergy
import OAI.NumberTheory.Ostmann.SharpSieveSampling

namespace OAI

open scoped BigOperators RealInnerProductSpace
open Set MeasureTheory
namespace Ostmann.HybridSieve

theorem separated_integral_sum_le_on {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (δ A B : ℝ) (hδ : 0 ≤ δ) (hAB : A ≤ B)
    (hθ : ∀ i, A ≤ θ i ∧ θ i + δ ≤ B)
    (hsep : ∀ i j, i ≠ j → δ ≤ |θ i - θ j|)
    (F : ℝ → ℝ) (hF : Continuous F) (hF₀ : ∀ x, 0 ≤ F x) :
    (∑ i, ∫ t in θ i..θ i + δ, F t) ≤ ∫ t in A..B, F t := by
  have hdisj : Pairwise (fun i j => Disjoint (Ioc (θ i) (θ i + δ)) (Ioc (θ j) (θ j + δ))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have ht : |θ i - θ j| < δ := by
      apply abs_lt.mpr
      constructor <;> linarith [hxi.1, hxi.2, hxj.1, hxj.2]
    exact (not_lt_of_ge (hsep i j hij)) ht
  have hsub : (⋃ i, Ioc (θ i) (θ i + δ)) ⊆ Ioc A B := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    constructor <;> linarith [(hθ i).1, (hθ i).2, hi.1, hi.2]
  have heq (i : ι) : (∫ t in θ i..θ i + δ, F t) =
      ∫ t in Ioc (θ i) (θ i + δ), F t :=
    intervalIntegral.integral_of_le (by linarith)
  simp_rw [heq]
  rw [intervalIntegral.integral_of_le hAB]
  rw [← integral_iUnion_fintype (fun i => measurableSet_Ioc) hdisj
    (fun i => (hF.intervalIntegrable (θ i) (θ i + δ)).1)]
  exact setIntegral_mono_set (hF.intervalIntegrable A B).1
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x _ => hF₀ x)) hsub.eventuallySubset

theorem separated_sampling_bound_on {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (δ A B : ℝ) (hδ : 0 ≤ δ) (hAB : A ≤ B)
    (hθ : ∀ i, A ≤ θ i ∧ θ i + δ ≤ B)
    (hsep : ∀ i j, i ≠ j → δ ≤ |θ i - θ j|)
    (F G : ℝ → ℝ) (hF : Continuous F) (hG : Continuous G)
    (hderiv : ∀ x, HasDerivAt F (G x) x) (hF₀ : ∀ x, 0 ≤ F x) :
    δ * (∑ i, F (θ i)) ≤ (∫ t in A..B, F t) + δ * (∫ t in A..B, |G t|) := by
  calc
    δ * (∑ i, F (θ i)) = ∑ i, δ * F (θ i) := Finset.mul_sum _ _ _
    _ ≤ ∑ i, ((∫ t in θ i..θ i + δ, F t) + δ * (∫ t in θ i..θ i + δ, |G t|)) :=
      Finset.sum_le_sum (fun i _ => Ostmann.sampling_point_bound F G hF hG hderiv (θ i) δ hδ)
    _ = (∑ i, ∫ t in θ i..θ i + δ, F t) +
        δ * (∑ i, ∫ t in θ i..θ i + δ, |G t|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add
      (separated_integral_sum_le_on θ δ A B hδ hAB hθ hsep F hF hF₀)
      (mul_le_mul_of_nonneg_left
        (separated_integral_sum_le_on θ δ A B hδ hAB hθ hsep (fun t => |G t|)
          hG.abs (fun t => abs_nonneg (G t))) hδ)

theorem separated_complex_samples_le_integral {ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (H : ℝ) (hH : 1 ≤ H)
    (hγ : ∀ j, |γ j| ≤ H) (hsep : ∀ j k, j ≠ k → 1 ≤ |γ j - γ k|)
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hderiv : ∀ t, HasDerivAt f (g t) t) :
    (∑ j, ‖f (γ j)‖ ^ 2) ≤
      2 * (∫ t in Icc (-2 * H) (2 * H), ‖f t‖ ^ 2) +
        (∫ t in Icc (-2 * H) (2 * H), ‖g t‖ ^ 2) := by
  have hab : -2 * H ≤ 2 * H := by linarith
  have hγ' : ∀ j, -2 * H ≤ γ j ∧ γ j + 1 ≤ 2 * H := by
    intro j
    have h := abs_le.mp (hγ j)
    constructor <;> linarith
  have hs := separated_sampling_bound_on γ 1 (-2 * H) (2 * H) (by norm_num)
    hab hγ' hsep (fun t => ‖f t‖ ^ 2) (fun t => 2 * inner ℝ (f t) (g t))
    (hf.norm.pow 2) ((hf.inner hg).const_mul 2) (fun t => (hderiv t).norm_sq)
    (fun t => sq_nonneg _)
  have hv := Ostmann.integral_abs_two_inner_le_energy f g hf hg hab (by norm_num : (0 : ℝ) < 1)
  simp only [one_mul, inv_one] at hs hv
  simp only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hs hv
  linarith

end Ostmann.HybridSieve

end OAI
