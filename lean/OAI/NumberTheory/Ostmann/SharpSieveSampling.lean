import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace OAI

open scoped BigOperators
open Set MeasureTheory
namespace Ostmann

theorem sampling_point_bound (F G : ℝ → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hderiv : ∀ x, HasDerivAt F (G x) x) (a δ : ℝ) (hδ : 0 ≤ δ) :
    δ * F a ≤ (∫ t in a..a + δ, F t) + δ * (∫ t in a..a + δ, |G t|) := by
  have had : a ≤ a + δ := by linarith
  have hpoint (x : ℝ) (hx : x ∈ Icc a (a + δ)) :
      F a ≤ F x + (∫ t in a..a + δ, |G t|) := by
    have heq : (∫ t in a..x, G t) = F x - F a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
        (hG.intervalIntegrable a x)
    have hnorm : F a - F x ≤ (∫ t in a..a + δ, |G t|) := calc
      F a - F x ≤ |F a - F x| := le_abs_self _
      _ = |F x - F a| := abs_sub_comm _ _
      _ = |∫ t in a..x, G t| := congrArg abs heq.symm
      _ ≤ ∫ t in a..x, |G t| := intervalIntegral.abs_integral_le_integral_abs hx.1
      _ ≤ ∫ t in a..a + δ, |G t| :=
        intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
          (Filter.Eventually.of_forall (fun t => abs_nonneg (G t)))
          (hG.abs.intervalIntegrable a (a + δ))
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) had
    (intervalIntegrable_const (c := F a))
    ((hF.add continuous_const).intervalIntegrable a (a + δ)) hpoint
  simpa only [Pi.add_apply, intervalIntegral.integral_const, sub_self, add_sub_cancel_left, smul_eq_mul,
    intervalIntegral.integral_add (hF.intervalIntegrable a (a + δ))
      (intervalIntegrable_const (c := ∫ t in a..a + δ, |G t|))] using hi

theorem separated_integral_sum_le {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ |θ i - θ j|)
    (F : ℝ → ℝ) (hF : Continuous F)
    (hF₀ : ∀ x ∈ Icc (0 : ℝ) 2, 0 ≤ F x) :
    (∑ i, ∫ t in θ i..θ i + δ, F t) ≤ ∫ t in (0 : ℝ)..2, F t := by
  have hdisj : Pairwise (fun i j => Disjoint (Ioc (θ i) (θ i + δ)) (Ioc (θ j) (θ j + δ))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have ht : |θ i - θ j| < δ := by
      apply abs_lt.mpr
      constructor <;> linarith [hxi.1, hxi.2, hxj.1, hxj.2]
    exact (not_lt_of_ge (hsep i j hij)) ht
  have hsub : (⋃ i, Ioc (θ i) (θ i + δ)) ⊆ Ioc (0 : ℝ) 2 := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    constructor <;> linarith [(hθ i).1, (hθ i).2, hi.1, hi.2]
  have heq (i : ι) : (∫ t in θ i..θ i + δ, F t) =
      ∫ t in Ioc (θ i) (θ i + δ), F t :=
    intervalIntegral.integral_of_le (by linarith)
  simp_rw [heq]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← integral_iUnion_fintype (fun i => measurableSet_Ioc) hdisj
    (fun i => (hF.intervalIntegrable (θ i) (θ i + δ)).1)]
  exact setIntegral_mono_set (hF.intervalIntegrable 0 2).1
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => hF₀ x ⟨hx.1.le, hx.2⟩))
    hsub.eventuallySubset

theorem separated_sampling_bound {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ |θ i - θ j|)
    (F G : ℝ → ℝ) (hF : Continuous F) (hG : Continuous G)
    (hderiv : ∀ x, HasDerivAt F (G x) x)
    (hF₀ : ∀ x ∈ Icc (0 : ℝ) 2, 0 ≤ F x) :
    δ * (∑ i, F (θ i)) ≤ (∫ t in (0 : ℝ)..2, F t) +
      δ * (∫ t in (0 : ℝ)..2, |G t|) := by
  calc
    δ * (∑ i, F (θ i)) = ∑ i, δ * F (θ i) := Finset.mul_sum _ _ _
    _ ≤ ∑ i, ((∫ t in θ i..θ i + δ, F t) + δ * (∫ t in θ i..θ i + δ, |G t|)) :=
      Finset.sum_le_sum (fun i _ => sampling_point_bound F G hF hG hderiv (θ i) δ hδ)
    _ = (∑ i, ∫ t in θ i..θ i + δ, F t) +
        δ * (∑ i, ∫ t in θ i..θ i + δ, |G t|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (∫ t in (0 : ℝ)..2, F t) + δ * (∫ t in (0 : ℝ)..2, |G t|) :=
      add_le_add (separated_integral_sum_le θ δ hδ hδ₁ hθ hsep F hF hF₀)
        (mul_le_mul_of_nonneg_left
          (separated_integral_sum_le θ δ hδ hδ₁ hθ hsep (fun t => |G t|) hG.abs
            (fun t _ => abs_nonneg (G t))) hδ)

end Ostmann

end OAI
