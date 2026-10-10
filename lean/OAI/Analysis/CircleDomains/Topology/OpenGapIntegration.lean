import OAI.Analysis.CircleDomains.Selection.FiniteGapIntegration
import OAI.Analysis.CircleDomains.Transfer.BoundedScalarFillings

namespace OAI

/-! Endpoint traces supplied by finite energy give the distributional error
for clipped scalar functions and constant fillings of finitely many gaps. -/
open Set Function Filter MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem clipped_integration_by_parts_from_open_gaps
    (n : ℕ) (a b : Fin (n + 1) → ℝ) (f d : ℝ → ℝ)
    (value A : Fin n → ℝ) (φ : ℝ → ℝ) (C : ℝ)
    (hab : ∀ i, a i < b i)
    (hd : ∀ i x, x ∈ Ioo (a i) (b i) → HasDerivAt f (d x) x)
    (hi : ∀ i, IntervalIntegrable d volume (a i) (b i))
    (hφ : ContDiff ℝ 1 φ) (hzero : φ (a 0) = 0) (hone : φ (b (Fin.last n)) = 0)
    (hC : 0 ≤ C) (hA : ∀ i, 0 ≤ A i)
    (hleft : ∀ (i : Fin n) u,
      Tendsto f (𝓝[Ioo (a i.castSucc) (b i.castSucc)] (b i.castSucc)) (𝓝 u) →
      |u - value i| ≤ A i)
    (hright : ∀ (i : Fin n) u,
      Tendsto f (𝓝[Ioo (a i.succ) (b i.succ)] (a i.succ)) (𝓝 u) →
      |value i - u| ≤ A i)
    (hφleft : ∀ i : Fin n, |φ (b i.castSucc)| ≤ C)
    (hφright : ∀ i : Fin n, |φ (a i.succ)| ≤ C) :
    |(∑ i, ((∫ x in a i..b i, clipScalar (f x) * deriv φ x) +
      (∫ x in a i..b i, deriv (clipScalar ∘ f) x * φ x))) +
      (∑ i : Fin n, clipScalar (value i) * (φ (a i.succ) - φ (b i.castSucc)))| ≤
        2 * C * ∑ i, A i := by
  choose g hg heq hl hr using fun i =>
    exists_absolutelyContinuous_extension_of_integrable_derivative (hab i) (hd i) (hi i)
  have hclip (i : Fin (n + 1)) :
      AbsolutelyContinuousOnInterval (clipScalar ∘ g i) (a i) (b i) :=
    clipScalar_lipschitz.comp_absolutelyContinuousOnInterval (hg i)
  have hevent (i : Fin (n + 1)) (x : ℝ) (hx : x ∈ Ioo (a i) (b i)) :
      (clipScalar ∘ g i) =ᶠ[𝓝 x] (clipScalar ∘ f) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    exact congrArg clipScalar (heq i hz)
  have hfun (i : Fin (n + 1)) :
      (∫ x in a i..b i, (clipScalar ∘ g i) x * deriv φ x) =
        ∫ x in a i..b i, clipScalar (f x) * deriv φ x := by
    rw [intervalIntegral.integral_of_le (hab i).le, intervalIntegral.integral_of_le (hab i).le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => congrArg (fun v => v * deriv φ x) (hevent i x hx).eq_of_nhds
  have hderiv (i : Fin (n + 1)) :
      (∫ x in a i..b i, deriv (clipScalar ∘ g i) x * φ x) =
        ∫ x in a i..b i, deriv (clipScalar ∘ f) x * φ x := by
    rw [intervalIntegral.integral_of_le (hab i).le, intervalIntegral.integral_of_le (hab i).le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => congrArg (fun v => v * φ x) (hevent i x hx).deriv_eq
  have hbound := integration_by_parts_with_filled_gaps n a b (fun i => clipScalar ∘ g i)
    (clipScalar ∘ value) A φ C hclip hφ hzero hone hC hA
    (fun i => (by
      have h := clipScalar_lipschitz.dist_le_mul (g i.castSucc (b i.castSucc)) (value i)
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
      exact h.trans (hleft i _ (hr i.castSucc))))
    (fun i => (by
      have h := clipScalar_lipschitz.dist_le_mul (value i) (g i.succ (a i.succ))
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
      exact h.trans (hright i _ (hl i.succ))))
    hφleft hφright
  simp_rw [hfun, hderiv] at hbound
  simpa only [comp_apply] using hbound

end CircleDomainRigidity

end OAI
