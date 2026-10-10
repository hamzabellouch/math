import OAI.Analysis.CircleDomains.Topology.OpenGapIntegration
import OAI.Analysis.CircleDomains.Topology.FiniteIntervalSplitting

namespace OAI

/-! The finite-gap estimate as an integral of the actual filled function,
with its ordinary derivative off the finitely many jumps. -/
open Set Function Filter MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem intervalIntegral_congr_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : EqOn f g (Ioo a b)) : (∫ x in a..b, f x) = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

 theorem filled_gap_integration_bound
    (n : ℕ) (a b : Fin (n + 1) → ℝ) (f d F : ℝ → ℝ)
    (value A : Fin n → ℝ) (φ : ℝ → ℝ) (C : ℝ)
    (hab : ∀ i, a i < b i) (hholes : ∀ i : Fin n, b i.castSucc ≤ a i.succ)
    (hd : ∀ i x, x ∈ Ioo (a i) (b i) → HasDerivAt f (d x) x)
    (hi : ∀ i, IntervalIntegrable d volume (a i) (b i))
    (hF : ∀ i, EqOn F (clipScalar ∘ f) (Ioo (a i) (b i)))
    (hfill : ∀ i : Fin n, EqOn F (fun _ => clipScalar (value i))
      (Ioo (b i.castSucc) (a i.succ)))
    (hφ : ContDiff ℝ 1 φ) (hzero : φ (a 0) = 0) (hone : φ (b (Fin.last n)) = 0)
    (hint : Integrable (fun x => F x * deriv φ x))
    (hdint : Integrable (fun x => deriv F x * φ x))
    (hC : 0 ≤ C) (hA : ∀ i, 0 ≤ A i)
    (hleft : ∀ (i : Fin n) u,
      Tendsto f (𝓝[Ioo (a i.castSucc) (b i.castSucc)] (b i.castSucc)) (𝓝 u) →
      |u - value i| ≤ A i)
    (hright : ∀ (i : Fin n) u,
      Tendsto f (𝓝[Ioo (a i.succ) (b i.succ)] (a i.succ)) (𝓝 u) →
      |value i - u| ≤ A i)
    (hφleft : ∀ i : Fin n, |φ (b i.castSucc)| ≤ C)
    (hφright : ∀ i : Fin n, |φ (a i.succ)| ≤ C) :
    |(∫ x in a 0..b (Fin.last n), F x * deriv φ x) +
      (∫ x in a 0..b (Fin.last n), deriv F x * φ x)| ≤ 2 * C * ∑ i, A i := by
  have hgap₁ (i : Fin (n + 1)) :
      (∫ x in a i..b i, F x * deriv φ x) =
        ∫ x in a i..b i, clipScalar (f x) * deriv φ x :=
    intervalIntegral_congr_Ioo (hab i).le fun x hx =>
      congrArg (fun t => t * deriv φ x) (hF i hx)
  have hgap₂ (i : Fin (n + 1)) :
      (∫ x in a i..b i, deriv F x * φ x) =
        ∫ x in a i..b i, deriv (clipScalar ∘ f) x * φ x := by
    apply intervalIntegral_congr_Ioo (hab i).le
    intro x hx
    have he : F =ᶠ[𝓝 x] clipScalar ∘ f := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
      exact hF i hz
    exact congrArg (fun t => t * φ x) he.deriv_eq
  have hhole₁ (i : Fin n) :
      (∫ x in b i.castSucc..a i.succ, F x * deriv φ x) =
        clipScalar (value i) * (φ (a i.succ) - φ (b i.castSucc)) := by
    rw [intervalIntegral_congr_Ioo (hholes i)
      (fun x hx => congrArg (fun t => t * deriv φ x) (hfill i hx)),
      intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hφ.differentiable (by norm_num)).differentiableAt.hasDerivAt)
      ((hφ.continuous_deriv le_rfl).intervalIntegrable _ _)
  have hhole₂ (i : Fin n) :
      (∫ x in b i.castSucc..a i.succ, deriv F x * φ x) = 0 := by
    trans ∫ x in b i.castSucc..a i.succ, (0 : ℝ)
    · apply intervalIntegral_congr_Ioo (hholes i)
      intro x hx
      have he : F =ᶠ[𝓝 x] fun _ => clipScalar (value i) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
        exact hfill i hz
      change deriv F x * φ x = 0
      rw [he.deriv_eq, deriv_const, zero_mul]
    · simp
  rw [← sum_integral_gaps_and_holes n a b (fun x => F x * deriv φ x)
      (fun _ => hint.intervalIntegrable) (fun _ => hint.intervalIntegrable),
    ← sum_integral_gaps_and_holes n a b (fun x => deriv F x * φ x)
      (fun _ => hdint.intervalIntegrable) (fun _ => hdint.intervalIntegrable)]
  simp_rw [hgap₁, hgap₂, hhole₁, hhole₂]
  rw [Finset.sum_const_zero, add_zero, add_right_comm,
    ← Finset.sum_add_distrib]
  exact clipped_integration_by_parts_from_open_gaps n a b f d value A φ C
    hab hd hi hφ hzero hone hC hA hleft hright hφleft hφright

end CircleDomainRigidity

end OAI
