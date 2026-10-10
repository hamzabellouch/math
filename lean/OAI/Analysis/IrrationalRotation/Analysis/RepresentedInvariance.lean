import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplierFields

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Countable ι]

theorem ae_invariance_of_represented
    (b : HilbertBasis ι ℂ E)
    (p T : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (P W : X → E →L[ℂ] E)
    (hp : ∀ f : Lp E 2 μ, p f =ᵐ[μ] fun x => P x (f x))
    (hT : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => W x (f x))
    (hinv : (1 - p) * T * p = 0) :
    ∀ᵐ x ∂μ, (1 - P x) * W x * P x = 0 := by
  have hzero : ∀ f : Lp E 2 μ, (0 : Lp E 2 μ →L[ℂ] Lp E 2 μ) f =ᵐ[μ]
      fun x => ((1 - P x) * W x * P x) (f x) := by
    intro f
    have hfix : T (p f) = p (T (p f)) := by
      have h := congrArg (fun A : Lp E 2 μ →L[ℂ] Lp E 2 μ => A f) hinv
      simpa only [mul_apply_eq_comp, sub_apply,
        one_apply_eq_self, zero_apply, sub_eq_zero] using h
    filter_upwards [hp f, hT (p f), hp (T (p f)), Lp.coeFn_zero E 2 μ]
      with x hpf hTf hpTf h0
    change (0 : Lp E 2 μ) x = _
    rw [h0]
    have heq : W x (P x (f x)) = P x (W x (P x (f x))) := by
      calc
        W x (P x (f x)) = T (p f) x := by rw [hTf, hpf]
        _ = p (T (p f)) x := congrArg (fun g : Lp E 2 μ => g x) hfix
        _ = P x (W x (P x (f x))) := by rw [hpTf, hTf, hpf]
    change (0 : E) = W x (P x (f x)) - P x (W x (P x (f x)))
    exact (sub_eq_zero.mpr heq).symm
  have huniq := field_unique_of_representation b
    (0 : Lp E 2 μ →L[ℂ] Lp E 2 μ) (fun x => (1 - P x) * W x * P x)
    (fun _ => 0) hzero (fun f => by
      filter_upwards [Lp.coeFn_zero E 2 μ] with x hx
      change (0 : Lp E 2 μ) x = (0 : E)
      exact hx)
  exact huniq

end Invariant233.L2Multiplication

end

end OAI
