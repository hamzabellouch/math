import OAI.Analysis.IrrationalRotation.Model.ConditionalConvolution
import OAI.Analysis.IrrationalRotation.Analysis.PointwiseConvolution

namespace OAI

open scoped ComplexConjugate ENNReal lp

namespace InvariantProjection.ConditionalConvolution

theorem tsum_omittedEvent {Ω : Type*} (H : ℤ → Set Ω) (K n : ℕ)
    (ω : Ω) (w : ℤ → ℝ) :
    (∑' v : ↑(((window K n) : Set ℤ)ᶜ),
      (H (selector K n v)).indicator (fun _ => (1 : ℝ)) ω * w v) =
    ∑' v : ℤ, (omittedEvent H K n v).indicator (fun _ => (1 : ℝ)) ω * w v := by
  classical
  rw [tsum_subtype (((window K n) : Set ℤ)ᶜ)
    (fun v : ℤ => (H (selector K n v)).indicator (fun _ => (1 : ℝ)) ω * w v)]
  apply tsum_congr
  intro v
  by_cases hv : v ∈ window K n <;> simp [omittedEvent, hv]

theorem pointwise_bound {Ω : Type*} (K n : ℕ) (Fx Fy : ℤ → ℝ)
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (H₁ H₂ : ℤ → Set Ω) (ω : Ω)
    (hratio : ∀ v : ℤ, 0 < Fy ((n : ℤ) + v) / Fx v ∧
      Fy ((n : ℤ) + v) / Fx v ≤ min (Fy v / Fx v)
        (Fy ((n : ℤ) + v) / Fx ((n : ℤ) + v)) ∧
      min (Fy v / Fx v) (Fy ((n : ℤ) + v) / Fx ((n : ℤ) + v)) ≤ 1)
    (hzero : (∑' v : ℤ, (ξ v / (Fx v : ℂ)) *
      ((Fy ((n : ℤ) + v) : ℂ) * conj (γ ((n : ℤ) + v)))) = 0)
    (htail : ∀ k : ℤ, (K : ℤ) < |k| → Fy k / Fx k ≤ η +
      (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
      (H₂ k).indicator (fun _ => (1 : ℝ)) ω) :
    ‖truncated K n (fun v => ξ v / (Fx v : ℂ))
      (fun w => (Fy (-w) : ℂ) * conj (γ (-w)))‖ ≤ η +
      (∑' v : ℤ, (omittedEvent H₁ K n v).indicator (fun _ => (1 : ℝ)) ω *
        (‖ξ v‖ * ‖γ ((n : ℤ) + v)‖)) +
      (∑' v : ℤ, (omittedEvent H₂ K n v).indicator (fun _ => (1 : ℝ)) ω *
        (‖ξ v‖ * ‖γ ((n : ℤ) + v)‖)) := by
  classical
  have hmask (H : ℤ → Set Ω) (k : ℤ) :
      ({k | ω ∈ H k} : Set ℤ).indicator (fun _ => (1 : ℝ)) k =
        (H k).indicator (fun _ => (1 : ℝ)) ω := by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hdom := InvariantProjection.l2_masked_convolution_tail_selector
    (window K n) ξ γ (Equiv.addLeft (n : ℤ)) hξ hγ
    (fun v => Fy ((n : ℤ) + v) / Fx v)
    (fun v => ⟨(hratio v).1.le, (hratio v).2.1.trans (hratio v).2.2⟩)
    η hη {k | ω ∈ H₁ k} {k | ω ∈ H₂ k} (selector K n)
    (by
      change (∑' v : ℤ, ((Fy ((n : ℤ) + v) / Fx v : ℝ) : ℂ) * ξ v *
        conj (γ ((n : ℤ) + v))) = 0
      calc
        _ = ∑' v : ℤ, (ξ v / (Fx v : ℂ)) *
            ((Fy ((n : ℤ) + v) : ℂ) * conj (γ ((n : ℤ) + v))) := by
          apply tsum_congr
          intro v
          exact (InvariantProjection.convolution_coefficient_factorization Fx Fy
            (fun v => ξ v) (fun v => γ v) (n : ℤ) v).symm
        _ = 0 := hzero)
    (by
      intro v hv
      have hvw : ¬ (|v| ≤ (K : ℤ) ∧ |(n : ℤ) + v| ≤ (K : ℤ)) := by
        intro hw
        apply hv
        simp only [window, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨abs_le.mp hw.1, hw.2⟩
      have hk := InvariantProjection.omitted_index_selector (K : ℤ) (n : ℤ) v hvw
      have hb := (InvariantProjection.omitted_index_ratio_bound (K : ℤ) (n : ℤ) v
        (fun k => Fy k / Fx k) _ (hratio v).2.1).trans (htail _ hk)
      simpa only [selector, hmask] using hb)
  simp only [hmask] at hdom
  rw [tsum_omittedEvent H₁ K n ω
    (fun v => ‖ξ v‖ * ‖γ ((Equiv.addLeft (n : ℤ)) v)‖),
    tsum_omittedEvent H₂ K n ω
    (fun v => ‖ξ v‖ * ‖γ ((Equiv.addLeft (n : ℤ)) v)‖)] at hdom
  convert hdom using 1
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  change (ξ v / (Fx v : ℂ)) *
    ((Fy (-(-(n : ℤ) - v)) : ℂ) * conj (γ (-(-(n : ℤ) - v)))) = _
  have hsign : -(-(n : ℤ) - v) = (n : ℤ) + v := by omega
  rw [hsign]
  exact InvariantProjection.convolution_coefficient_factorization Fx Fy (fun v => ξ v) (fun v => γ v) (n : ℤ) v
  all_goals rfl

end InvariantProjection.ConditionalConvolution

end OAI
