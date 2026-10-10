import OAI.Analysis.IrrationalRotation.Analysis.ConvolutionRatios
import OAI.Analysis.IrrationalRotation.Analysis.MaskedConvolutionTail

namespace OAI

open scoped ComplexConjugate ENNReal lp

namespace InvariantProjection

theorem l2_masked_convolution_tail
    (s : Finset ℤ) (ξ γ : ℓ²(ℤ, ℂ)) (e : ℤ ≃ ℤ)
    (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1)
    (r : ℤ → ℝ) (hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (H₁ H₂ : Set ℤ)
    (hzero : (∑' v : ℤ, (r v : ℂ) * ξ v * conj (γ (e v))) = 0)
    (hmask : ∀ v, v ∉ s → r v ≤ η + H₁.indicator (fun _ => (1 : ℝ)) v +
      H₂.indicator (fun _ => (1 : ℝ)) v) :
    ‖∑ v ∈ s, (r v : ℂ) * ξ v * conj (γ (e v))‖ ≤ η +
      (∑' v : ↑((s : Set ℤ)ᶜ), H₁.indicator (fun v => ‖ξ v‖ * ‖γ (e v)‖) v) +
      (∑' v : ↑((s : Set ℤ)ᶜ), H₂.indicator (fun v => ‖ξ v‖ * ‖γ (e v)‖) v) := by
  have hbase := l2_reindexed_absolute_products ξ γ e
  have hsum : (∑' v, ‖ξ v‖ * ‖γ (e v)‖) ≤ 1 := by
    refine hbase.2.trans ?_
    calc
      ‖ξ‖ * ‖γ‖ ≤ 1 * 1 := mul_le_mul hξ hγ (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hdom := norm_finset_sum_le_masked_tail s
    (fun v => (r v : ℂ) * ξ v * conj (γ (e v)))
    (fun v => ‖ξ v‖ * ‖γ (e v)‖) η H₁ H₂
    (l2_reindexed_multiplier_bound ξ γ e r hr).1 hzero hbase.1
    (fun v => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hη
    (fun v hv => by
      simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hr v).1]
      calc
        r v * ‖ξ v‖ * ‖γ (e v)‖ = r v * (‖ξ v‖ * ‖γ (e v)‖) := by ring
        _ ≤ (η + H₁.indicator (fun _ => (1 : ℝ)) v +
            H₂.indicator (fun _ => (1 : ℝ)) v) * (‖ξ v‖ * ‖γ (e v)‖) := by
          gcongr
          exact hmask v hv)
  refine hdom.trans ?_
  gcongr
  simpa using mul_le_mul_of_nonneg_left hsum hη

theorem l2_masked_convolution_tail_selector
    (s : Finset ℤ) (ξ γ : ℓ²(ℤ, ℂ)) (e : ℤ ≃ ℤ)
    (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1)
    (r : ℤ → ℝ) (hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (H₁ H₂ : Set ℤ) (k : ℤ → ℤ)
    (hzero : (∑' v : ℤ, (r v : ℂ) * ξ v * conj (γ (e v))) = 0)
    (hmask : ∀ v, v ∉ s → r v ≤ η + H₁.indicator (fun _ => (1 : ℝ)) (k v) +
      H₂.indicator (fun _ => (1 : ℝ)) (k v)) :
    ‖∑ v ∈ s, (r v : ℂ) * ξ v * conj (γ (e v))‖ ≤ η +
      (∑' v : ↑((s : Set ℤ)ᶜ),
        (H₁.indicator (fun _ => (1 : ℝ)) (k v)) * (‖ξ v‖ * ‖γ (e v)‖)) +
      (∑' v : ↑((s : Set ℤ)ᶜ),
        (H₂.indicator (fun _ => (1 : ℝ)) (k v)) * (‖ξ v‖ * ‖γ (e v)‖)) := by
  classical
  have hind (H : Set ℤ) (v : ℤ) :
      (k ⁻¹' H).indicator (fun v => ‖ξ v‖ * ‖γ (e v)‖) v =
        H.indicator (fun _ => (1 : ℝ)) (k v) * (‖ξ v‖ * ‖γ (e v)‖) := by
    by_cases hv : k v ∈ H <;> simp [hv]
  have hone (H : Set ℤ) (v : ℤ) :
      (k ⁻¹' H).indicator (fun _ => (1 : ℝ)) v =
        H.indicator (fun _ => (1 : ℝ)) (k v) := by
    simp only [Set.indicator_apply, Set.mem_preimage]
  have h := l2_masked_convolution_tail s ξ γ e hξ hγ r hr η hη
    (k ⁻¹' H₁) (k ⁻¹' H₂) hzero (by simpa only [hone] using hmask)
  simpa only [hind] using h

theorem cocycle_masked_tail
    (K n : ℕ) (Fx Fy : ℤ → ℝ)
    (hFx : ∀ k, 0 < Fx k) (hFy : ∀ k, 0 < Fy k)
    (hx : Antitone Fx) (hy : Antitone Fy) (hxy : ∀ k, Fy k / Fx k ≤ 1)
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (H₁ H₂ : Set ℤ)
    (hzero : (∑' v : ℤ,
      ((Fy ((n : ℤ) + v) / Fx v : ℝ) : ℂ) * ξ v * conj (γ ((n : ℤ) + v))) = 0)
    (htail : ∀ k : ℤ, (K : ℤ) < |k| → Fy k / Fx k ≤
      η + H₁.indicator (fun _ => (1 : ℝ)) k + H₂.indicator (fun _ => (1 : ℝ)) k) :
    let s : Finset ℤ := (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
      (fun v => |(n : ℤ) + v| ≤ (K : ℤ))
    let k : ℤ → ℤ := fun v => if (K : ℤ) < |v| then v else (n : ℤ) + v
    ‖∑ v ∈ s, ((Fy ((n : ℤ) + v) / Fx v : ℝ) : ℂ) * ξ v *
      conj (γ ((n : ℤ) + v))‖ ≤ η +
      (∑' v : ↑((s : Set ℤ)ᶜ), H₁.indicator (fun _ => (1 : ℝ)) (k v) *
        (‖ξ v‖ * ‖γ ((n : ℤ) + v)‖)) +
      (∑' v : ↑((s : Set ℤ)ᶜ), H₂.indicator (fun _ => (1 : ℝ)) (k v) *
        (‖ξ v‖ * ‖γ ((n : ℤ) + v)‖)) := by
  dsimp only
  refine l2_masked_convolution_tail_selector
    ((Finset.Icc (-(K : ℤ)) (K : ℤ)).filter (fun v => |(n : ℤ) + v| ≤ (K : ℤ)))
    ξ γ (Equiv.addLeft (n : ℤ)) hξ hγ (fun v => Fy ((n : ℤ) + v) / Fx v) ?_
    η hη H₁ H₂ (fun v => if (K : ℤ) < |v| then v else (n : ℤ) + v) hzero ?_
  · intro v
    have h := cocycle_two_ratio_bounds Fx Fy hFx hFy hx hy hxy n v
    exact ⟨h.1.le, h.2.1.trans h.2.2⟩
  · intro v hv
    have hvw : ¬ (|v| ≤ (K : ℤ) ∧ |(n : ℤ) + v| ≤ (K : ℤ)) := by
      intro hw
      apply hv
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨abs_le.mp hw.1, hw.2⟩
    have hk := omitted_index_selector (K : ℤ) (n : ℤ) v hvw
    have h := cocycle_two_ratio_bounds Fx Fy hFx hFy hx hy hxy n v
    exact (omitted_index_ratio_bound (K : ℤ) (n : ℤ) v
      (fun k => Fy k / Fx k) _ h.2.1).trans (htail _ hk)

end InvariantProjection

end OAI
