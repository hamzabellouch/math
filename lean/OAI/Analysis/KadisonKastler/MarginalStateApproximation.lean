import OAI.Analysis.KadisonKastler.MarginalStateMultiplication

namespace OAI

/-! # Strong approximation of products under normal marginals

This estimates a possibly nonnormal ambient state using its vector-state
marginals. It is the product approximation step of Marrakchi's Lemma 4.1.
-/

namespace KadisonKastler

open Filter NaimarkZFC
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem state_product_sub_le_of_vector_marginals
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) (Ω : H)
    (a b a' b' : H →L[ℂ] H)
    (ha : φ ((a-a')*star (a-a'))=((‖star (a-a') Ω‖^2 : ℝ) : ℂ))
    (hb : φ (star (b-b')*(b-b'))=((‖(b-b') Ω‖^2 : ℝ) : ℂ)) :
    ‖φ (a*b)-φ (a'*b')‖ ≤
      ‖star (a-a') Ω‖*‖b‖+‖a'‖*‖(b-b') Ω‖ := by
  have he : a*b-a'*b'=(a-a')*b+a'*(b-b') := by noncomm_ring
  rw [← map_sub,he,map_add]
  exact (norm_add_le _ _).trans (add_le_add
    (state_left_mul_le_of_vector_marginal φ hφ Ω (a-a') b ha)
    (state_right_mul_le_of_vector_marginal φ hφ Ω a' (b-b') hb))

theorem state_product_tendsto_of_vector_marginals
    {I : Type*} {l : Filter I}
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) (Ω : H)
    (a b : I → H →L[ℂ] H) (a₀ b₀ : H →L[ℂ] H)
    (ha : ∀ i, φ ((a i-a₀)*star (a i-a₀))=((‖star (a i-a₀) Ω‖^2 : ℝ) : ℂ))
    (hb : ∀ i, φ (star (b i-b₀)*(b i-b₀))=((‖(b i-b₀) Ω‖^2 : ℝ) : ℂ))
    (B : ℝ) (hB : ∀ i, ‖b i‖ ≤ B)
    (hca : Tendsto (fun i => star (a i-a₀) Ω) l (𝓝 0))
    (hcb : Tendsto (fun i => (b i-b₀) Ω) l (𝓝 0)) :
    Tendsto (fun i => φ (a i*b i)) l (𝓝 (φ (a₀*b₀))) := by
  have hlim : Tendsto (fun i => ‖star (a i-a₀) Ω‖*B+‖a₀‖*‖(b i-b₀) Ω‖)
      l (𝓝 0) := by
    simpa only [norm_zero,zero_mul,mul_zero,add_zero] using
      (hca.norm.mul_const B).add (hcb.norm.const_mul ‖a₀‖)
  have hn : Tendsto (fun i => ‖φ (a i*b i)-φ (a₀*b₀)‖) l (𝓝 0) := by
    apply squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hlim
    exact (state_product_sub_le_of_vector_marginals φ hφ Ω (a i) (b i) a₀ b₀
      (ha i) (hb i)).trans (add_le_add
        (mul_le_mul_of_nonneg_left (hB i) (norm_nonneg _)) le_rfl)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end

end KadisonKastler

end OAI
