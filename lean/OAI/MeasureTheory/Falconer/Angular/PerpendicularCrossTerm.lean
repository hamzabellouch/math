import OAI.MeasureTheory.Falconer.Angular.CapSymbolBounds
import OAI.MeasureTheory.Falconer.Angular.DiscardedCapTerm

namespace OAI

/-!
# A perpendicular-test error for the original four endpoint transforms

The cap-weighted endpoint products satisfy the analytic localization
hypotheses. All four original spatial laws and all four model-mass
normalizations are retained in the resulting estimate.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem perpendicular_endpoint_cross_term
    (hpublished : PublishedGnomonicSurface) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w d₀ : Space (n+2)) (τ δ : ℝ),
      ‖w‖ = 1 → 0 < τ → 0 < δ → δ ≤ 1/2 → τ < ‖perpendicularPart w d₀‖ →
      ∀ (μ μ' ν ν' : Measure (Space (n+2)))
        [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν'],
      ∀ (η θ : Sphere (n+2) → ℝ), Measurable η → Measurable θ →
      (∀ z, |η z| ≤ 1) → (∀ z, |θ z| ≤ 1) →
      (∀ z, η z ≠ 0 → ‖(z : Space (n+2))-w‖ ≤ δ) →
      ∀ (b b' c c' : Space (n+2) → Sphere (n+2) → ℂ),
      Measurable (Function.uncurry b) → Measurable (Function.uncurry b') →
      Measurable (Function.uncurry c) → Measurable (Function.uncurry c') →
      (∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n,
        ContDiff ℝ ∞ (rotatedChartAmplitude e (fun z => (η z : ℂ)) y)) →
      (∀ x, ∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n,
        ContDiff ℝ ∞ (rotatedChartAmplitude e (b x) y)) →
      (∀ x, ∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n,
        ContDiff ℝ ∞ (rotatedChartAmplitude e (b' x) y)) →
      ∀ (H B D : ℝ), 0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      (∀ x z, ‖b x z‖ ≤ B) → (∀ x z, ‖b' x z‖ ≤ B) →
      (∀ x z, ‖c x z‖ ≤ B) → (∀ x z, ‖c' x z‖ ≤ B) →
      (∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ k ≤ m,
        ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖iteratedDeriv k (rotatedChartAmplitude e (fun z => (η z : ℂ)) y) u‖ ≤ H*(δ⁻¹)^k) →
      (∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ k ≤ m,
        ∀ x, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖iteratedDeriv k (rotatedChartAmplitude e (b x) y) u‖ ≤ B*D^k) →
      (∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ k ≤ m,
        ∀ x, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖iteratedDeriv k (rotatedChartAmplitude e (b' x) y) u‖ ≤ B*D^k) →
      (∀ x : Space (n+2) × Space (n+2), (∃ z, capPairAmplitude η b b' x z ≠ 0) →
        ‖x.1-x.2‖ ≤ (τ/4)*D) →
      (∀ x : Space (n+2) × Space (n+2), (∃ z, capPairAmplitude η b b' x z ≠ 0) →
        ‖(x.1-x.2)-d₀‖+8*δ*‖d₀‖ ≤ τ/2) →
      ∀ (M M' P P' v : ℝ) (Ψ : ℝ → ℝ), Measurable Ψ →
      (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) → ∀ W : ℝ, 0 ≤ W → (∀ t, Ψ t ≤ W) →
      ‖endpointCapCrossTerm μ μ' ν ν' M M' P P' v Ψ b b' c c' η θ‖ ≤
        |(M⁻¹*M'⁻¹)*(P⁻¹*P'⁻¹)| *
          (A*(4^m*H*B*B)*(B*B)*(sphereMeasure (n+2)).real univ*
            ((μ.prod μ').prod (ν.prod ν')).real univ) *
          (16*D/((2 : ℝ)^v*τ))^m*(4*W) := by
  let X := (Space (n+2) × Space (n+2)) × (Space (n+2) × Space (n+2))
  obtain ⟨A,hA,hmain⟩ := discarded_cap_term_bound (X := X) hpublished n m hn
  refine ⟨A,hA,?_⟩
  intro w d₀ τ δ hw hτ hδ hsmall hbad
  obtain ⟨e,hew,he⟩ := hmain w d₀ τ δ hw hτ hδ.le hsmall hbad
  intro μ μ' ν ν' _ _ _ _ η θ hη hθ hηnorm hθnorm hcap
    b b' c c' hb hb' hc hc' hηsmooth hbsmooth hb'smooth
    H B D hH hB hD hscale hbB hb'B hcB hc'B hηder hbder hb'der hv herr
    M M' P P' v Ψ hΨ hs W hW hΨW
  let μ₄ := (μ.prod μ').prod (ν.prod ν')
  let a₁ : X → Sphere (n+2) → ℂ := fun x z => capPairAmplitude η b b' x.1 z
  let a₂ : X → Sphere (n+2) → ℂ := fun x z => capPairAmplitude θ c c' x.2 z
  have ha₁ : Measurable (Function.uncurry a₁) :=
    (capPairAmplitude_measurable η hη b b' hb hb').comp
      (measurable_fst.fst.prodMk measurable_snd)
  have ha₂ : Measurable (Function.uncurry a₂) :=
    (capPairAmplitude_measurable θ hθ c c' hc hc').comp
      (measurable_fst.snd.prodMk measurable_snd)
  have hcap₁ (x : X) (z : Sphere (n+2)) (hz : a₁ x z ≠ 0) :
      ‖(z : Space (n+2))-w‖ ≤ δ := capPairAmplitude_cap_support η b b' w δ hcap x.1 z hz
  have hb₁ (x : X) (z : Sphere (n+2)) : ‖a₁ x z‖ ≤ B*B := by
    simpa only [one_mul] using capPairAmplitude_norm_le η b b' zero_le_one hB hηnorm hbB hb'B x.1 z
  have hb₂ (x : X) (z : Sphere (n+2)) : ‖a₂ x z‖ ≤ B*B := by
    simpa only [one_mul] using capPairAmplitude_norm_le θ c c' zero_le_one hB hθnorm hcB hc'B x.2 z
  have hpairSmooth (x : X) (y : Space n) (_hy : ‖y‖ ≤ 1) :
      ContDiff ℝ ∞ (rotatedChartAmplitude e (a₁ x) y) :=
    capPairAmplitude_chart_smooth e η b b' x.1 y (hηsmooth e y)
      (hbsmooth x.1.1 e y) (hb'smooth x.1.2 e y)
  have hpairDer (k : ℕ) (hk : k ≤ m) (x : X) (y : Space n) (hy : ‖y‖ ≤ 1)
      (u : ℝ) (hu : u ∈ tsupport (rotatedChartAmplitude e (a₁ x) y)) :
      ‖iteratedDeriv k (rotatedChartAmplitude e (a₁ x) y) u‖ ≤ (4^m*H*B*B)*D^k := by
    apply capPairAmplitude_supported_derivatives e η b b' x.1 m hδ hsmall
      hH hB hB (zero_le_one.trans hD) hscale
      (fun z hz => by simpa only [hew] using hcap z hz)
      (hηsmooth e) (hbsmooth x.1.1 e) (hb'smooth x.1.2 e)
      (hηder e) (fun j hj => hbder e j hj x.1.1)
      (fun j hj => hb'der e j hj x.1.2) k hk y hy u hu
  have hh := he μ₄ (fun x => x.1.1-x.1.2) (fun x => x.2.1-x.2.2)
    (by fun_prop) (by fun_prop) a₁ a₂ ha₁ ha₂ hcap₁ hpairSmooth
    (B*B) (B*B) (4^m*H*B*B) D v Ψ (by positivity) (by positivity) (by positivity) hD
    hb₁ hb₂ (fun x hx => hv x.1 hx) (fun x hx => herr x.1 hx) hpairDer hΨ hs W hW hΨW
  rw [endpointCapCrossTerm_four_point,norm_smul,Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans_eq
  ring

end Falconer

end OAI
