import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphSourceFixedGeometry
import OAI.MeasureTheory.FalconerCompletion.Graphs.SpherePlaneWaveSub

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
namespace CurrentFalconer
open Set MeasureTheory Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem graph_source_four_spatial_decay
    {sig c₀ Ccap G : ℝ} (hsig : 0 < sig) (hc₀ : 0 < c₀)
    (hCcap : 0 ≤ Ccap) (hG : 0 ≤ G) (T : ℝ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (a p v L : ℝ), p-a ≤ v-p+2*sig*N → L ≤ v-p+2*sig*N → 0 ≤ v-p →
    let R := (2:ℝ)^N
    let δ := min c₀ (((2:ℝ)^(p-a))⁻¹*R^(10*sig))
    let τ := (2:ℝ)^(-p)*R^(30*sig)
    let A := 1+R^sig*max 1 ((2:ℝ)^L*R^(-50*sig))+δ⁻¹
    ∀ (μ₁ μ₂ μ₃ μ₄ : Measure V),
    ∀ [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄],
    ∀ (Ψ : ℝ → ℂ) (w₁ w₂ d₁ d₂ : V) (K J₁ J₂ : ℝ)
      (θ₁ θ₂ : V → ℂ) (b₁ b₂ b₃ b₄ : V → V → ℂ)
      (P₁ P₂ B₁ B₂ B₃ B₄ : ℝ),
    ContDiff ℝ ∞ Ψ → tsupport Ψ ⊆ Icc (1/4:ℝ) 4 →
    (∫ u : ℝ, ‖Ψ u‖) ≤ K → (∀ u, ‖iteratedDeriv m Ψ u‖ ≤ K) →
    ‖w₁‖=1 → ‖w₂‖=1 → 0 ≤ K → 0 ≤ J₁ → 0 ≤ J₂ →
    Measurable θ₁ → Measurable θ₂ →
    Measurable (Function.uncurry b₁) → Measurable (Function.uncurry b₂) →
    Measurable (Function.uncurry b₃) → Measurable (Function.uncurry b₄) →
    0 ≤ P₁ → 0 ≤ P₂ → 0 ≤ B₁ → 0 ≤ B₂ → 0 ≤ B₃ → 0 ≤ B₄ →
    (∀ w, ‖w‖=1 → ‖θ₁ w‖ ≤ P₁) → (∀ w, ‖w‖=1 → ‖θ₂ w‖ ≤ P₂) →
    (∀ x w, ‖w‖=1 → ‖b₁ x w‖ ≤ B₁) → (∀ x w, ‖w‖=1 → ‖b₂ x w‖ ≤ B₂) →
    (∀ x w, ‖w‖=1 → ‖b₃ x w‖ ≤ B₃) → (∀ x w, ‖w‖=1 → ‖b₄ x w‖ ≤ B₄) →
    (∀ᵐ z ∂(μ₁.prod μ₂).prod (μ₃.prod μ₄),
      ‖z.1.1-z.1.2‖ ≤ G*(2:ℝ)^(-a) ∧ ‖z.2.1-z.2.2‖ ≤ G*(2:ℝ)^(-a) ∧
      ‖(z.1.1-z.1.2)-d₁‖ ≤ G*(2:ℝ)^(-p) ∧ ‖(z.2.1-z.2.2)-d₂‖ ≤ G*(2:ℝ)^(-p)) →
    ¬(‖d₁-inner ℝ d₁ w₁ • w₁‖ ≤ τ ∧
      ‖d₂-inner ℝ d₂ w₂ • w₂‖ ≤ τ ∧ |inner ℝ w₁ d₁+inner ℝ w₂ d₂| ≤ τ) →
    (∀ z, ContDiff ℝ ∞ (graphPairAmplitude θ₁ b₁ b₂ z)) →
    (∀ z, ContDiff ℝ ∞ (graphPairAmplitude θ₂ b₃ b₄ z)) →
    (∀ z j, j ≤ m → ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (graphPairAmplitude θ₁ b₁ b₂ z) w‖ ≤ J₁*A^j) →
    (∀ z j, j ≤ m → ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (graphPairAmplitude θ₂ b₃ b₄ z) w‖ ≤ J₂*A^j) →
    (∀ w, ‖w‖=1 → θ₁ w ≠ 0 → ‖w-w₁‖ ≤ Ccap*δ) →
    (∀ w, ‖w‖=1 → θ₂ w ≠ 0 → ‖w-w₂‖ ≤ Ccap*δ) →
    ‖∫ u, Ψ u*graphPairMoment μ₁ μ₂ b₁ b₂ θ₁ ((2:ℝ)^v*u)*
      graphPairMoment μ₃ μ₄ b₃ b₄ θ₂ ((2:ℝ)^v*u)‖ ≤
      C*K*J₁*J₂*R^(-T)*((μ₁.prod μ₂).prod (μ₃.prod μ₄)).real univ := by
  obtain ⟨m,C,hC,N₀,hN₀⟩ := graph_source_fixed_nonedge_decay V hsig hc₀ hCcap hG T
  refine ⟨m,C,hC,N₀,?_⟩
  intro N hN a p v L hh hL hq R δ τ A μ₁ μ₂ μ₃ μ₄ _ _ _ _
    Ψ w₁ w₂ d₁ d₂ K J₁ J₂ θ₁ θ₂ b₁ b₂ b₃ b₄ P₁ P₂ B₁ B₂ B₃ B₄
    hΨ hsΨ hK hdΨ hw₁ hw₂ hK0 hJ₁ hJ₂ hθ₁ hθ₂ hb₁ hb₂ hb₃ hb₄
    hP₁ hP₂ hB₁ hB₂ hB₃ hB₄ hdθ₁ hdθ₂ hbd₁ hbd₂ hbd₃ hbd₄ hgeo hne
    ha₁ ha₂ hd₁ hd₂ hs₁ hs₂
  have hiΨ : Integrable Ψ := hΨ.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport Ψ) hsΨ)
  rw [graph_four_spatial_factorization μ₁ μ₂ μ₃ μ₄ hΨ.continuous.measurable hiΨ
    ((2:ℝ)^v) θ₁ θ₂ b₁ b₂ b₃ b₄ hθ₁ hθ₂ hb₁ hb₂ hb₃ hb₄
    hP₁ hP₂ hB₁ hB₂ hB₃ hB₄ hdθ₁ hdθ₂ hbd₁ hbd₂ hbd₃ hbd₄]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hgeo] with z hz
  apply hN₀ N hN a p v L hh hL hq Ψ w₁ w₂ d₁ d₂
    (z.1.1-z.1.2) (z.2.1-z.2.2) K J₁ J₂
    (graphPairAmplitude θ₁ b₁ b₂ z.1) (graphPairAmplitude θ₂ b₃ b₄ z.2)
    hΨ hsΨ hK hdΨ hw₁ hw₂ hK0 hJ₁ hJ₂ hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 hne
    (ha₁ z.1) (ha₂ z.2) (hd₁ z.1) (hd₂ z.2)
  · intro w hw hne
    apply hs₁ w hw
    intro hz
    apply hne
    simp [graphPairAmplitude,hz]
  · intro w hw hne
    apply hs₂ w hw
    intro hz
    apply hne
    simp [graphPairAmplitude,hz]

end CurrentFalconer
end
end

end OAI
