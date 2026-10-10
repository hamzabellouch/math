import OAI.Combinatorics.Progressions.Probability.MeasureExceptionalModeledPatchTransfer

namespace OAI

section

namespace Erdos3
open MeasureTheory MvPolynomial
open scoped BigOperators NNReal

theorem exists_recursive_exceptional_patch_transfer
    {H σ Ω U I : Type*} [MeasurableSpace H] [Fintype Ω] [Fintype U] [Fintype I]
    {s detector E m d D d₀ j : ℕ}
    (hs : 1 ≤ s) (hD : D ≤ d) (hE : E ≤ d₀ + s * (d - D))
    (hdetector : detector ≤ j * D) (hj : j ≤ s) (law : Measure H) [IsProbabilityMeasure law]
    (productive bad : Set H) (hprod : MeasurableSet productive) (hbad : MeasurableSet bad)
    (Qgood : H → Prop) (hQgood : ∀ᵐ h ∂law, Qgood h)
    (w : Fin detector → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin detector → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (F : H → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C)
    (hF : ∀ h ∈ productive, h ∉ bad → Qgood h → ∀ β, LipschitzWith L (F h β))
    (hFbound : ∀ h ∈ productive, h ∉ bad → Qgood h → ∀ β y, F h β y ∈ Set.Icc (0 : ℝ) C)
    (M : Fin m → Fin detector → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hinvariant : ∀ h ∈ productive, h ∉ bad → Qgood h → ∀ c k, F h (recoveredIntegerLift M c k) = F h c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (f : Ω → ℝ) (G : H → Ω → (Fin m → ℤ) → ℝ) {lam δ ε : ℝ}
    (hf : ∀ u, 0 ≤ f u) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ h ∈ productive, h ∉ bad → Qgood h → ∀ u β, (1 - δ) *
      F h β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) ≤ G h u β)
    (hupper : ∀ h ∈ productive, h ∉ bad → Qgood h → ∀ u β, G h u β ≤ (1 + δ) *
      F h β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)))
    (ψ : H → U → Ω) (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun u => (bufferedScalarScore χ
      (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
      (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) f lam u : ℂ)) =
        (∑ i, c i • J i) + e)
    {τ ρ η M₀ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hη : 0 ≤ η)
    (hc : (∑ i, ‖c i‖) ≤ M₀)
    (hmass : τ ≤ law.real productive) (hbadmass : law.real bad ≤ τ / 4)
    (hatom : ∀ h ∈ productive, h ∉ bad → Qgood h → ∀ i,
      ‖(𝔼 u, (G h u (nearestIntegerLift
        (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * J i u) -
        (𝔼 a, J i (ψ h a))‖ ≤ η)
    (hb : Integrable (fun h => 𝔼 a, e (ψ h a)) law)
    (hlocal : (∫ h, ‖𝔼 a, e (ψ h a)‖ ∂law) ≤ τ * ρ / 32)
    (hforecast : ∀ h ∈ productive, h ∉ bad → Qgood h →
      ‖𝔼 u, (G h u (nearestIntegerLift
        (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * e u‖ ≤ ρ / 8)
    (hbudget : M₀ * η ≤ ρ / 8)
    (hscore : ∀ h ∈ productive, h ∉ bad → Qgood h → ρ ≤ 𝔼 a, bufferedScalarScore χ
      (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
      (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) f lam (ψ h a)) :
    ∃ Q : PolynomialPatch σ s (d₀ + s * d),
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ detector + 1) +
        (χ.lip + L / C) * K + B.kernel.lip + 4 ∧
      (ρ / 2) / ((1 + δ) * (C : ℝ) * (q : ℝ) ^ detector) ≤
        𝔼 u, (f u - (1 - ε) * lam) * Q.value (t u) := by
  obtain ⟨Q, hQlip, hQscore⟩ := exists_measure_exceptional_recovered_patch law
    productive bad hprod hbad Qgood hQgood w hw hws hmono P hP p B χ F L C hC hF hFbound
    M K hM hweight hinvariant q hq hmesh t f G hf hlam hδ hdiscount hlower hupper
    ψ e J c hmodel hτ hρ hη hc hmass hbadmass hatom hb hlocal hforecast hbudget hscore
  have hrank : detector + E ≤ d₀ + s * d :=
    recursive_patch_step_rank_bound hD hE hdetector hj
  refine ⟨Q.padRank hs hrank, ?_, ?_⟩
  · rw [PolynomialPatch.padRank_lip]
    exact add_le_add hQlip le_rfl
  · simpa only [PolynomialPatch.padRank_value] using hQscore

end Erdos3

end

end OAI
