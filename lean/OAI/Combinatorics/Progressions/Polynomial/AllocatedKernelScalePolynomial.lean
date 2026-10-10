import OAI.Combinatorics.Progressions.Linear.AllocatedAveragedCoarseKernelComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedKernelScale_upper (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ v, Fintype (B v)]
      {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
      (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
      {p E T : ℝ}, 0 ≤ p → 0 ≤ E → 0 ≤ T →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
      (∀ j, (n j : ℝ) ≤ p) → (∀ j, (R j)⁻¹ ≤ Real.exp p) → (∀ j, (σ j)⁻¹ ≤ Real.exp p) →
      ((allocatedKernelScale (G := G) B U b hR hσ p E T).value : ℝ) ≤
        Real.exp ((p + E + T + a)^a) := by
  obtain ⟨A, _, hscale⟩ := exists_allocatedPrimitiveNormalizedScale_upper m
  obtain ⟨a, ha, hthreshold⟩ := exists_allocatedKernelThreshold_bound A
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ J _ U b R σ hR hσ p E T hp hE hT hvars hn hRi hσi
  obtain ⟨hQ, hpQ, _, _, _⟩ := allocatedKernelPrimitiveBudget_bounds hp hE hT
  have hexp := Real.exp_le_exp.mpr hpQ
  have hS := hscale B U b hR hσ hQ (show 0 ≤ E + 1 by positivity) (show 0 ≤ T + 1 by positivity)
    (hvars.trans hpQ) (fun j => (hn j).trans hpQ)
    (fun j => (hRi j).trans hexp) (fun j => (hσi j).trans hexp)
  exact hS.trans (Real.exp_le_exp.mpr (hthreshold hp hE hT))

end Erdos3.VectorPolynomial

end

end OAI
