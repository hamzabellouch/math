import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hread : ∀ j i e, allocatedReadProjection read ⟨j, Sum.inr i⟩ e = (sample j).2 i e)

include hread

omit [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)] in
theorem allocatedOriginalSampleInactiveCoefficients_eq_read :
    allocatedOriginalSampleInactiveCoefficients B selected sample =
      fun a => allocatedReadProjection read ⟨(selected a).1, Sum.inr (selected a).2⟩ := by
  funext a e
  exact (hread (selected a).1 (selected a).2 e).symm

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem forecastInactiveOriginalSampleOutput_eq_read
    (x : G → IntegerScalarCubeBox Empty S.value) :
    forecastInactiveFixedOutput B U b S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x =
    forecastInactiveFixedOutput B U b S selected
      (fun a => allocatedReadProjection read ⟨(selected a).1, Sum.inr (selected a).2⟩) x := by
  rw [allocatedOriginalSampleInactiveCoefficients_eq_read B selected sample read hread]

end Erdos3.VectorPolynomial

end

end OAI
