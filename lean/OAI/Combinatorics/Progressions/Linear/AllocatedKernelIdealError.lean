import OAI.Combinatorics.Progressions.Estimates.AllocatedIdealRefinedPointwise
import OAI.Combinatorics.Progressions.Sampling.AllocatedLongGridCoordinates

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedKernelIdeal_error_le {D p p₀ e E : ℝ} {δ : ℝ≥0} {M : ℕ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hp : 0 ≤ p) (hp₀ : 0 ≤ p₀) (he : 0 ≤ e)
    (hR : ∀ j, 0 ≤ R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (hδe : (δ : ℝ)⁻¹ ≤ Real.exp e) (hMP₀ : (M : ℝ) ≤ Real.exp p₀) :
    let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * p₀
    let Q := {q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) //
      allocatedLongIntegerCoordinate B U basis S q}
    let select := allocatedLongIntegerSelect B U basis S (O := O)
    let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O p), (Real.exp_pos _).le⟩
    let Kp : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * bound *
      bound ^ Fintype.card (LayerSamplerAxis I n)
    let Ki : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
      R q.1.val.1)⁻¹‖₊ *
      (affineProductProfileLip (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) δ *
        NNReal.mk (Real.exp p) (Real.exp_pos p).le)
    let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O p))
      (Real.exp p * (partitionedIdealRadius α m + 1)))
    (2 * Real.exp (allocatedJetSupportLog (G := G) B α O p) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        physicalIdealErrorShare E (allocatedIdealVolumeEnvelope m D p) +
      (layerKernelIndexBound m M : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
        (physicalIdealErrorShare E (D * w) +
          (2 * (Ro : ℝ)) ^ Fintype.card (UnselectedColumn select) *
            ((2 * (Ro : ℝ) + 2) ^ Fintype.card Q * ((Kp : ℝ) + Ki) *
              physicalIdealErrorShare E (D * w + allocatedIdealMeshEnvelope m D p e))) ≤
      Real.exp (-E) := by
  dsimp only
  exact allocatedPhysicalIdeal_error_le B hdim (allocatedGridAxis (I := I) U basis S.value)
    (allocatedLongIntegerSelect B U basis S (O := O)) R hR
    (δ := δ) (p := p) (e := e) (E := E)
    hp he (mul_nonneg (Nat.cast_nonneg _) hp₀) (Nat.cast_nonneg _)
    hRi hδe (layerKernelIndexBound_le_exp m hMP₀) le_rfl le_rfl le_rfl

end Erdos3.VectorPolynomial

end

end OAI
