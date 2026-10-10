import OAI.Analysis.KadisonKastler.CanonicalAmplification

namespace OAI

/-! # Transporting an implementer through Hilbert coordinates -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def spatialTransportUnitary (e : H ≃ₗᵢ[ℂ] K) (u : unitary (H →L[ℂ] H)) :
    unitary (K →L[ℂ] K) :=
  Unitary.map (StarMonoidHom.ofClass e.conjStarAlgEquiv) u

@[simp] theorem coe_spatialTransportUnitary (e : H ≃ₗᵢ[ℂ] K)
    (u : unitary (H →L[ℂ] H)) :
    (spatialTransportUnitary e u : K →L[ℂ] K) = e.conjStarAlgEquiv u := rfl

theorem norm_spatialTransportUnitary_sub_one (e : H ≃ₗᵢ[ℂ] K)
    (u : unitary (H →L[ℂ] H)) :
    ‖(spatialTransportUnitary e u : K →L[ℂ] K) - 1‖ = ‖(u : H →L[ℂ] H) - 1‖ := by
  rw [coe_spatialTransportUnitary, ← map_one e.conjStarAlgEquiv, ← map_sub]
  exact norm_spatialConjugate e _

theorem unitaryConj_spatialTransport (e : H ≃ₗᵢ[ℂ] K)
    (u : unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    unitaryConj (spatialTransportUnitary e u) (e.conjStarAlgEquiv T) =
      e.conjStarAlgEquiv (unitaryConj u T) := by
  simp only [unitaryConj, coe_spatialTransportUnitary, map_mul, map_star]

theorem Conjugates.spatialTransport {M N : VonNeumannAlgebra H}
    {u : unitary (H →L[ℂ] H)} (hu : Conjugates u M N) (e : H ≃ₗᵢ[ℂ] K) :
    Conjugates (spatialTransportUnitary e u)
      (spatialTransportAlgebra e M) (spatialTransportAlgebra e N) := by
  change unitaryConj (spatialTransportUnitary e u) ''
      (e.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H))) =
    e.conjStarAlgEquiv '' (N : Set (H →L[ℂ] H))
  simpa only [Set.image_image, unitaryConj_spatialTransport] using
    congrArg (fun S : Set (H →L[ℂ] H) => e.conjStarAlgEquiv '' S) hu

@[simp] theorem spatialTransportAlgebra_symm (e : H ≃ₗᵢ[ℂ] K)
    (M : VonNeumannAlgebra H) :
    spatialTransportAlgebra e.symm (spatialTransportAlgebra e M) = M := by
  ext T
  rw [mem_spatialTransportAlgebra, mem_spatialTransportAlgebra]
  change e.conjStarAlgEquiv.symm (e.conjStarAlgEquiv T) ∈ M ↔ T ∈ M
  rw [StarAlgEquiv.symm_apply_apply]

theorem exists_bounded_conjugacy_of_spatialTransport
    (e : H ≃ₗᵢ[ℂ] K) (M N : VonNeumannAlgebra H) {a : ℝ}
    (hex : ∃ u : unitary (K →L[ℂ] K),
      Conjugates u (spatialTransportAlgebra e M) (spatialTransportAlgebra e N) ∧
        ‖(u : K →L[ℂ] K) - 1‖ ≤ a) :
    ∃ u : unitary (H →L[ℂ] H),
      Conjugates u M N ∧ ‖(u : H →L[ℂ] H) - 1‖ ≤ a := by
  obtain ⟨u, hu, hnorm⟩ := hex
  refine ⟨spatialTransportUnitary e.symm u, ?_, ?_⟩
  · simpa only [spatialTransportAlgebra_symm] using hu.spatialTransport e.symm
  · simpa only [norm_spatialTransportUnitary_sub_one] using hnorm

end

end KadisonKastler

end OAI
