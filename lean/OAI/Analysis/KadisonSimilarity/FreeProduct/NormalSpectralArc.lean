import OAI.Analysis.KadisonSimilarity.FreeProduct.SpectralArcTransport

namespace OAI

/-! The abstract spectral-arc input follows once its generated algebra has
the actual faithful normal range. The ambient algebra need not be presented
in those coordinates. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem dihedralSpectralArcInput_of_normal_range
    (τ : A →ₗ[ℂ] ℂ) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hρ : Function.Injective ρ)
    (Ω : H) (hτ : ∀ a, vectorTrace Ω (ρ a) = τ a)
    (C : StarSubalgebra ℂ A) (P : VonNeumannAlgebra H)
    (hrange : C.map ρ = P.toStarSubalgebra) (w d : Aˣ) (hwC : (w : A) ∈ C)
    (hw : star (w : A) = (↑w⁻¹ : A)) (hwn : ‖(w : A)‖ ≤ 1)
    (hd : (d : A) * (d : A) = 1) (hds : star (d : A) = (d : A))
    (hconj : (d : A) * (w : A) = star (w : A) * (d : A))
    (hhaar : ∀ l : ℤ, τ (↑(w ^ l) : A) = if l = 0 then 1 else 0)
    (hcoset : ∀ l : ℤ, τ ((↑(w ^ l) : A) * (d : A)) = 0) :
    DihedralSpectralArcInput τ C w d := by
  apply dihedralSpectralArcInput_of_injective τ (vectorTrace Ω).toLinearMap ρ hρ hτ C w d
  rw [hrange]
  apply concreteDihedralSpectralArcInput Ω P
  · change ρ (w : A) ∈ P.toStarSubalgebra
    rw [← hrange]
    exact ⟨(w : A), hwC, rfl⟩
  · change star (ρ (w : A)) = ρ (↑w⁻¹ : A)
    rw [← map_star ρ, hw]
  · change ‖ρ (w : A)‖ ≤ 1
    rw [NonUnitalStarAlgHom.norm_map ρ hρ]
    exact hwn
  · change ρ (d : A) * ρ (d : A) = 1
    rw [← map_mul ρ, hd, map_one]
  · change star (ρ (d : A)) = ρ (d : A)
    rw [← map_star ρ, hds]
  · change ρ (d : A) * ρ (w : A) = star (ρ (w : A)) * ρ (d : A)
    rw [← map_star ρ, ← map_mul ρ, ← map_mul ρ, hconj]
  · intro l
    rw [← starAlgHom_unit_zpow ρ w l]
    exact (hτ _).trans (hhaar l)
  · intro l
    rw [← starAlgHom_unit_zpow ρ w l]
    change vectorTrace Ω (ρ (↑(w ^ l) : A) * ρ (d : A)) = 0
    rw [← map_mul ρ, hτ, hcoset]

end KadisonSimilarity

end

end OAI
