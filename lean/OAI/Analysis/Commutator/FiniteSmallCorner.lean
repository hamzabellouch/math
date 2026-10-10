import Mathlib
import OAI.Analysis.Commutator.FiniteFactorCornerTransport

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder

namespace Kadison.CornerTransport

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem finite_small_corner_bound (Q : VonNeumannAlgebra H) (hQ : FactorCorner.IsFactor Q)
    (σ : Q →ₚ[ℂ] ℂ) (hσ : ∀ a b : Q,σ (a*b)=σ (b*a))
    (hfaith : ∀ a : Q,σ (star a*a)=0 → a=0)
    (j : Q →⋆ₐ[ℂ] A) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (T : K →L[ℂ] K) (hT : ∀ q : Q,T*ρ (j q)=ρ (j q)*T)
    (e : Q) (he : IsStarProjection e) {c : ℝ}
    (hbound : ∀ z : A,j e*z*j e=z → ‖T*ρ z-ρ z*T‖≤c*‖z‖)
    (f : Q) (hf : IsStarProjection f) (htrace : σ f≤σ e)
    (z : A) (hz : j f*z*j f=z) : ‖T*ρ z-ρ z*T‖≤c*‖z‖ := by
  obtain ⟨u,hu⟩ := PartialIsometryOrder.finite_factor_unitary_subequivalence Q hQ σ hσ hfaith f e hf he htrace
  let v : unitary A := ⟨j (u:Q),Unitary.map_mem j u.property⟩
  have hv : (v:A)*j f*star (v:A)≤j e := by
    change j (u:Q)*j f*star (j (u:Q))≤j e
    rw [←map_star,←map_mul,←map_mul]
    exact OrderHomClass.monotone j hu
  have hcorner := conjugate_corner (j e) (j f) (he.map j) (hf.map j) v hv z hz
  apply bound_under_unitary ρ T v (hT (u:Q)) ?_ z (hbound _ hcorner)
  change T*ρ (star (j (u:Q)))=ρ (star (j (u:Q)))*T
  rw [←map_star]
  exact hT (star (u:Q))

end Kadison.CornerTransport

end

end
end

end OAI
