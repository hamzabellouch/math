import OAI.AlgebraicGeometry.CartierSections.FieldTopology
import OAI.AlgebraicGeometry.CartierSections.FieldRetraction

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal
namespace CartierSections
section ClosedChartFieldTopology
universe u
local instance polynomialOrigin_isMaximal_topology {σ k : Type u} [Fintype σ] [Field k] :
    (MvPolynomial.idealOfVars σ k).IsMaximal :=
  polynomialOrigin_isMaximal

variable {σ k R A K : Type u} [Fintype σ] [Field k] [IsAlgClosed k]
  [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A] [IsNoetherianRing A]
  [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Algebra (MvPolynomial σ k) R] [Algebra (MvPolynomial σ k) A]
  [Algebra k A] [IsScalarTower k (MvPolynomial σ k) A]
  [Algebra R A] [IsScalarTower (MvPolynomial σ k) R A]
  [IsLocalization.AtPrime R (MvPolynomial.idealOfVars σ k)]
  [IsLocalHom (algebraMap R A)] [Algebra.FormallyUnramified R A]
  [Algebra.EssFiniteType R A] [Algebra.FormallyEtale (MvPolynomial σ k) A]

lemma isCompact_closedChartFieldRetraction_cone
    (a : σ → NNReal) (ha : ∀ i, 0 < a i) :
    IsCompact ((fun w : σ → NNReal => fun x : K =>
      closedChartFieldRetraction (σ := σ) (k := k) (R := R) (A := A) w x) ''
      normalizedWeights a) := by
  sorry

end ClosedChartFieldTopology
end CartierSections

end

end OAI
