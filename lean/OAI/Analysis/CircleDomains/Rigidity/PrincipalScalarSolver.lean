import OAI.Analysis.CircleDomains.Rigidity.ConductivityDistortion

namespace OAI

/-! Scalar transport data for conductivity postcomposition, constructed
from smooth principal maps. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def CompactScalarPullback (φ : ℂ ≃ₜ ℂ) : Prop :=
  ∀ (u : EuclideanPlane → ℝ), Continuous u → HasCompactSupport u →
    ∀ W : DeGiorgi.MemW1pWitness 2 u univ,
    ∀ F : Set EuclideanPlane, IsCompact F →
      (∀ i, ∀ᵐ x ∂volume, x ∈ F → W.weakGrad x i=0) →
      ∃ V : DeGiorgi.MemW1pWitness 2 (u ∘ physicalHomeomorph φ.symm) univ,
        ∀ i, ∀ᵐ x ∂volume, x ∈ physicalHomeomorph φ '' F → V.weakGrad x i=0

def PrincipalConductivityScalarSolver : Prop :=
  ∀ F : Set EuclideanPlane, IsCompact F → ∀ n : ℕ, 1 ≤ n →
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))),
      Tendsto (fun z => φ z-z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      (∀ᵐ x ∂volume,
        D.realGradient x 0 = conductivityValue F n x*D.imagGradient x 1 ∧
        D.realGradient x 1 = -conductivityValue F n x*D.imagGradient x 0) ∧
      CompactScalarPullback φ

lemma principalConductivityScalarSolver_of_published_inputs
    (hqc : PlaneQuasiconformalCalculus) (hprincipal : PrincipalRealBeltrami) :
    PrincipalConductivityScalarSolver := by
  intro F hF n hn
  obtain ⟨φ, D, ht, hsys⟩ := exists_principal_conductivity_coordinate hprincipal hF n hn
  refine ⟨φ, D, ht, hsys, ?_⟩
  intro u hu hs W A _hA hz
  exact quasiconformal_compact_zero_gradient hqc φ D
    (D.conductivity_boundedDistortion F n hn hsys) hu hs W A hz

end CircleDomainRigidity

end

end OAI
