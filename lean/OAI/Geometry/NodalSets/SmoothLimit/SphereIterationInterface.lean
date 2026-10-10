import OAI.Geometry.NodalSets.Charts.RoundSphereEnergyData
import OAI.Geometry.NodalSets.Elliptic.IntrinsicOneStep

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff RealInnerProductSpace ENNReal
noncomputable section

structure SphereComparisonPair (r delta : ℝ) where
  energy : SphereEnergyData
  density_smooth : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ energy.density
  comparison : ∀ y ∈ closedBall (0 : BaseModel) r,
    dist ((intrinsicChartCoefficient energy.tensor energy.density seedPoint y,
      fderiv ℝ (intrinsicChartCoefficient energy.tensor energy.density seedPoint) y) : CoefficientFirstJet BaseModel)
      (roundCoefficientJet y) < delta
  support : Set Base
  support_compact : IsCompact support
  support_patch : support ⊆ seedSpherePatch r
  exterior_tensor : ∀ x ∉ support, ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
    energy.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫
  exterior_density : ∀ x ∉ support, energy.density x=1

structure SphereNodalStage (r delta : ℝ) (k : ℕ) extends SphereComparisonPair r delta where
  frequency : ℕ
  frequency_pos : 0 < frequency
  charts : Finset Base
  radius : ℝ
  radius_pos : 0 < radius
  persistence : ∀ (b : SphereEnergyData) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
    sphereCoefficientDistance charts 8 energy.tensor energy.density b.tensor b.density < radius →
    ∃ (mu : ℝ) (v : Base → ℝ), mu ∈ Icc (seedEigenvalue frequency/2) (2*seedEigenvalue frequency) ∧
      0 < mu ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
      (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
        mu*v ((extChartAt (𝓡 4) p).symm y)) ∧
      ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift v) ∧ circleLift v ≠ 0 ∧
      (∀ x : Manifold5, -chartLaplacian
        (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
        (extChartAt modelWithCorners x) (circleLift v) (extChartAt modelWithCorners x x) =
          mu*circleLift v x) ∧
      ENNReal.ofReal ((k:ℝ)+1) < nodalMeasure
        (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
        (circleLift v) / ENNReal.ofReal (Real.sqrt mu)

def SphereStageExtension (r delta : ℝ) : Prop :=
  ∀ (d : SphereComparisonPair r delta) (k : ℕ) (P : Finset Base) (J : ℕ) (eps : ℝ), 0 < eps →
    ∀ n₀ : ℕ, ∃ s : SphereNodalStage r delta k, n₀ ≤ s.frequency ∧ d.support ⊆ s.support ∧
      sphereCoefficientDistance P J d.energy.tensor d.energy.density s.energy.tensor s.energy.density < eps

theorem sphere_iteration_interface :
    ∃ r delta : ℝ, 0 < r ∧ 0 < delta ∧
      (∃ d : SphereComparisonPair r delta, d.energy=roundSphereEnergyData ∧ d.support=∅) ∧
      SphereStageExtension r delta := by
  obtain ⟨r,a,delta,hr,ha,hdelta,hcube,hbranch,H⟩ := intrinsic_one_step
  refine ⟨r,delta,hr,hdelta,?_,?_⟩
  · exact ⟨⟨roundSphereEnergyData,roundSphereEnergyData_density_smooth,
      roundSphereEnergyData_comparison r hdelta,∅,isCompact_empty,empty_subset _,
      roundSphereEnergyData_exterior.1,roundSphereEnergyData_exterior.2⟩,rfl,rfl⟩
  · intro d k P J eps heps n₀
    obtain ⟨n,hn,hn0,b,hb,hclose,hcomp,K,hK,hsub,hKP,hA,hrho,Q,eta,heta,Heta⟩ :=
      H d.energy d.density_smooth d.comparison d.support d.support_compact d.support_patch
        d.exterior_tensor d.exterior_density ((k:ℝ)+1) (by positivity) P J eps heps n₀
    exact ⟨⟨⟨b,hb,hcomp,K,hK,hKP,hA,hrho⟩,n,hn0,Q,eta,heta,Heta⟩,hn,hsub,hclose⟩

end
end Yau.Target

end OAI
