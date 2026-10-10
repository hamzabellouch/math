import Mathlib
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.FormalBoxes

namespace OAI

/-! Projective Tangent Box. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

universe u
namespace SplitTangent

attribute [instance] ComplexManifold.topology ComplexManifold.charts
  ComplexManifold.holomorphicAtlas ComplexManifold.hausdorff
  ComplexManifold.secondCountable

namespace FormalCauchy

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

instance projectiveTangentBoxAnalyticFunctionCoeFun (U : Set ℂ) :
    CoeFun (AnalyticFunction U) (fun _ => ℂ → ℂ) := ⟨Subtype.val⟩

open scoped MvPowerSeries.WithPiTopology

end FormalCauchy
end SplitTangent

open Set Filter Topology

namespace SplitTangent.TangentSplitting
open HolomorphicJets
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

theorem coordinateCurve_analyticAlternative {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) :
    AnalyticOnNhd ℂ (coordinateCurve g x) (coordinateDomain g x) := by
  intro z hz
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hz
  exact (hc.comp z (hg z)).contDiffAt.analyticAt

 

def localJetAlternative {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g) (x : X.Carrier) :
    ℕ → ℂ → Model X := Classical.choose
  (exists_cauchyOn (coordinateDomain_open hg x) (coordinateCurve g x)
    (fun i z hz => analyticAt_pi_iff.mp (coordinateCurve_analyticAlternative hg x z hz) i)
    (S.coordinateMatrix x) (fun i j _ hz => S.coordinateMatrix_analytic x i j _
      ((chartAt (Model X) x).map_source hz)))

end SplitTangent.TangentSplitting

open Filter Topology

section FiniteBaseImport
open Polynomial
namespace SplitTangent.RationalSurface

local instance projectiveTangentBoxDecidableEq : DecidableEq K := Classical.decEq K

variable {ι : Type*} [Fintype ι]

end SplitTangent.RationalSurface

end FiniteBaseImport

open Filter Topology

open Filter Topology Metric Set

 

open MvPowerSeries

open Filter Topology Set Metric

end

end OAI
