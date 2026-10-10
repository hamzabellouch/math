import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.NormalEikonal

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section DividedHessian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
end DividedHessian
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section CrossingValue
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma doubleNormalCost_self_contDiffAt {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈injectivityDomain x) :
    ContDiffAt ℝ ∞ (doubleNormalCost (n := n) x x) (0,p) := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  have hu : ContMDiffAt 𝓘(ℝ,X×X) 𝓘(ℝ,Model n) ∞
      (fun z : X×X => riemannianExp x z.1) (0,p) :=
    (contMDiff_riemannianExp_fiber x _).comp (0,p) contDiffAt_fst.contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,X×X) 𝓘(ℝ,Model n) ∞
      (fun z : X×X => riemannianExp x z.2) (0,p) :=
    (contMDiff_riemannianExp_fiber x _).comp (0,p) contDiffAt_snd.contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:X),riemannianExp x p) := by
    simpa only [riemannianExp_zero] using hc
  exact (hc'.comp (0,p) (hu.prodMk hv)).contDiffAt

def radialCrossingValue (x : M) (p v : TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  let B := doubleNormalCost x x
  fderiv ℝ (fderiv ℝ B) (0,p) (v,0) (v,0) -
    fderiv ℝ (fderiv ℝ (fderiv ℝ B)) (0,p) (0,p) (v,0) (v,0)
end CrossingValue
end WeakMTWTransport

end

end

end

end OAI
