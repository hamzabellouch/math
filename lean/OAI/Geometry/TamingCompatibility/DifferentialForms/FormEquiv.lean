import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Linear
import OAI.Geometry.TamingCompatibility.DifferentialForms.Form

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.MetricHodge
open ContinuousAlternatingMap MetricForms MetricModel ExteriorForms
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

def formEquiv (g : Metric E) (k : ℕ) :
    MetricForms.Form E k ≃L[ℝ] MetricForms.Form (MetricModel.Model g) k :=
  (equiv g).symm.continuousAlternatingMapCongrLeft

lemma formEquiv_apply (g : Metric E) {k : ℕ} (α : MetricForms.Form E k)
    (v : Fin k → MetricModel.Model g) : formEquiv g k α v = α (fun i => (equiv g) (v i)) := rfl

lemma formEquiv_symm_apply (g : Metric E) {k : ℕ}
    (α : MetricForms.Form (MetricModel.Model g) k) (v : Fin k → E) :
    (formEquiv g k).symm α v = α (fun i => (equiv g).symm (v i)) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
lemma volumeSquare_comp (F : MetricForms.Form D 2) (L : E →L[ℝ] D) :
    volumeSquare (F.compContinuousLinearMap L) = (volumeSquare F).compContinuousLinearMap L := by
  ext v
  have hv : v = ![v 0,v 1,v 2,v 3] := by ext i; fin_cases i <;> rfl
  rw [hv, volumeSquare_apply]
  have hc : ((volumeSquare F).compContinuousLinearMap L) ![v 0,v 1,v 2,v 3] =
      volumeSquare F ![L (v 0), L (v 1), L (v 2), L (v 3)] := by
    change volumeSquare F (fun i => L (![v 0,v 1,v 2,v 3] i)) = _
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [hc,volumeSquare_apply]
  simp only [MetricForms.comp_two]

def starTwo (g : Metric E) (J : E →L[ℝ] E) (F α : MetricForms.Form E 2) :
    MetricForms.Form E 2 := pairing g α F • F - α.compContinuousLinearMap J

lemma formEquiv_starTwo (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (F α : MetricForms.Form E 2) :
    formEquiv g 2 (starTwo g J F α) =
      HermitianHodge.star (isometry g J hJ).toContinuousLinearMap
        (formEquiv g 2 F) (formEquiv g 2 α) := by
  ext v
  rfl

def starThree (g : Metric E) (F : MetricForms.Form E 2) (α : MetricForms.Form E 3) :
    MetricForms.Form E 1 :=
  (formEquiv g 1).symm (HodgeThree.star (formEquiv g 2 F) (formEquiv g 3 α))

lemma starThree_apply (g : Metric E) (F : MetricForms.Form E 2) (α : MetricForms.Form E 3) (u : E) :
    starThree g F α ![u] = -pairing g α ((volumeSquare F).curryLeft u) := by
  change HodgeThree.star (formEquiv g 2 F) (formEquiv g 3 α)
    ((fun i => (equiv g).symm (![u] i))) = _
  have hv : (fun i => (equiv g).symm (![u] i)) = ![(equiv g).symm u] := by
    ext i; fin_cases i; rfl
  rw [hv,HodgeThree.star_apply]
  congr 1
  change FormMetric.pairing _ _ = FormMetric.pairing _ _
  congr 1
  change (volumeSquare (F.compContinuousLinearMap (equiv g))).curryLeft ((equiv g).symm u) =
    ((volumeSquare F).curryLeft u).compContinuousLinearMap (equiv g)
  rw [volumeSquare_comp]
  ext v
  change volumeSquare F (fun i => (equiv g) ((Matrix.vecCons ((equiv g).symm u) v) i)) =
    volumeSquare F (Matrix.vecCons u (fun i => (equiv g) (v i)))
  congr 1

variable (g : Metric E) (J : E →L[ℝ] E)
  (hJ : ∀ u, J (J u) = -u)
  (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
  (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
  (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)

include hJ horth hdim hF
lemma starTwo_square (α : MetricForms.Form E 2) :
    starTwo g J F (starTwo g J F α) = α := by
  apply (formEquiv g 2).injective
  rw [formEquiv_starTwo g J horth,formEquiv_starTwo g J horth]
  exact HermitianHodge.star_square (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF _

lemma starThree_injective : Function.Injective (starThree g F) := by
  intro α β h
  apply (formEquiv g 3).injective
  have hp := HodgeThree.star_injective (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF
  apply hp
  exact (formEquiv g 1).symm.injective h

omit hJ horth hdim hF in
lemma starThree_zero : starThree g F 0 = 0 := by
  rw [starThree,_root_.map_zero,HodgeThree.star_zero,_root_.map_zero]

lemma starThree_eq_zero (α : MetricForms.Form E 3) : starThree g F α = 0 ↔ α = 0 := by
  rw [← starThree_zero g F]
  exact (starThree_injective g J hJ horth hdim F hF).eq_iff

end TamingCompatibility.MetricHodge

end

end OAI
