import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricL2Core

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldLocalization
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def PreL2 (_A : FiniteCharts X) (_J : AlmostComplexStructure X) (_α : TwoForm X)
    (_hs : IsSmooth _α) (_ht : Tames _α _J) (k : Bool) : Type _ := ↥(smoothForms X (if k then 2 else 1))

instance preL2Add (k : Bool) : AddCommGroup (PreL2 A J α hs ht k) :=
  inferInstanceAs (AddCommGroup (smoothForms X (if k then 2 else 1)))
instance preL2Module (k : Bool) : Module ℝ (PreL2 A J α hs ht k) :=
  inferInstanceAs (Module ℝ (smoothForms X (if k then 2 else 1)))

@[instance_reducible] def preL2Core (k : Bool) :
    InnerProductSpace.Core ℝ (PreL2 A J α hs ht k) := by
  cases k
  · exact oneCore A J α hs ht
  · exact twoCore A J α hs ht

instance preL2Normed (k : Bool) : NormedAddCommGroup (PreL2 A J α hs ht k) :=
  letI := preL2Core A J α hs ht k
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
instance preL2Inner (k : Bool) : InnerProductSpace ℝ (PreL2 A J α hs ht k) :=
  InnerProductSpace.ofCore (preL2Core A J α hs ht k).toCore

lemma preL2_inner (k : Bool) (a b : PreL2 A J α hs ht k) :
    inner ℝ a b = l2Pairing A J α ht a b := by
  cases k <;> rfl

lemma preL2_norm_sq (k : Bool) (a : PreL2 A J α hs ht k) :
    ‖a‖^2 = l2Pairing A J α ht a a := by
  rw [← real_inner_self_eq_norm_sq,preL2_inner]

abbrev L2 (k : Bool) := UniformSpace.Completion (PreL2 A J α hs ht k)

def smoothL2 (k : Bool) : PreL2 A J α hs ht k →ₗᵢ[ℝ] L2 A J α hs ht k :=
  UniformSpace.Completion.toComplₗᵢ

lemma smoothL2_dense (k : Bool) : DenseRange (smoothL2 A J α hs ht k) :=
  UniformSpace.Completion.denseRange_coe

end TamingCompatibility.GeometricHilbert

end

end OAI
