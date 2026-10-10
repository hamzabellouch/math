import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.LocalCodifferential
import OAI.Geometry.TamingCompatibility.Functional.MetricL2Completion

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
lemma antiInvariantPart_add (J : AlmostComplexStructure X) (a b : TwoForm X) :
    antiInvariantPart J (a+b) = antiInvariantPart J a + antiInvariantPart J b := by
  simp only [antiInvariantPart,jAction_add,add_sub_add_comm,smul_add]
lemma antiInvariantPart_smul (J : AlmostComplexStructure X) (c : ℝ) (a : TwoForm X) :
    antiInvariantPart J (c • a) = c • antiInvariantPart J a := by
  simp only [antiInvariantPart,jAction_smul]
  module

namespace ManifoldHodge
lemma starThree_add (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : ManifoldForms.Form X 3) : starThree J α ht (a+b) =
      starThree J α ht a + starThree J α ht b := by
  funext x
  change MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x) (invariantPart J α x)
      (a x+b x) = MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
      (invariantPart J α x) (a x) + MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
      (invariantPart J α x) (b x)
  exact MetricHodge.starThree_add _ _ _ _
lemma starThree_smul (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (c : ℝ) (a : ManifoldForms.Form X 3) : starThree J α ht (c • a) =
      c • starThree J α ht a := by
  funext x
  change MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x) (invariantPart J α x)
      (c • a x) = c • MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x)
      (invariantPart J α x) (a x)
  exact MetricHodge.starThree_smul _ _ _ _
lemma codifferential_anti (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    {a : TwoForm X} (ha : antiInvariantPart J a = a) :
    codifferential J α ht a = -starThree J α ht (ManifoldForms.exteriorDerivative a) := by
  have he : starTwo J α ht a = a := by
    conv_lhs => rw [← ha]
    exact (starTwo_antiInvariant J α ht a).trans ha
  rw [codifferential,he]
end ManifoldHodge

namespace GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def antiPre : Submodule ℝ (PreL2 A J α hs ht true) where
  carrier := {a | antiInvariantPart J a.val = a.val}
  zero_mem' := by
    change antiInvariantPart J 0 = 0
    have he := antiInvariantPart_smul J 0 (0 : TwoForm X)
    simpa only [zero_smul] using he
  add_mem' := by
    intro a b ha hb
    change antiInvariantPart J (a.val+b.val) = a.val+b.val
    rw [antiInvariantPart_add,ha,hb]
  smul_mem' := by
    intro c a ha
    change antiInvariantPart J (c • a.val) = c • a.val
    rw [antiInvariantPart_smul,ha]

def antiDelta : antiPre A J α hs ht →ₗ[ℝ] PreL2 A J α hs ht false where
  toFun a := ⟨codifferential J α ht a.val.val, GeometricAdjoint.codifferential_smooth J α hs ht a.val.property⟩
  map_add' a b := by
    apply Subtype.ext
    change codifferential J α ht (a.val.val+b.val.val) =
      codifferential J α ht a.val.val + codifferential J α ht b.val.val
    have ha : antiInvariantPart J a.val.val = a.val.val := a.property
    have hb : antiInvariantPart J b.val.val = b.val.val := b.property
    have hsa : Smooth a.val.val := a.val.property
    have hsb : Smooth b.val.val := b.val.property
    have hab : antiInvariantPart J (a.val.val+b.val.val) = a.val.val+b.val.val := by
      with_reducible rw [antiInvariantPart_add,ha,hb]
    with_reducible rw [codifferential_anti J α ht hab,
      codifferential_anti J α ht ha,codifferential_anti J α ht hb,
      exteriorDerivative_add hsa hsb,starThree_add,neg_add]
  map_smul' c a := by
    apply Subtype.ext
    change codifferential J α ht (c • a.val.val) = c • codifferential J α ht a.val.val
    have ha : antiInvariantPart J a.val.val = a.val.val := a.property
    have hca : antiInvariantPart J (c • a.val.val) = c • a.val.val := by
      with_reducible rw [antiInvariantPart_smul,ha]
    with_reducible rw [codifferential_anti J α ht hca,
      codifferential_anti J α ht ha,exteriorDerivative_smul,starThree_smul,smul_neg]

def antiGraph : antiPre A J α hs ht →ₗ[ℝ]
    WithLp 2 (L2 A J α hs ht true × L2 A J α hs ht false) :=
  (WithLp.linearEquiv 2 ℝ (L2 A J α hs ht true × L2 A J α hs ht false)).symm.toLinearMap.comp <|
  ((smoothL2 A J α hs ht true).toLinearMap.comp (antiPre A J α hs ht).subtype).prod
    ((smoothL2 A J α hs ht false).toLinearMap.comp (antiDelta A J α hs ht))

def antiEnergy : Submodule ℝ (WithLp 2 (L2 A J α hs ht true × L2 A J α hs ht false)) :=
  (LinearMap.range (antiGraph A J α hs ht)).topologicalClosure

instance antiEnergy_complete : CompleteSpace (antiEnergy A J α hs ht) :=
  ((LinearMap.range (antiGraph A J α hs ht)).isClosed_topologicalClosure).completeSpace_coe

end GeometricHilbert
end TamingCompatibility

end
end

end
end
end

end OAI
