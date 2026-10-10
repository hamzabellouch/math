import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.AntiEnergy

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def testDerivative (b : PreL2 A J α hs ht false) : L2 A J α hs ht true :=
  smoothL2 A J α hs ht true ⟨exteriorDerivative b.val,b.property.exteriorDerivative⟩

lemma antiGraph_weak (a : antiPre A J α hs ht) (b : PreL2 A J α hs ht false) :
    inner ℝ (testDerivative A J α hs ht b) (antiGraph A J α hs ht a).fst =
      inner ℝ (smoothL2 A J α hs ht false b) (antiGraph A J α hs ht a).snd := by
  let db : PreL2 A J α hs ht true := ⟨exteriorDerivative b.val,b.property.exteriorDerivative⟩
  have h := GeometricAdjoint.formal_adjoint A J α hs ht b.property a.val.property
  have he : l2Pairing A J α ht db a.val = l2Pairing A J α ht b (antiDelta A J α hs ht a) := h
  exact ((smoothL2 A J α hs ht true).inner_map_map db a.val).trans
    ((preL2_inner A J α hs ht true db a.val).trans (he.trans
      (((smoothL2 A J α hs ht false).inner_map_map b (antiDelta A J α hs ht a)).trans
        (preL2_inner A J α hs ht false b (antiDelta A J α hs ht a))).symm))

lemma antiEnergy_weak (u : antiEnergy A J α hs ht) (b : PreL2 A J α hs ht false) :
    inner ℝ (testDerivative A J α hs ht b) u.val.fst =
      inner ℝ (smoothL2 A J α hs ht false b) u.val.snd := by
  let S : Set (WithLp 2 (L2 A J α hs ht true × L2 A J α hs ht false)) :=
    {v | inner ℝ (testDerivative A J α hs ht b) v.fst =
      inner ℝ (smoothL2 A J α hs ht false b) v.snd}
  have hc : _root_.IsClosed S := isClosed_eq
    (continuous_const.inner (WithLp.fstL 2 ℝ _ _).continuous)
    (continuous_const.inner (WithLp.sndL 2 ℝ _ _).continuous)
  have hr : (LinearMap.range (antiGraph A J α hs ht) : Set _) ⊆ S := by
    rintro _ ⟨a,rfl⟩
    exact antiGraph_weak A J α hs ht a b
  exact (closure_minimal hr hc) u.property

lemma antiEnergy_fst_injective : Function.Injective
    (fun u : antiEnergy A J α hs ht => u.val.fst) := by
  suffices hz : ∀ u : antiEnergy A J α hs ht, u.val.fst = 0 → u = 0 by
    intro u v huv
    have he : u-v=0 := hz (u-v) (by change u.val.fst - v.val.fst = 0; exact sub_eq_zero.mpr huv)
    exact sub_eq_zero.mp he
  intro u hu
  have htest (b : PreL2 A J α hs ht false) :
      inner ℝ (smoothL2 A J α hs ht false b) u.val.snd = 0 := by
    rw [← antiEnergy_weak A J α hs ht u b,hu,inner_zero_right]
  have hall : ∀ v : L2 A J α hs ht false, inner ℝ v u.val.snd = 0 := by
    intro v
    exact (smoothL2_dense A J α hs ht false).induction_on v
      (isClosed_eq (continuous_id.inner continuous_const) continuous_const) htest
  have hz : u.val.snd = 0 := inner_self_eq_zero.mp (hall u.val.snd)
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℝ (L2 A J α hs ht true × L2 A J α hs ht false)).injective
  exact Prod.ext hu hz
end TamingCompatibility.GeometricHilbert

end

end OAI
