import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalSmooth
import OAI.Geometry.TamingCompatibility.Hodge.HodgeClosedSmooth

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in
lemma hodgeSmoothShift_power_closed_iff (r : ℝ) (j : ℕ) (a : PreL2 A J α hs ht true) :
    IsClosed ((hodgeSmoothShift A J α hs ht r ^ j) a).val ↔ IsClosed a.val := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ']
    change IsClosed (hodgeSmoothShift A J α hs ht r ((hodgeSmoothShift A J α hs ht r ^ j) a)).val ↔ _
    rw [hodgeSmoothShift_closed_iff,ih]

def hodgeIsExact (a : PreL2 A J α hs ht true) : Prop :=
  ∃ ξ : PreL2 A J α hs ht false, a = hodgePreD A J α hs ht ξ

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma hodgeIsExact_closed (a : PreL2 A J α hs ht true) (ha : hodgeIsExact A J α hs ht a) :
    IsClosed a.val := by
  obtain ⟨ξ,rfl⟩ := ha
  exact hodgePreD_closed A J α hs ht ξ

omit [T2Space X] in
lemma hodgeSmoothShift_exact_iff (r : ℝ) (a : PreL2 A J α hs ht true) :
    hodgeIsExact A J α hs ht (hodgeSmoothShift A J α hs ht r a) ↔ hodgeIsExact A J α hs ht a := by
  constructor
  · intro ha
    have hc := (hodgeSmoothShift_closed_iff A J α hs ht r a).mp
      (hodgeIsExact_closed A J α hs ht _ ha)
    obtain ⟨ξ,hξ⟩ := ha
    refine ⟨ξ-r^2 • hodgeDelta A J α hs ht a,?_⟩
    rw [map_sub,map_smul,← hξ,hodgeSmoothShift_apply,hodgeLaplacian_closed A J α hs ht a hc]
    simp only [add_sub_cancel_right]
  · intro ha
    have hc := hodgeIsExact_closed A J α hs ht a ha
    obtain ⟨ξ,hξ⟩ := ha
    refine ⟨ξ+r^2 • hodgeDelta A J α hs ht a,?_⟩
    rw [map_add,map_smul,← hξ,hodgeSmoothShift_apply,hodgeLaplacian_closed A J α hs ht a hc]

omit [T2Space X] in
lemma hodgeSmoothShift_power_exact_iff (r : ℝ) (j : ℕ) (a : PreL2 A J α hs ht true) :
    hodgeIsExact A J α hs ht ((hodgeSmoothShift A J α hs ht r ^ j) a) ↔ hodgeIsExact A J α hs ht a := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ']
    change hodgeIsExact A J α hs ht (hodgeSmoothShift A J α hs ht r
      ((hodgeSmoothShift A J α hs ht r ^ j) a)) ↔ _
    rw [hodgeSmoothShift_exact_iff,ih]

omit [T2Space X] in
lemma hodgeRegularization_smooth_inverse (r : ℝ) (hr : 0 < r) (f b : PreL2 A J α hs ht true)
    (hb : smoothL2 A J α hs ht true b = hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true f)) :
    (hodgeSmoothShift A J α hs ht r ^ 3) b = f := by
  apply (smoothL2 A J α hs ht true).injective
  apply hodgeRegularization_injective A J α hs ht r hr
  rw [hodgeRegularization_smoothShift_cube A J α hs ht r hr,hb]

include D hD in

theorem hodgeRegularization_smooth_closed_exact (r : ℝ) (hr : 0 < r)
    (f : PreL2 A J α hs ht true) :
    ∃ b : PreL2 A J α hs ht true,
      smoothL2 A J α hs ht true b = hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true f) ∧
      (IsClosed b.val ↔ IsClosed f.val) ∧
      (hodgeIsExact A J α hs ht b ↔ hodgeIsExact A J α hs ht f) := by
  obtain ⟨b,hb⟩ := hodgeRegularization_smooth A J α hs ht D hD r hr f
  have hi := hodgeRegularization_smooth_inverse A J α hs ht r hr f b hb
  refine ⟨b,hb,?_,?_⟩
  · rw [← hi,hodgeSmoothShift_power_closed_iff]
  · rw [← hi,hodgeSmoothShift_power_exact_iff]
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
