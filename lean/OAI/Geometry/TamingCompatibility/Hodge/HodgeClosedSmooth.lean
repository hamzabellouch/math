import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothLaplacian

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma preStar_self_adjoint (a b : PreL2 A J α hs ht true) :
    ⟪preStar A J α hs ht a,b⟫ = ⟪a,preStar A J α hs ht b⟫ := by
  conv_lhs => rw [← preStar_square A J α hs ht b]
  exact (preStar A J α hs ht).inner_map_map a (preStar A J α hs ht b)

lemma hodgePreD_adjoint (a : PreL2 A J α hs ht false) (b : PreL2 A J α hs ht true) :
    ⟪hodgePreD A J α hs ht a,b⟫ = ⟪a,hodgeDelta A J α hs ht b⟫ := by
  have h := hodgeGraph_weak A J α hs ht b a
  change ⟪smoothL2 A J α hs ht true (hodgePreD A J α hs ht a),
    smoothL2 A J α hs ht true b⟫ =
      ⟪smoothL2 A J α hs ht false a,smoothL2 A J α hs ht false (hodgeDelta A J α hs ht b)⟫ at h
  simpa only [(smoothL2 A J α hs ht true).inner_map_map,
    (smoothL2 A J α hs ht false).inner_map_map] using h

lemma hodgeDelta_star_eq_zero_iff (a : PreL2 A J α hs ht true) :
    hodgeDelta A J α hs ht (preStar A J α hs ht a) = 0 ↔ IsClosed a.val := by
  change _ ↔ ManifoldForms.Closed (a.val : Form X 2)
  rw [closed_iff_exteriorDerivative_eq_zero (α := (a.val : Form X 2)) a.property]
  change (⟨codifferential J α ht (starTwo J α ht a.val),_⟩ : PreL2 A J α hs ht false) = 0 ↔ _
  rw [Subtype.ext_iff]
  change -starThree J α ht (exteriorDerivative (starTwo J α ht (starTwo J α ht a.val))) = 0 ↔ _
  rw [starTwo_square,neg_eq_zero,starThree_eq_zero]

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma hodgePreD_closed (a : PreL2 A J α hs ht false) :
    IsClosed (hodgePreD A J α hs ht a).val := a.property.closed_exteriorDerivative

def hodgeCoexactPart (a : PreL2 A J α hs ht true) : PreL2 A J α hs ht true :=
  preStar A J α hs ht (hodgePreD A J α hs ht
    (hodgeDelta A J α hs ht (preStar A J α hs ht a)))

lemma hodgeCoexactPart_pair (a b : PreL2 A J α hs ht true) :
    ⟪hodgeCoexactPart A J α hs ht a,b⟫ =
      ⟪hodgeDelta A J α hs ht (preStar A J α hs ht a),
        hodgeDelta A J α hs ht (preStar A J α hs ht b)⟫ := by
  rw [hodgeCoexactPart,preStar_self_adjoint,hodgePreD_adjoint]

lemma hodgeCoexactPart_closed_pair (a b : PreL2 A J α hs ht true)
    (hb : IsClosed b.val) : ⟪hodgeCoexactPart A J α hs ht a,b⟫ = 0 := by
  rw [hodgeCoexactPart_pair,(hodgeDelta_star_eq_zero_iff A J α hs ht b).mpr hb,inner_zero_right]

lemma hodgeLaplacian_closed (a : PreL2 A J α hs ht true) (ha : IsClosed a.val) :
    hodgeLaplacian A J α hs ht a = hodgePreD A J α hs ht (hodgeDelta A J α hs ht a) := by
  rw [hodgeLaplacian_apply,(hodgeDelta_star_eq_zero_iff A J α hs ht a).mpr ha,map_zero,map_zero,add_zero]

lemma hodgeSmoothShift_closed_iff (r : ℝ) (a : PreL2 A J α hs ht true) :
    IsClosed (hodgeSmoothShift A J α hs ht r a).val ↔ IsClosed a.val := by
  constructor
  · intro ha
    let v := hodgeCoexactPart A J α hs ht a
    have h := hodgeCoexactPart_closed_pair A J α hs ht a
      (hodgeSmoothShift A J α hs ht r a) ha
    rw [hodgeSmoothShift_apply,inner_add_right,real_inner_smul_right,hodgeLaplacian_apply,
      inner_add_right,hodgeCoexactPart_closed_pair A J α hs ht a
        (hodgePreD A J α hs ht (hodgeDelta A J α hs ht a))
        (hodgePreD_closed A J α hs ht _),zero_add] at h
    change ⟪v,a⟫ + r^2*⟪v,v⟫ = 0 at h
    have hp : 0 ≤ r^2*⟪v,v⟫ := mul_nonneg (sq_nonneg _) real_inner_self_nonneg
    have he : ⟪hodgeDelta A J α hs ht (preStar A J α hs ht a),
        hodgeDelta A J α hs ht (preStar A J α hs ht a)⟫ = 0 := by
      rw [← hodgeCoexactPart_pair]
      exact le_antisymm (by linarith) (by rw [hodgeCoexactPart_pair]; exact real_inner_self_nonneg)
    exact (hodgeDelta_star_eq_zero_iff A J α hs ht a).mp (inner_self_eq_zero.mp he)
  · intro ha
    rw [hodgeSmoothShift_apply,hodgeLaplacian_closed A J α hs ht a ha]
    exact IsClosed.add ha ((hodgePreD_closed A J α hs ht _).smul _)
      a.property ((hodgePreD A J α hs ht (hodgeDelta A J α hs ht a)).property.smul _)
end TamingCompatibility.GeometricHilbert

end

end OAI
