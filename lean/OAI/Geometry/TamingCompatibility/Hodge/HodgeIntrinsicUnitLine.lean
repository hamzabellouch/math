import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeUnitKernelBounds
import OAI.Geometry.TamingCompatibility.Hodge.HodgeDirectionCoordinates

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] in
lemma exists_intrinsic_unit_line (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hx : (extChartAt Model p).symm q = u.val.proj) :
    ∃ v : UnitaryFrame.V, ‖v‖ = 1 ∧ ∀ a : TwoForm X,
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) =
        ⟪HodgeChart.rawVector J α ht p D a q,UnitaryFrame.line v⟫ := by
  have hqt := D.domain_subset hq
  have hall : ∀ w : TangentSpace Model ((extChartAt Model p).symm q),
      (hermitianMetric J α hs ht).inner _ w w = 1 →
      ∃ v : UnitaryFrame.V, ‖v‖ = 1 ∧ ∀ a : TwoForm X,
        eval a ((extChartAt Model p).symm q) w (J.endomorphism _ w) =
          ⟪HodgeChart.rawVector J α ht p D a q,UnitaryFrame.line v⟫ := by
    intro w hw
    let L := inverseChartEquiv p q hqt
    let c : Space := L.symm w
    let v := directionCoordinates (coordinateMetric J α ht p q)
      (by simp [Space]) (fun i => D.frame i q) (D.frame_gram q hq) c
    have he : L c = w := L.apply_symm_apply w
    have hc : (coordinateMetric J α ht p q).bilinear c c = 1 := by
      rw [coordinateMetric_bilinear J α ht p hqt,chartMetric_derivative J α p hqt]
      have he' : mfderiv Model Model (extChartAt Model p).symm q c = w := by
        rw [← inverseChartEquiv_coe p q hqt]
        exact he
      rw [he']
      exact hw
    refine ⟨v,norm_directionCoordinates _ _ _ _ c hc,?_⟩
    intro a
    obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex q hq
    calc
      _ = ManifoldForms.pullback a (extChartAt Model p).symm q ![c,coordinateJ J p q c] := by
        rw [GeometricChart.pullback_complexLine J a p hqt,← inverseChartEquiv_coe p q hqt]
        exact congrArg (fun z => eval a ((extChartAt Model p).symm q) z (J.endomorphism _ z)) he.symm
      _ = _ := coordinates_direction_eval _ _ _ (D.frame_gram q hq)
        (coordinateJ J p q) h0 h1 h2 h3 _ c
  rw [hx] at hall
  exact hall u.val.2 u.property

omit [CompactSpace X] [T2Space X] in
lemma rawVector_pairing (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain) (a b : TwoForm X) :
    ⟪HodgeChart.rawVector J α ht p D a q,HodgeChart.rawVector J α ht p D b q⟫ =
      GeometricAdjoint.pairing J α ht a b ((extChartAt Model p).symm q) := by
  unfold HodgeChart.rawVector
  rw [coordinates_pairing _ (by simp [Space]) _ (D.frame_gram q hq),
    GeometricAdjoint.pairing_two_chart J α ht p a b (D.domain_subset hq)]

omit [CompactSpace X] [T2Space X] in
lemma rawVector_constant_test (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain) (v : UnitaryFrame.W) :
    HodgeChart.rawVector J α ht p D (HodgeChart.manifoldTest J α ht p D (fun _ => v)) q = v := by
  unfold HodgeChart.rawVector
  rw [HodgeChart.pullback_manifoldTest J α ht p D _ (D.domain_subset hq)]
  exact coordinates_reconstruct _ _ (D.frame_gram q hq) v

omit [CompactSpace X] [T2Space X] in
lemma rawVector_star (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain) (a : TwoForm X) :
    HodgeChart.rawVector J α ht p D (starTwo J α ht a) q =
      UnitaryFrame.star (HodgeChart.rawVector J α ht p D a q) := by
  unfold HodgeChart.rawVector
  rw [pullback_starTwo J α ht a p (D.domain_subset hq)]
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex q hq
  exact coordinates_star _ (by simp [Space]) _ (D.frame_gram q hq)
    (coordinateJ J p q) (coordinateMetric_hermitian J α ht p (D.domain_subset hq))
    h0 h1 h2 h3 _ (ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hq)) _

include hE in
omit [CompactSpace X] [T2Space X] in
lemma framePairing_coordinateEncode (p : A.centers) {q : Space}
    (hq : q ∈ (E p).chart.domain) (a : TwoForm X) (v : UnitaryFrame.W) :
    framePairing A J α ht E a ((extChartAt Model p.val).symm q)
      (coordinateEncode J α ht A E p q v) =
        ⟪HodgeChart.rawVector J α ht p.val (E p).chart a q,v⟫ := by
  rw [framePairing_apply]
  erw [← rawVector_pairing J α ht p.val (E p).chart hq,
    ← coordinateDecode_rawVector J α ht A E p q,
    coordinateDecode_encode J α ht A E hE p hq]

lemma exists_unitDual_raw_line (p : A.centers) {q : Space} (hq : q ∈ (E p).chart.domain)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hx : (extChartAt Model p.val).symm q = u.val.proj) :
    ∃ v : UnitaryFrame.V, ‖v‖ = 1 ∧
      HodgeChart.rawVector J α ht p.val (E p).chart
        (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val q = UnitaryFrame.line v := by
  obtain ⟨v,hv,heval⟩ := exists_intrinsic_unit_line J α hs ht p.val (E p).chart hq u hx
  refine ⟨v,hv,?_⟩
  apply ext_inner_right ℝ
  intro w
  let a := HodgeChart.manifoldTest J α ht p.val (E p).chart (fun _ => w)
  have ha : HodgeChart.rawVector J α ht p.val (E p).chart a q = w :=
    rawVector_constant_test J α ht p.val (E p).chart hq w
  rw [← ha,rawVector_pairing J α ht p.val (E p).chart hq,hx,
    unitDual_pairing A J α hs ht E hE (hermitianMetric J α hs ht) a u,heval a,real_inner_comm]

lemma exists_unitDual_coordinate_line (p : A.centers) {q : Space} (hq : q ∈ (E p).chart.domain)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hx : (extChartAt Model p.val).symm q = u.val.proj) :
    ∃ v : UnitaryFrame.V, ‖v‖ = 1 ∧
      coordinateDecode J α ht A E p q
        (frameEncode J α ht A E u.val.proj
          ((unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val u.val.proj)) =
          UnitaryFrame.line v ∧
      coordinateDecode J α ht A E p q
        (frameEncode J α ht A E u.val.proj
          ((starTwo J α ht (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val) u.val.proj)) =
          UnitaryFrame.star (UnitaryFrame.line v) ∧
      ∀ w : UnitaryFrame.W,
        framePairing A J α ht E (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val
          u.val.proj (coordinateEncode J α ht A E p q w) = ⟪UnitaryFrame.line v,w⟫ := by
  obtain ⟨v,hv,he⟩ := exists_unitDual_raw_line A J α hs ht E hE p hq u hx
  refine ⟨v,hv,?_,?_,?_⟩
  · rw [← hx,← coordinateEncode_rawVector J α ht A E p _ hq,
      coordinateDecode_encode J α ht A E hE p hq,he]
  · rw [← hx,← coordinateEncode_rawVector J α ht A E p _ hq,
      coordinateDecode_encode J α ht A E hE p hq,rawVector_star J α ht p.val (E p).chart hq,he]
  · intro w
    rw [← hx,framePairing_coordinateEncode A J α ht E hE p hq,he]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

lemma unitDual_starDirection (u : MetricUnit (hermitianMetric J α hs ht)) :
    frameEncode J α ht A E u.val.proj
      ((starTwo J α ht (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val) u.val.proj) =
      unitStarDirection A J α ht E (hermitianMetric J α hs ht) u := by
  ext i
  rw [frameEncode_apply]
  rw [hodgeStar_pairing]
  exact unitDual_pairing A J α hs ht E hE (hermitianMetric J α hs ht)
    (starTwo J α ht (globalFrame J α ht A E i.1 i.2)) u

include hE in
lemma coordinateWedge_lines (p : A.centers) {q y : Space}
    (hq : q ∈ (E p).chart.domain) (hy : y ∈ (E p).chart.domain)
    (u v : MetricUnit (hermitianMetric J α hs ht))
    (hu : (extChartAt Model p.val).symm y = u.val.proj)
    (hv : (extChartAt Model p.val).symm q = v.val.proj) :
    ∃ a b : UnitaryFrame.V, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
      ∀ K : Space × Space → UnitaryFrame.W →L[ℝ] UnitaryFrame.W,
        unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
          (coordinateMatrix J α ht A E p K (q,y)
            (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v)) =
          ⟪UnitaryFrame.line a, K (q,y) (UnitaryFrame.star (UnitaryFrame.line b))⟫ := by
  obtain ⟨a,ha,_,_,hpa⟩ := exists_unitDual_coordinate_line A J α hs ht E hE p hy u hu
  obtain ⟨b,hb,_,hdb,_⟩ := exists_unitDual_coordinate_line A J α hs ht E hE p hq v hv
  refine ⟨a,b,ha,hb,fun K => ?_⟩
  rw [unitFrameFunctional_eq A J α hs ht E hE,← unitDual_starDirection A J α hs ht E hE]
  change framePairing A J α ht E (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val
    u.val.proj (coordinateEncode J α ht A E p y (K (q,y)
      (coordinateDecode J α ht A E p q _))) = _
  rw [hdb,hpa]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
