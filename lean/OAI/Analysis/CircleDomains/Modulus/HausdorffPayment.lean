import OAI.Analysis.CircleDomains.Selection.FinitelySuslinian
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-!
# Length payment by crossing a ball

The generic-level-continua proof in Section 1 of `047-02` uses radial
distance on a subcontinuum crossing a ball contained in the physical
domain. Its image contains the radius interval, so one-dimensional
Hausdorff measure pays at least the ball radius.
-/

open Set Metric MeasureTheory
open scoped ENNReal Topology

namespace CircleDomainRigidity

/-- Radial distance is one-Lipschitz and maps a connected set containing
two points onto an interval of length their distance. -/
theorem dist_le_hausdorffMeasure_one_of_preconnected
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {C : Set X} (hC : IsPreconnected C) {p q : X} (hp : p ∈ C) (hq : q ∈ C) :
    ENNReal.ofReal (dist q p) ≤ (μH[1] : Measure X) C := by
  have himage : IsPreconnected ((fun z => dist z p) '' C) :=
    hC.image _ (LipschitzWith.dist_left p).continuous.continuousOn
  have hinterval : Icc 0 (dist q p) ⊆ (fun z => dist z p) '' C :=
    himage.Icc_subset ⟨p, hp, dist_self p⟩ ⟨q, hq, rfl⟩
  calc
    ENNReal.ofReal (dist q p) = (μH[1] : Measure ℝ) (Icc 0 (dist q p)) := by
      rw [hausdorffMeasure_real, Real.volume_Icc]
      simp only [sub_zero]
    _ ≤ (μH[1] : Measure ℝ) ((fun z => dist z p) '' C) := measure_mono hinterval
    _ ≤ (μH[1] : Measure X) C := by
      simpa using (LipschitzWith.dist_left p).hausdorffMeasure_image_le
        (show (0 : ℝ) ≤ 1 by norm_num) C

/-- A compact continuum through the center and exiting a closed ball
pays at least the radius in physical Hausdorff length, provided the ball
lies in the physical domain. No local connectedness is assumed. -/
theorem radius_le_hausdorffMeasure_inter_of_exits_closedBall
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {C G : Set X} (hcompact : IsCompact C) (hconn : IsConnected C)
    {p : X} (hp : p ∈ C) {r : ℝ} (hr : 0 < r)
    (hball : closedBall p r ⊆ G) (hexit : ∃ q ∈ C, r < dist q p) :
    ENNReal.ofReal r ≤ (μH[1] : Measure X) (C ∩ G) := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  let : PreconnectedSpace C := Subtype.preconnectedSpace hconn.isPreconnected
  let pc : C := ⟨p, hp⟩
  let F : Set C := Subtype.val ⁻¹' closedBall p r
  have hFclosed : IsClosed F := isClosed_closedBall.preimage continuous_subtype_val
  have hpF : pc ∈ F := by
    change dist p p ≤ r
    simpa using hr.le
  have hproper : F ≠ univ := by
    obtain ⟨q, hq, hqout⟩ := hexit
    intro heq
    have hqF : (⟨q, hq⟩ : C) ∈ F := by rw [heq]; trivial
    exact (not_le.mpr hqout) hqF
  obtain ⟨z, hz, hzfront⟩ := component_meets_frontier hFclosed hproper hpF
  have hzboundary : z.val ∈ frontier (closedBall p r) :=
    continuous_subtype_val.frontier_preimage_subset _ hzfront
  have hzdist : dist z.val p = r := frontier_closedBall_subset_sphere hzboundary
  let K := connectedComponentIn F pc
  let D : Set X := Subtype.val '' K
  have hDconn : IsPreconnected D :=
    isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
  have hpD : p ∈ D := ⟨pc, mem_connectedComponentIn hpF, rfl⟩
  have hzD : z.val ∈ D := ⟨z, hz, rfl⟩
  have hDsub : D ⊆ C ∩ G := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.property, hball (connectedComponentIn_subset F pc hw)⟩
  calc
    ENNReal.ofReal r = ENNReal.ofReal (dist z.val p) := congrArg _ hzdist.symm
    _ ≤ (μH[1] : Measure X) D :=
      dist_le_hausdorffMeasure_one_of_preconnected hDconn hpD hzD
    _ ≤ (μH[1] : Measure X) (C ∩ G) := measure_mono hDsub

/-- The physical length on `G`, pushed through a monotone quotient,
gives the finite bound on large quotient continua. The remaining
geometric hypothesis supplies a uniformly sized physical ball crossed
by each sufficiently large quotient continuum. -/
theorem finite_large_continuum_bound_of_quotient_length
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Function.Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x})) {G : Set Y}
    (hlength : (μH[1] : Measure Y) G < ∞)
    (hcross : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧
      ∀ C : Set X, IsCompact C → IsConnected C → ε ≤ diam C →
        ∃ p ∈ π ⁻¹' C, closedBall p r ⊆ G ∧ ∃ q ∈ π ⁻¹' C, r < dist q p) :
    HasFiniteLargeContinuumBound X := by
  let ν : Measure Y := (μH[1] : Measure Y).restrict G
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hlength.ne
  let μ : Measure X := ν.map π
  apply finite_large_continuum_bound_of_measure μ
  intro ε hε
  obtain ⟨r, hr, hcrossr⟩ := hcross ε hε
  refine ⟨r, hr, ?_⟩
  intro C hcompact hconn hdiam
  obtain ⟨p, hp, hball, hexit⟩ := hcrossr C hcompact hconn hdiam
  have hCmeas : MeasurableSet C := hcompact.isClosed.measurableSet
  have hprecompact : IsCompact (π ⁻¹' C) := (hcompact.isClosed.preimage hπ).isCompact
  have hpreconn : IsConnected (π ⁻¹' C) :=
    Topology.IsCoinducing.isConnected_preimage_of_isClosed hfiber
      (hπ.isClosedMap.isQuotientMap hπ hsurj).isCoinducing hcompact.isClosed hconn
  have hpay := radius_le_hausdorffMeasure_inter_of_exits_closedBall
    hprecompact hpreconn hp hr hball hexit
  have hμC : μ C = (μH[1] : Measure Y) ((π ⁻¹' C) ∩ G) := by
    change ν.map π C = _
    rw [Measure.map_apply hπ.measurable hCmeas]
    exact Measure.restrict_apply (hCmeas.preimage hπ.measurable)
  have hpay' : ENNReal.ofReal r ≤ μ C := hμC.symm ▸ hpay
  have hreal := ENNReal.toReal_mono (measure_ne_top μ C) hpay'
  simpa only [ENNReal.toReal_ofReal hr.le, measureReal_def] using hreal

end CircleDomainRigidity

end OAI
