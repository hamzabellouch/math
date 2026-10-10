import OAI.Analysis.CircleDomains.Uniformization.BandLimits
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

/-!
# Haar measure of a projected band

The projection of a real interval of length `b - a` is contained in
the circle ball with midpoint `(a + b) / 2` and radius `(b - a) / 2`.
This gives the manuscript's band-incidence bound, including long bands.
-/

open Set MeasureTheory Metric
open scoped Topology

namespace CircleDomainRigidity

theorem addCircle_image_Icc_subset_closedBall (a b : ℝ) :
    ((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b ⊆
      closedBall (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) ((b - a) / 2) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall, dist_eq_norm, ← QuotientAddGroup.mk_sub]
  apply QuotientAddGroup.norm_mk_le_norm.trans
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem volume_addCircle_image_Icc_le (a b : ℝ) :
    volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b) ≤
      ENNReal.ofReal (min 1 (b - a)) := by
  calc
    _ ≤ volume (closedBall (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) ((b - a) / 2)) :=
      measure_mono (addCircle_image_Icc_subset_closedBall a b)
    _ = _ := by rw [AddCircle.volume_closedBall]; congr 2; ring

theorem circleBandGraph_fiber_eq_image_realFiber
    {X : Type*} [TopologicalSpace X] (G : Set X) (f : X → ℝ) (x : X) :
    {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G f} =
      ((↑) : ℝ → AddCircle (1 : ℝ)) ''
        {r : ℝ | (x, r) ∈ intervalFiberHull (clusterGraph G f)} := by
  ext t
  constructor
  · rintro ⟨⟨y, r⟩, hr, he⟩
    have hy : y = x := congrArg Prod.fst he
    subst y
    exact ⟨r, hr, congrArg Prod.snd he⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨(x, r), hr, rfl⟩

theorem measurableSet_circleBandIncidence
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ y ∈ G, |f y| ≤ M) (x : X) :
    MeasurableSet {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G f} :=
  (isCompact_circleBandIncidence hM x).isClosed.measurableSet

/-- The band-incidence estimate in the coordinates used by the paper:
the budget bounds the difference of the actual upper and lower limits. -/
theorem volume_circleBandGraph_incidence_le_budget
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ y ∈ G, |f y| ≤ M)
    {x : X} (hx : x ∈ closure G) {a : ℝ}
    (hbudget : Filter.limsup f (𝓝[G] x) - Filter.liminf f (𝓝[G] x) ≤ a) :
    volume {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G f} ≤
      ENNReal.ofReal a := by
  rw [circleBandGraph_fiber_eq_image_realFiber,
    intervalFiberHull_clusterGraph_eq_boundary_band hM hx]
  exact (volume_addCircle_image_Icc_le _ _).trans
    (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans hbudget))

/-- The bound required by weighted dust incidence, specialized to the
actual compact interval fibers of the band graph. -/
theorem volume_circleBandGraph_fiber_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ y ∈ G, |f y| ≤ M)
    {x : X} (hx : x ∈ closure G) {a : ℝ}
    (hbudget : sSup {t : ℝ | (x, t) ∈ clusterGraph G f} -
      sInf {t : ℝ | (x, t) ∈ clusterGraph G f} ≤ a) :
    volume {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G f} ≤
      ENNReal.ofReal a := by
  have heq : {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G f} =
      ((↑) : ℝ → AddCircle (1 : ℝ)) ''
        Icc (sInf {t : ℝ | (x, t) ∈ clusterGraph G f})
          (sSup {t : ℝ | (x, t) ∈ clusterGraph G f}) := by
    rw [← intervalFiberHull_fiber_eq_Icc (isCompact_clusterGraph hM) x
      (clusterGraph_fiber_nonempty_of_mem_closure hM hx)]
    ext t
    constructor
    · rintro ⟨⟨y, r⟩, hr, he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(x, r), hr, rfl⟩
  rw [heq]
  exact (volume_addCircle_image_Icc_le _ _).trans
    (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans hbudget))

end CircleDomainRigidity

end OAI
