import OAI.Geometry.NodalSets.Charts.ChartOperatorIdentity
import OAI.Geometry.NodalSets.Charts.CommonSmoothChart

namespace OAI

namespace Yau.Geometry
open Filter Set
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

def metricChartParameter (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (y : Coord) (e : Coord ≃L[ℝ] Coord) : QuadParam Coord :=
  (y,e.toContinuousLinearMap,actualFrameConnection g y e)

def extendedPrincipal (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (y : T → Coord) (e : T → Coord ≃L[ℝ] Coord) (beta : Coord → ℝ)
    (t : T) (i j : Fin 4) : Coord → ℂ :=
  cutoffCoefficient beta (complexPrincipal g i j) (metricChartParameter g (y t) (e t))

def extendedDrift (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (y : T → Coord) (e : T → Coord ≃L[ℝ] Coord) (beta : Coord → ℝ)
    (t : T) (j : Fin 4) : Coord → ℂ :=
  cutoffCoefficient beta (complexDrift g w j) (metricChartParameter g (y t) (e t))

structure NormalOperatorFamily
    (a : T → Fin 4 → Fin 4 → Coord → ℂ) (b : T → Fin 4 → Coord → ℂ) : Prop where
  principal_smooth : ∀ t i j, ContDiff ℝ ∞ (a t i j)
  drift_smooth : ∀ t j, ContDiff ℝ ∞ (b t j)
  principal_jets : ∀ k i j, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (a z.1 i j) z.2)
  drift_jets : ∀ k j, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (b z.1 j) z.2)
  principal_symm : ∀ t i j x, a t i j x = a t j i x
  normal_value : ∀ t i j, a t i j 0 = if i=j then 1 else 0
  normal_first : ∀ t i j, fderiv ℝ (a t i j) 0 = 0

theorem compact_actual_normal_operator
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (y : T → Coord) (hy : Continuous y) (e : T → Coord ≃L[ℝ] Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
    {U : Set Coord} (hU : IsOpen U) (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x) :
    ∃ beta : ContDiffBump (0:Coord),
      (∀ t x, x ∈ tsupport beta → rawQuadratic (metricChartParameter g (y t) (e t)) x ∈ U) ∧
      NormalOperatorFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta) := by
  have hB := actualFrameConnection_continuous g hg hpos y hy e he
  obtain ⟨r,hr,hri⟩ := compact_quadratic_chart_domain isCompact_univ y hy e he
    (fun t ↦ actualFrameConnection g (y t) (e t)) hB hU (fun t _ ↦ hyU t)
  let beta : ContDiffBump (0:Coord) := ⟨r/4,r/2,by positivity,by linarith⟩
  have hnorm (x : Coord) (hx : x ∈ tsupport beta) : ‖x‖ < r := by
    rw [beta.tsupport_eq, Metric.mem_closedBall, dist_zero_right] at hx
    change ‖x‖ ≤ r/2 at hx
    linarith
  have hsource (t : T) (x : Coord) (hx : x ∈ tsupport beta) :
      rawQuadratic (metricChartParameter g (y t) (e t)) x ∈ U :=
    (hri t (mem_univ t) x (hnorm x hx)).1
  have hp : Continuous (fun t ↦ metricChartParameter g (y t) (e t)) := hy.prodMk (he.prodMk hB)
  obtain ⟨hG,hb,hGc,hbc⟩ := complex_chart_coefficient_extensions g hg w hw
    (fun t ↦ metricChartParameter g (y t) (e t)) hp beta beta.contDiff
    (fun t x _ ↦ hpos _) (fun t x hx ↦ hwpos _ (hsource t x hx))
    (fun t x hx ↦ by
      obtain ⟨J,hJ⟩ := (hri t (mem_univ t) x (hnorm x hx)).2
      exact ⟨J,hJ.symm⟩)
  have hnormal (t : T) := extended_actual_metric_normal_jets g hg hs hpos (y t) (e t)
    (ho t) beta beta.eventuallyEq_one
  have hsym (t : T) (i j : Fin 4) (x : Coord) :
      extendedPrincipal g y e beta t i j x = extendedPrincipal g y e beta t j i x := by
    by_cases hx : x ∈ tsupport beta
    · obtain ⟨J,hJ⟩ := (hri t (mem_univ t) x (hnorm x hx)).2
      have hh := chartPrincipal_symmetric g hs (metricChartParameter g (y t) (e t)) x
        (hpos _) J hJ.symm i j
      simp only [extendedPrincipal,cutoffCoefficient,complexPrincipal,hh]
    · simp [extendedPrincipal,cutoffCoefficient,image_eq_zero_of_notMem_tsupport hx]
  exact ⟨beta,hsource,⟨hG,hb,hGc,hbc,hsym,fun t ↦ (hnormal t).1,fun t ↦ (hnormal t).2⟩⟩

omit [CompactSpace T] in
theorem NormalOperatorFamily.matching_taylor
    {a : T → Fin 4 → Fin 4 → Coord → ℂ} {b : T → Fin 4 → Coord → ℂ}
    (h : NormalOperatorFamily a b) (m : ℕ) (hm : 1 ≤ m) :
    let A := fun t i j ↦ taylorPolynomial (a t i j) 0 m
    let B := fun t j ↦ taylorPolynomial (b t j) 0 m
    (∀ i j, ContinuousPolyFamily (fun t ↦ A t i j)) ∧
    (∀ j, ContinuousPolyFamily (fun t ↦ B t j)) ∧
    (∀ t i j, MvPolynomial.homogeneousComponent 0 (A t i j) = if i=j then 1 else 0) ∧
    (∀ t i j, MvPolynomial.homogeneousComponent 1 (A t i j) = 0) ∧
    (∀ t i j, FlatAt m (fun x ↦ a t i j x-reval (A t i j) x) 0) ∧
    ∀ t j, FlatAt m (fun x ↦ b t j x-reval (B t j) x) 0 := by
  dsimp only
  have hmets (t : T) := normal_metric_matching_taylor (a t) (h.principal_smooth t)
    (h.normal_value t) (h.normal_first t) m hm
  exact ⟨fun i j ↦ parametric_taylor_family _ (fun k ↦ h.principal_jets k i j) m,
    fun j ↦ parametric_taylor_family _ (fun k ↦ h.drift_jets k j) m,
    fun t ↦ (hmets t).1,fun t ↦ (hmets t).2.1,fun t ↦ (hmets t).2.2,
    fun t j ↦ flatAt_taylorPolynomial (h.drift_smooth t j) m⟩

end
end Yau.Geometry

end OAI
