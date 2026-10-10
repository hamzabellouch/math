import OAI.Analysis.CircleDomains.Topology.FiniteCircleGreen
import OAI.Analysis.CircleDomains.Modulus.WeightedCollarNeighborhoods
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! Smooth inward collars for regular Jordan boundaries.

Published input: J. M. Lee, Introduction to Smooth Manifolds, second edition
(2013), Theorem 9.25, pp.222--223 (Collar Neighborhood Theorem), together with
its regular-domain interpretation in Proposition5.47, p.121. The formulation
below is the compact planar Jordan-boundary specialization: parametrize the
boundary circle (Milnor's compact one-manifold classification), take inward
collar slices, and use their bounded Jordan sides (planar Schoenflies).
It is a specialization/corollary, not a verbatim transcription of Theorem9.25.
The continuous-tangent clause retains the C¹ dependence of its smooth
collar embedding and is used only for the uniform boundary variation bound.
The regular-level hypothesis is retained explicitly.
https://thunv.wordpress.com/wp-content/uploads/2015/09/graduate-texts-in-mathematics-vol-218-john-m-lee-introduction-to-smooth-manifolds-springer-2013.pdf
DOI: 10.1007/978-1-4419-9982-5.
-/

open Set Function Filter Metric
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

structure RegularJordanInwardCollar (H : ℂ ≃ₜ ℂ) where
  width : ℝ
  width_pos : 0 < width
  curve : ℝ → ℝ → ℂ
  disk : ℝ → ℂ ≃ₜ ℂ
  disk_zero : disk 0 = H
  continuous : ContinuousOn (fun p : ℝ × ℝ => curve p.1 p.2) (Icc 0 width ×ˢ univ)
  tangent_continuous : ContinuousOn (fun p : ℝ × ℝ => deriv (curve p.1) p.2)
    (Icc 0 width ×ˢ univ)
  parametrization : ∀ ρ ∈ Icc 0 width, PositiveJordanParametrization (disk ρ) (curve ρ)
  inward : ∀ ρ ∈ Ioc 0 width, closure (jordanInterior (disk ρ)) ⊆ jordanInterior H
  retains_compact : ∀ K : Set ℂ, IsCompact K → K ⊆ jordanInterior H →
    ∃ η > 0, η ≤ width ∧ ∀ ρ ∈ Ioc 0 η, K ⊆ jordanInterior (disk ρ)

/-- Explicit published-input parameter: the regular-level planar Jordan
specialization of the collar-neighborhood theorem described above. -/
def SmoothRegularJordanCollars : Prop :=
  ∀ (H : ℂ ≃ₜ ℂ) (f : ℂ → ℝ) (t : ℝ), ContDiff ℝ (⊤ : ℕ∞) f →
    IsPlanarRegularValue f t → frontier (jordanInterior H) ⊆ {z | f z = t} →
    Nonempty (RegularJordanInwardCollar H)

 theorem WeightedCollar.exists_regular_inward_collar
    (hcollar : SmoothRegularJordanCollars)
    {G : Set Sphere} {π : Sphere → Sphere} {B : Set Sphere} {p : Sphere} {g : ℂ → ℝ≥0∞}
    (D : WeightedCollar G π B p g) : Nonempty (RegularJordanInwardCollar D.disk) :=
  hcollar D.disk D.function D.level D.smooth D.regular D.frontier_level

 theorem RegularJordanInwardCollar.uniform_approach
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) :
    ∀ ε > 0, ∃ η > 0, η ≤ C.width ∧ ∀ ρ ∈ Icc 0 η,
      ∀ t ∈ Icc (0 : ℝ) 1, dist (C.curve ρ t) (C.curve 0 t) < ε := by
  have hsub : Icc (0 : ℝ) C.width ×ˢ Icc (0 : ℝ) 1 ⊆ Icc 0 C.width ×ˢ (univ : Set ℝ) :=
    prod_mono Subset.rfl (subset_univ _)
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (C.continuous.mono hsub)
  intro ε hε
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let η := min C.width (d / 2)
  have hη : 0 < η := lt_min C.width_pos (half_pos hd)
  have hηw : η ≤ C.width := min_le_left _ _
  refine ⟨η, hη, hηw, ?_⟩
  intro ρ hρ t ht
  apply hdist (ρ, t) ⟨⟨hρ.1, hρ.2.trans hηw⟩, ht⟩
    (0, t) ⟨⟨le_rfl, C.width_pos.le⟩, ht⟩
  rw [Prod.dist_eq, dist_self, max_eq_left (show (0 : ℝ) ≤ dist ρ 0 from dist_nonneg),
    Real.dist_eq, sub_zero, abs_of_nonneg hρ.1]
  exact hρ.2.trans_lt ((min_le_right C.width (d / 2)).trans_lt (half_lt_self hd))

 theorem RegularJordanInwardCollar.eventually_in_boundary_neighborhood
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    {U : Set ℂ} (hU : IsOpen U) (hCU : frontier (jordanInterior H) ⊆ U) :
    ∃ η > 0, η ≤ C.width ∧ ∀ ρ ∈ Icc 0 η, ∀ t ∈ Icc (0 : ℝ) 1, C.curve ρ t ∈ U := by
  have hcompact := (isCompact_closure_jordanInterior H).of_isClosed_subset
    isClosed_frontier frontier_subset_closure
  obtain ⟨d, hd, hthick⟩ := hcompact.exists_cthickening_subset_open hU hCU
  obtain ⟨η, hη, hηw, hnear⟩ := C.uniform_approach d hd
  refine ⟨η, hη, hηw, ?_⟩
  intro ρ hρ t ht
  have hpar0 := C.parametrization 0 ⟨le_rfl, C.width_pos.le⟩
  have hzero : C.curve 0 t ∈ frontier (jordanInterior H) := by
    have hz : C.curve 0 t ∈ frontier (jordanInterior (C.disk 0)) :=
      hpar0.boundary ▸ mem_image_of_mem _ ht
    simpa only [C.disk_zero] using hz
  exact hthick (mem_cthickening_of_dist_le _ _ _ _ hzero (hnear ρ hρ t ht).le)

end CircleDomainRigidity

end

end OAI
