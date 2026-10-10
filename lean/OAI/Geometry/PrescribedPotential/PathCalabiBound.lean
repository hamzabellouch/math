import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiLocalUniform
import OAI.Geometry.PrescribedPotential.PathCalabiRicci
import OAI.Geometry.PrescribedPotential.PathEllipticity

namespace OAI

/-! Path Calabi Bound. -/

section

 

noncomputable section
open Set Filter Topology Matrix Metric
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
open KaehlerCalculus EllipticKernel
local instance pathCalabiRealIP (d : ℕ) : InnerProductSpace ℝ (EC d) :=
  InnerProductSpace.rclikeToReal ℂ (EC d)
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
  {A : ComplexAtlas d X}
namespace CoordinateBall
variable (p : CoordinateBall A)

theorem path_calabi_bound (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t b : ℝ) (φ : SmoothRealFunction A), t ∈ Icc 0 1 →
      ∀ hs : SolvesVolumePath g h t φ b, ∀ x ∈ p.source,
        ((g.deform φ hs.choose).localField p.index).calabiNorm (A.chart p.index x) ≤ C := by
  obtain ⟨R,K,hR,hK,hell⟩ := volumePath_relative_ellipticity g h
  let ψ : ContDiffBump p.center :=
    { rIn := p.radius, rOut := 2*p.radius, rIn_pos := p.radius_pos,
      rIn_lt_rOut := by linarith [p.radius_pos] }
  let L : Set (V d) := coordinateEquiv d '' closedBall p.center (3*p.radius)
  let χ : V d → ℝ := fun z => ψ ((coordinateEquiv d).symm z)
  have hL : IsCompact L := (isCompact_closedBall _ _).image (coordinateEquiv d).continuous
  have hLc (z : V d) : z ∈ L ↔ (coordinateEquiv d).symm z ∈ closedBall p.center (3*p.radius) := by
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hy
    · intro hz
      exact ⟨_,hz,(coordinateEquiv d).apply_symm_apply z⟩
  have hdom : L ⊆ (A.chart p.index).target := by
    intro z hz
    have hh := p.closure_sub (closedBall_subset_closedBall (by linarith [p.radius_pos]) ((hLc z).mp hz))
    simpa only [ComplexAtlas.euclideanChart_target,mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hh
  have hχ : ContDiff ℝ ∞ χ := ψ.contDiff.comp (coordinateEquiv d).symm.contDiff
  have hχint (z : V d) (hz : z ∈ L) (hn : χ z ≠ 0) : z ∈ interior L := by
    have hs : (coordinateEquiv d).symm z ∈ ball p.center (2*p.radius) := by
      rw [← ψ.support_eq]
      exact hn
    have hs' : (coordinateEquiv d).symm z ∈ ball p.center (3*p.radius) :=
      ball_subset_ball (by linarith [p.radius_pos]) hs
    apply mem_interior_iff_mem_nhds.mpr
    apply mem_of_superset (((isOpen_ball.preimage (coordinateEquiv d).symm.continuous).mem_nhds hs'))
    intro y hy
    exact (hLc y).mpr (ball_subset_closedBall hy)
  have hHG := (g.smooth p.index).continuousOn.mono hdom
  have hH : ContinuousOn (fun q : ℝ × V d => pathLogDetHessian g h p.index q.1 q.2) (Icc 0 1 ×ˢ L) :=
    (pathLogDetHessian_continuous g h p.index).mono (prod_mono (subset_univ _) hdom)
  have hJ : ContinuousOn (fun q : ℝ × V d => pathRicciJet g h p.index q.1 q.2) (Icc 0 1 ×ˢ L) :=
    (pathRicciJet_continuous g h p.index).mono (prod_mono (subset_univ _) hdom)
  obtain ⟨C,hC,hbound⟩ := calabi_interior_uniform isCompact_Icc hL (g.matrix p.index) hHG
    (fun z hz => g.positive _ _ (hdom hz))
    (fun q : ℝ × V d => pathLogDetHessian g h p.index q.1 q.2)
    (fun q : ℝ × V d => pathRicciJet g h p.index q.1 q.2) hH hJ χ hχ
    (fun _ _ => ψ.nonneg) (fun _ _ => ψ.le_one) hχint hR.le hK.le
  refine ⟨C,hC,?_⟩
  intro t b φ ht hs x hx
  have hxV : A.chart p.index x ∈ L := by
    apply (hLc _).mpr
    exact closedBall_subset_closedBall (by linarith [p.radius_pos]) (ball_subset_closedBall hx.2)
  apply hbound ((g.deform φ hs.choose).localField p.index) t ht hdom
    (fun z hz => hell t b φ ht hs p.index z (hdom hz))
    (fun z hz => volumePath_logdet_hessian g h hs hs.choose p.index (hdom hz))
    (fun z hz => volumePath_ricciJet g h hs hs.choose p.index (hdom hz)) _ hxV
  exact ψ.one_of_mem_closedBall (ball_subset_closedBall hx.2)
end CoordinateBall

 

theorem volumePath_calabi_finite_cover (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) :
    ∃ (S : Finset (CoordinateBall A)) (C : ℝ), 0 ≤ C ∧
      (∀ x, ∃ p ∈ S, x ∈ p.source) ∧
      ∀ p ∈ S, ∀ (t b : ℝ) (φ : SmoothRealFunction A), t ∈ Icc 0 1 →
        ∀ hs : SolvesVolumePath g h t φ b, ∀ x ∈ p.source,
          ((g.deform φ hs.choose).localField p.index).calabiNorm (A.chart p.index x) ≤ C := by
  classical
  obtain ⟨S,hS⟩ := CoordinateBall.finite_cover (A := A)
  choose C hC hb using fun p : CoordinateBall A => p.path_calabi_bound g h
  refine ⟨S,∑ p ∈ S, C p,Finset.sum_nonneg (fun p _ => hC p),hS,?_⟩
  intro p hp t b φ ht hs x hx
  exact (hb p t b φ ht hs x hx).trans (Finset.single_le_sum (fun q _ => hC q) hp)
end Anticanonical.SourceSmooth

end
end

end OAI
