import OAI.Geometry.NodalSets.Charts.SphereEnergyCompletion
import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientFormComparison
import OAI.Geometry.NodalSets.Hausdorff.PerturbedNodalTransfer

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace ENNReal NNReal
noncomputable section

theorem sphere_finite_norm_uniform_nodal_transfer (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    {H : Set Yau.Jets.Coord} (hH : IsCompact H) :
    ∃ eta > 0, ∃ C : ℝ≥0, 0 < C ∧
      ∀ (b : SphereEnergyData) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
        sphereCoefficientDistance P 0 d.tensor d.density b.tensor b.density < eta →
        ∀ (u : Base → ℝ) (U : Set Yau.Jets.Coord), U ⊆ H →
          Measure.hausdorffMeasure (4:ℝ)
            ((U ×ˢ Icc (-1:ℝ) 1) ∩ {z : Yau.Jets.Coord × ℝ | u (seedSphereFromCoord z.1)=0}) ≤
          (C:ℝ≥0∞)^4 * nodalMeasure
            (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive) (circleLift u) := by
  obtain ⟨c,hc,B,hB,R,hR,hlo,hhi,hrlo,hrhi⟩ :=
    intrinsic_pair_uniform_bounds d.tensor d.smooth d.symm d.pos d.density hd d.positive
  obtain ⟨eta,heta,Heta⟩ := sphere_coefficient_relative_form_comparison P hcover
    d.tensor d.smooth d.symm d.pos d.density hd d.positive (1/2) (by norm_num)
  obtain ⟨a,t,ht,hchart⟩ := exists_short_circle_arc (seedPoint,(1:Circle))
  obtain ⟨C,hC,htransfer⟩ := uniform_intrinsic_coefficient_nodal_transfer
    (c/2) (3*B/2) (c/2) (3*R/2) (by positivity) (by positivity) (by positivity) (by positivity)
    (seedPoint,(1:Circle)) a ht.ne' (hH.prod isCompact_Icc)
    (hchart (fun y hy ↦ by rw [centeredSphereChart_target]; trivial))
  refine ⟨eta,heta,C,hC,?_⟩
  intro b hb hdist u U hUH
  have hcmp := Heta b.tensor b.density b.smooth b.symm b.pos hb hdist
  have hblo : ∀ (x : Base) (v : AmbientBase), ⟪(x:AmbientBase),v⟫=0 →
      (c/2)*‖v‖^2 ≤ b.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) := by
    intro x v hv
    have h := hlo x (sphereCovectorRestriction x v)
    rw [roundCotangentTensor_tangent x v v hv hv,real_inner_self_eq_norm_sq] at h
    have hh := abs_le.mp ((hcmp x).1 (sphereCovectorRestriction x v))
    nlinarith
  have hbhi : ∀ (x : Base) (v : AmbientBase), ⟪(x:AmbientBase),v⟫=0 →
      b.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) ≤ (3*B/2)*‖v‖^2 := by
    intro x v hv
    have h := hhi x (sphereCovectorRestriction x v)
    rw [roundCotangentTensor_tangent x v v hv hv,real_inner_self_eq_norm_sq] at h
    have hh := abs_le.mp ((hcmp x).1 (sphereCovectorRestriction x v))
    nlinarith
  have hbrlo (x : Base) : c/2 ≤ b.density x := by
    have hh := abs_le.mp (hcmp x).2
    linarith [hrlo x]
  have hbrhi (x : Base) : b.density x ≤ 3*R/2 := by
    have hh := abs_le.mp (hcmp x).2
    linarith [hrhi x]
  apply htransfer b.tensor b.smooth b.symm b.pos b.density hb b.positive hblo hbhi hbrlo hbrhi
  · rintro z ⟨hz,_⟩
    exact ⟨hUH hz.1,hz.2⟩
  · rintro z ⟨_,hzero⟩
    rw [circleLift_productChartInverse]
    exact hzero

end
end Yau.Target

end OAI
