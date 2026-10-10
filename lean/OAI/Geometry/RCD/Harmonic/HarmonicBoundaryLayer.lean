import OAI.Geometry.RCD.Sobolev.BoundaryDirichletLayer
import OAI.Geometry.RCD.Sobolev.HarmonicReplacementEnergy

namespace OAI

/-! # The boundary values retained by actual harmonic replacements -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_replacement_boundary_layer {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) :
    ∃ C : ℝ, 0<C ∧ ∀ (p : X) (r S R δ ε : ℝ),
      0<r → 0<δ → 4*δ≤R → R+2*δ≤S → 0≤ε → ε≤δ/8 →
      ∀ V : X → Euclidean n, IsPointedApproximation p 0 r S ε V →
      -1≤K*(S*r)^2 → ∀ u w : SobolevSpace (hausdorff n X) hX.quadratic,
      w-u∈SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p (R*r)) →
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (R*r)) w →
      ∀ E : ℝ, r^2*energyForm (hausdorff n X) hX.quadratic u u≤
        E*(hausdorff n X).real (ball p (S*r)) →
      ((hausdorff n X).real (ball p (S*r)))⁻¹*
        (∫ z in closedBall p (R*r) \ ball p ((R-δ)*r),
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w-u) z)^2 ∂hausdorff n X)≤C*E*δ^2 := by
  obtain ⟨C,hC,hbound⟩ := hX.boundary_dirichlet_layer hn
  refine ⟨C,hC,?_⟩
  intro p r S R δ ε hr hδ hR hS hε hεδ V hV hcurv u w hb hw E hE
  have hl := hbound p r S R δ ε hr hδ hR hS hε hεδ V hV hcurv ⟨w-u,hb⟩
  change (∫ z in closedBall p (R*r) \ ball p ((R-δ)*r),
    (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w-u) z)^2 ∂hausdorff n X)≤
    C*δ^2*r^2*energyForm (hausdorff n X) hX.quadratic (w-u) (w-u) at hl
  rw [harmonic_replacement_energy_identity _ _ _ u w hb hw] at hl
  have hwe : 0≤energyForm (hausdorff n X) hX.quadratic w w := by
    rw [energyForm_self]
    exact mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg _ _ w)
  have he := mul_le_mul_of_nonneg_left hE (show 0≤C*δ^2 by positivity)
  have hpoint : (∫ z in closedBall p (R*r) \ ball p ((R-δ)*r),
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w-u) z)^2 ∂hausdorff n X)≤
      C*E*δ^2*(hausdorff n X).real (ball p (S*r)) := by
    calc _ ≤ C*δ^2*r^2*energyForm (hausdorff n X) hX.quadratic u u :=
           hl.trans (mul_le_mul_of_nonneg_left (sub_le_self _ hwe) (by positivity))
         _ ≤ _ := by convert he using 1 <;> ring
  have hm : 0<(hausdorff n X).real (ball p (S*r)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos (by linarith) hr)).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  calc _ ≤ ((hausdorff n X).real (ball p (S*r)))⁻¹*
        (C*E*δ^2*(hausdorff n X).real (ball p (S*r))) :=
        mul_le_mul_of_nonneg_left hpoint (inv_pos.mpr hm).le
       _ = _ := by field_simp

end RegularPointCoordinates

end

end OAI
