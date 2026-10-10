import OAI.Analysis.Mahler.HemisphereFlux
import OAI.Analysis.Mahler.SphereRadius

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
namespace MahlerStokes

/-- Outward cofactor density in the fixed ordered coordinate basis. The
argument x is the unit normal; r*x is the evaluation point of the form. -/
def coordinateSphereDensity {n : ℕ} (r : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (x : Fin (n+1) → ℝ) : ℝ :=
  ∑ i : Fin (n+1), (-1 : ℝ)^i.val * x i *
    ω (r • x) (i.removeNth (coordinateBasis (n+1)))

lemma continuousOn_sphere_coefficient {n : ℕ}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContinuousOn ω {x | radiusSq x = 1}) (i : Fin (n+1)) :
    ContinuousOn (fun z : EuclideanSpace ℝ (Fin (n+1)) =>
      ω (ofLp z) (i.removeNth (coordinateBasis (n+1)))) (sphere 0 1) := by
  have hw : ContinuousOn (fun z : EuclideanSpace ℝ (Fin (n+1)) => ω (ofLp z)) (sphere 0 1) := by
    apply hω.comp (PiLp.continuous_ofLp 2 _).continuousOn
    intro z hz
    change radiusSq (ofLp z) = 1
    rw [radiusSq_eq_euclidean_norm_sq]
    have hn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    simp [hn]
  exact (ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth (coordinateBasis (n+1)))).continuous.comp_continuousOn hw

/-- Exact equality of the hemisphere-coordinate Stokes integral and the
outward cofactor density integrated against volume.toSphere. -/
theorem sphereFlux_unit_eq_areaIntegral {n : ℕ}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContinuousOn ω {x | radiusSq x = 1}) :
    sphereFlux 1 ω =
      ∫ z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1,
        coordinateSphereDensity 1 ω (ofLp (z : EuclideanSpace ℝ (Fin (n+1))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere := by
  let : CompactSpace (sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hc (i : Fin (n+1)) : Continuous (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (-1 : ℝ)^i.val * (z : EuclideanSpace ℝ (Fin (n+1))) i *
      ω (ofLp (z : EuclideanSpace ℝ (Fin (n+1)))) (i.removeNth (coordinateBasis (n+1)))) :=
    ((continuous_const.mul (by fun_prop)).mul
      ((continuousOn_sphere_coefficient ω hω i).comp_continuous continuous_subtype_val (fun z => z.property)))
  simp only [coordinateSphereDensity, one_smul]
  rw [integral_finsetSum _ (fun i _ =>
    (hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  unfold sphereFlux
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_sphere_coordinate i _ (continuousOn_sphere_coefficient ω hω i)]

/-- Positive-radius coordinate Stokes flux equals the actual unit-sphere
area integral with the positive tangential dilation Jacobian r^n. Regularity
is required only on the radius-r sphere. -/
theorem sphereFlux_pos_eq_areaIntegral {n : ℕ} {r : ℝ} (hr : 0 < r)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContinuousOn ω {x | radiusSq x = r^2}) :
    sphereFlux r ω = r^n *
      ∫ z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1,
        coordinateSphereDensity r ω (ofLp (z : EuclideanSpace ℝ (Fin (n+1))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere := by
  rw [sphereFlux_pos_scale hr]
  congr 1
  have hw : ContinuousOn (fun x => ω (r • x)) {x | radiusSq x = 1} := by
    apply hω.comp (by fun_prop : Continuous (fun x : Fin (n+1) → ℝ => r • x)).continuousOn
    intro x hx
    change radiusSq (r • x) = r^2
    rw [radiusSq_smul, hx, mul_one]
  simpa [coordinateSphereDensity] using sphereFlux_unit_eq_areaIntegral (fun x => ω (r • x)) hw

end MahlerStokes

end

end OAI
