import OAI.Analysis.Mahler.SphereCoordinateIntegral

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
namespace MahlerStokes

/-- The degree equality is explicit; this is transport along that equality,
not an arbitrary permutation of the ordered real coordinates. -/
def degreeCastEuclidean {d e : ℕ} (h : d = e) :
    EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e) := by
  subst e
  exact LinearIsometryEquiv.refl ℝ _

lemma degreeCastEuclidean_apply {d e : ℕ} (h : d = e)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin e) :
    degreeCastEuclidean h x i = x (Fin.cast h.symm i) := by
  subst e
  rfl

/-- Interleaved complex coordinates with the boundary/ambient degree cast
shown in the type. -/
def complexSphereCoordinates (d k : ℕ) (h : d+1 = k*2) :
    EuclideanSpace ℝ (Fin (d+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin k) :=
  (degreeCastEuclidean h).trans (interleavedEuclidean k)

/-- The interleaved real-to-complex coordinate map after the explicit Fin cast. -/
lemma complexSphereCoordinates_eq_complexCoordinates (d k : ℕ) (h : d+1 = k*2)
    (x : EuclideanSpace ℝ (Fin (d+1))) :
    complexSphereCoordinates d k h x =
      complexCoordinates k (fun i => x (Fin.cast h.symm i)) := by
  change interleavedEuclidean k (degreeCastEuclidean h x) =
    interleavedEuclidean k (toLp 2 (fun i => x (Fin.cast h.symm i)))
  apply congrArg (interleavedEuclidean k)
  ext i
  exact degreeCastEuclidean_apply h x i

/-- Exact positive-radius hemisphere-to-complex-sphere integration equality.
The right side uses the same volume.toSphere as Mahler.sphereArea; r^d is
the tangential Jacobian in Mahler.radiusSphereArea. -/
theorem sphereFlux_eq_complexSphereIntegral {d k : ℕ} (h : d+1 = k*2)
    {r : ℝ} (hr : 0 < r)
    (ω : (Fin (d+1) → ℝ) → (Fin (d+1) → ℝ) [⋀^Fin d]→L[ℝ] ℝ)
    (hω : ContinuousOn ω {x | radiusSq x = r^2}) :
    sphereFlux r ω = r^d *
      ∫ z : sphere (0 : EuclideanSpace ℂ (Fin k)) 1,
        coordinateSphereDensity r ω
          (ofLp ((complexSphereCoordinates d k h).symm (z : EuclideanSpace ℂ (Fin k))))
        ∂(volume : Measure (EuclideanSpace ℂ (Fin k))).toSphere := by
  rw [sphereFlux_pos_eq_areaIntegral hr ω hω]
  congr 1
  have hp := measurePreserving_sphereIsometry (complexSphereCoordinates d k h) volume volume
    (complexSphereCoordinates d k h).measurePreserving
  have he := hp.integral_comp (sphereIsometry (complexSphereCoordinates d k h)).measurableEmbedding
    (fun z : sphere (0 : EuclideanSpace ℂ (Fin k)) 1 =>
      coordinateSphereDensity r ω (ofLp ((complexSphereCoordinates d k h).symm
        (z : EuclideanSpace ℂ (Fin k)))))
  simpa [sphereIsometry] using he

/-- Boundary degree 2k+1 and ambient complex dimension k+1
in the sphere flux integral. -/
theorem sphereFlux_eq_complexSphereIntegral_succ (k : ℕ)
    {r : ℝ} (hr : 0 < r)
    (ω : (Fin ((2*k+1)+1) → ℝ) → (Fin ((2*k+1)+1) → ℝ) [⋀^Fin (2*k+1)]→L[ℝ] ℝ)
    (hω : ContinuousOn ω {x | radiusSq x = r^2}) :
    sphereFlux r ω = r^(2*k+1) *
      ∫ z : sphere (0 : EuclideanSpace ℂ (Fin (k+1))) 1,
        coordinateSphereDensity r ω
          (ofLp ((complexSphereCoordinates (2*k+1) (k+1) (by omega)).symm
            (z : EuclideanSpace ℂ (Fin (k+1)))))
        ∂(volume : Measure (EuclideanSpace ℂ (Fin (k+1)))).toSphere :=
  sphereFlux_eq_complexSphereIntegral (by omega) hr ω hω

end MahlerStokes

end

end OAI
