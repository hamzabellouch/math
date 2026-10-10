import OAI.Geometry.NodalSets.Charts.SphereUniformChartL2
import OAI.Geometry.NodalSets.Coefficients.RealCoefficientNeighborhoodPointwise
import OAI.Geometry.NodalSets.Spectral.SphereEigenDirectRepresentative

namespace OAI

namespace Yau.Target
open MeasureTheory Set Metric Yau.Geometry Yau.Analysis
open scoped ContDiff
noncomputable section

theorem sphere_eigen_neighborhood_pointwise (d₀ : SphereEnergyData) (p : Base)
    (hrho₀ : ContDiff ℝ ∞ (fun x ↦ d₀.density (sphereChartCoordMap p x)))
    (mu₀ : ℝ) (n : ℕ) (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hRO : closedBall y R ⊆ interior (Yau.realCenteredCube 4 (1/64))) :
    ∃ eps > 0, ∃ K > 0, ∀ (d : SphereEnergyData) (mu : ℝ),
      ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)) → mu ≠ 0 →
      (∀ x ∈ closedBall y R, ∀ es : List (Fin 4), es.length ≤ n+5 →
        (∀ i j, |partialJet (fun z ↦ sphereChartPrincipalDensity d p z i j) es x-
          partialJet (fun z ↦ sphereChartPrincipalDensity d₀ p z i j) es x| ≤ eps) ∧
        |partialJet (sphereEigenForcingCoefficient d p mu) es x-
          partialJet (sphereEigenForcingCoefficient d₀ p mu₀) es x| ≤ eps) →
      (∀ x ∈ closedBall y R, |roundCoordDensity x*d.density (sphereChartCoordMap p x)-
        roundCoordDensity x*d₀.density (sphereChartCoordMap p x)| ≤ eps) →
      ∀ f : SphereWeightedL2 d, sphereL2Resolvent d f=mu • f →
      ∀ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v →
        v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
          (fun x ↦ f (sphereChartCoordMap p x)) →
        ∀ ds : List (Fin 4), ds.length ≤ n → ∀ x ∈ closedBall y r,
          (partialJet v ds x)^2 ≤ K*‖f‖^2 := by
  have hB₀ : ContDiff ℝ ∞ (sphereEigenForcingCoefficient d₀ p mu₀) :=
    contDiff_const.mul (roundCoordDensity_smooth.mul hrho₀)
  obtain ⟨eps₁,heps₁,A,hA,ha⟩ := real_coefficient_neighborhood_pointwise
    (interior (Yau.realCenteredCube 4 (1/64))) isOpen_interior n y r R hr hR hRO
    (sphereChartPrincipalDensity d₀ p) (sphereEigenForcingCoefficient d₀ p mu₀)
    (sphereChartPrincipalDensity_smooth d₀ p) hB₀
    (fun x _ ↦ (intrinsicRealPrincipal_posDef d₀.tensor d₀.symm d₀.pos p x).smul
      (roundCoordDensity_pos x))
  obtain ⟨eps₂,heps₂,B,hB,hb⟩ := sphereWeightedL2_chart_neighborhood d₀ p (isCompact_closedBall y R)
  refine ⟨min eps₁ eps₂,lt_min heps₁ heps₂,A*B,mul_pos hA hB,
    fun d mu hrho hmu hclose hrclose f heigen v hv hvf ds hd x hx ↦ ?_⟩
  have hBv : ContDiff ℝ ∞ (sphereEigenForcingCoefficient d p mu) :=
    contDiff_const.mul (roundCoordDensity_smooth.mul hrho)
  have hpoint := ha (sphereChartPrincipalDensity d p) (sphereEigenForcingCoefficient d p mu) v
    (sphereChartPrincipalDensity_smooth d p) hBv hv (sphereChartPrincipalDensity_symmetric d p)
    (fun x hx es hes ↦ ⟨fun i j ↦ ((hclose x hx es hes).1 i j).trans (min_le_left _ _),
      (hclose x hx es hes).2.trans (min_le_left _ _)⟩)
    (sphere_eigen_direct_matrix_equation d p hrho mu hmu f heigen v hv hvf) ds hd x hx
  have hsize := (hb d (fun x hx ↦ (hrclose x hx).trans (min_le_right _ _)) f).2
  have hQ : closedBall y R ⊆ Yau.realCenteredCube 4 (1/32) :=
    hRO.trans (interior_subset.trans (Yau.realCenteredCube_mono (by norm_num)))
  have heq : v =ᵐ[volume.restrict (closedBall y R)]
      (fun x ↦ f (sphereChartCoordMap p x)) := ae_mono (Measure.restrict_mono hQ le_rfl) hvf
  have hi : (∫ z in closedBall y R, v z^2) =
      ∫ z in closedBall y R, (f (sphereChartCoordMap p z))^2 :=
    integral_congr_ae (heq.fun_comp (fun a : ℝ ↦ a^2))
  rw [hi] at hpoint
  exact hpoint.trans ((mul_le_mul_of_nonneg_left hsize hA.le).trans_eq (by ring))

end
end Yau.Target

end OAI
