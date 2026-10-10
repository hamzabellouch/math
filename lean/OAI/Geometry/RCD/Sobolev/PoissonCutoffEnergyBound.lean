import OAI.Geometry.RCD.Sobolev.PositiveDefectCutoff
import OAI.Geometry.RCD.Sobolev.GoodLaplacianCutoff

namespace OAI

/-! # The quantitative cutoff bound for a squared-distance replacement

The full positive source of the boundary datum supplies the sign. Only the
already controlled energy-density error of the replacement is needed.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem GoodLaplacianCutoff.poisson_energy_bound
    {p : X} {r C b : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (hC : 0 ≤ C) (hb : 2*r < b)
    (u q : SobolevSpace μ Q) (σ : Measure X) {a n E : ℝ} (hna : n ≤ a)
    (hsource : ∀ (ψ : SobolevSpace μ Q) (v : X → ℝ) (L : ℝ≥0),
      LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ ball p b →
      SobolevSpace.toLp μ Q ψ =ᵐ[μ] v →
      energyForm μ Q q ψ+a*(∫ x in ball p b, v x ∂μ)=∫ x, v x ∂σ)
    (heik : (fun x => (1/2:ℝ)*localGamma μ Q q q x)
      =ᵐ[μ.restrict (ball p b)] SobolevSpace.toLp μ Q q)
    (herror : (∫ x in ball p b,
      |(1/2:ℝ)*localGamma μ Q u u x-(1/2:ℝ)*localGamma μ Q q q x| ∂μ) ≤ E) :
    (1/2:ℝ)*weightedGamma μ Q χ.laplacian u u+
      (n-2*a)*(∫ x, χ.weight x ∂μ) ≤ (C/r^2)*E := by
  have hout (x : X) (hx : x ∉ ball p b) : 2*r < dist p x := by
    have hh : b ≤ dist p x := by simpa only [mem_ball,dist_comm,not_lt] using hx
    exact hb.trans_le hh
  have hzero : ∀ᵐ x ∂μ, x ∉ ball p b → χ.laplacian x=0 := by
    filter_upwards [χ.laplacian_locality] with x hx hn
    exact hx (Or.inr (hout x hn))
  have hloc (f : SobolevSpace μ Q) : weightedGamma μ Q χ.laplacian f f=
      ∫ x in ball p b, χ.laplacian x*localGamma μ Q f f x ∂μ := by
    symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hzero] with x hx hn
    rw [hx hn,zero_mul]
  have hvloc : (∫ x in ball p b, χ.weight x ∂μ)=∫ x, χ.weight x ∂μ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact Eventually.of_forall fun x hx => χ.zero x (hout x hx)
  have hqsource := positive_defect_cutoff_identity μ Q q σ a hsource χ.weight χ.lipschitz
    (χ.hasCompactSupport μ Q)
    ((χ.tsupport_subset μ Q).trans (closedBall_subset_ball hb))
    χ.sobolev χ.representative χ.laplacian χ.weak_laplacian hzero
  rw [hvloc] at hqsource
  have hqident : (1/2:ℝ)*weightedGamma μ Q χ.laplacian q q=
      a*(∫ x, χ.weight x ∂μ)-∫ x, χ.weight x ∂σ := by
    rw [hloc,← integral_const_mul,← hqsource]
    apply integral_congr_ae
    filter_upwards [heik] with x hx
    change (1/2:ℝ)*(χ.laplacian x*localGamma μ Q q q x)=
      SobolevSpace.toLp μ Q q x*χ.laplacian x
    rw [← hx]
    ring
  let e := fun x => (1/2:ℝ)*localGamma μ Q u u x-(1/2:ℝ)*localGamma μ Q q q x
  have hei : IntegrableOn e (ball p b) μ :=
    (((localGamma_memL1 μ Q u u).const_mul (1/2:ℝ)).sub
      ((localGamma_memL1 μ Q q q).const_mul (1/2:ℝ))).integrableOn
  have hweighted : |∫ x in ball p b, χ.laplacian x*e x ∂μ| ≤ (C/r^2)*E := by
    have hh := norm_integral_le_of_norm_le (hei.abs.const_mul (C/r^2)) (show
        ∀ᵐ x ∂μ.restrict (ball p b), ‖χ.laplacian x*e x‖ ≤ (C/r^2)*|e x| from by
      filter_upwards [ae_restrict_of_ae χ.laplacian_bound] with x hx
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _))
    rw [Real.norm_eq_abs,integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left herror (div_nonneg hC (sq_nonneg r)))
  have hsplit : (∫ x in ball p b, χ.laplacian x*e x ∂μ)=
      (1/2:ℝ)*weightedGamma μ Q χ.laplacian u u-
        (1/2:ℝ)*weightedGamma μ Q χ.laplacian q q := by
    have hi (f : SobolevSpace μ Q) : IntegrableOn
        (fun x => χ.laplacian x*localGamma μ Q f f x) (ball p b) μ :=
      ((localGamma_memL1 μ Q f f).bdd_mul (Lp.aestronglyMeasurable χ.laplacian)
        (χ.laplacian_bound.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)).integrableOn
    rw [hloc,hloc,← integral_const_mul,← integral_const_mul,
      ← integral_sub ((hi u).const_mul (1/2:ℝ)) ((hi q).const_mul (1/2:ℝ))]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only [e]; ring
  have hn0 : (n-a)*(∫ x, χ.weight x ∂μ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hna)
      (integral_nonneg fun x => (χ.bounds x).1)
  have hσ0 : 0 ≤ ∫ x, χ.weight x ∂σ := integral_nonneg fun x => (χ.bounds x).1
  have hh := (le_abs_self (∫ x in ball p b, χ.laplacian x*e x ∂μ)).trans hweighted
  rw [hsplit,hqident] at hh
  linarith only [hh,hn0,hσ0]

end RegularPointCoordinates

end

end OAI
