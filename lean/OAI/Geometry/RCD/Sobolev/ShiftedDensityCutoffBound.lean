import OAI.Geometry.RCD.Sobolev.ShiftedRadonCutoff

namespace OAI

/-! # Quantitative inner bounds from the full shifted cutoff mass

No absolute continuity of the full Bochner measure is needed. Its singular
part contributes with the correct sign to the upper bound.
-/

open Set Filter Metric MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem GoodLaplacianCutoff.shifted_density_le_full
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (σ : Measure X) [IsFiniteMeasure σ] (d : Lp ℝ 2 μ) (n : ℝ) :
    (∫ x, χ.weight x*((σ.rnDeriv μ x).toReal-2*d x+n) ∂μ) ≤
      (∫ x, χ.weight x ∂σ)-2*(∫ x, χ.weight x*d x ∂μ)+n*(∫ x, χ.weight x ∂μ) := by
  have hχ : Integrable χ.weight μ :=
    χ.weight.continuous.integrable_of_hasCompactSupport (χ.hasCompactSupport μ Q)
  have hd : Integrable (fun x => χ.weight x*d x) μ := by
    have hi := (Lp.memLp (SobolevSpace.toLp μ Q χ.sobolev)).integrable_mul (Lp.memLp d)
    exact hi.congr (χ.representative.mono fun x hx => by
      change SobolevSpace.toLp μ Q χ.sobolev x*d x=χ.weight x*d x
      rw [hx])
  have hRN : Integrable (fun x => χ.weight x*(σ.rnDeriv μ x).toReal) μ := by
    have hi : Integrable (fun x => (σ.rnDeriv μ x).toReal) μ := by
      simpa only [IntegrableOn,Measure.restrict_univ] using
        (Measure.integrableOn_toReal_rnDeriv (μ := σ) (ν := μ) (s := univ) (measure_ne_top _ _))
    exact hi.bdd_mul χ.weight.continuous.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (χ.bounds x).1]
      exact (χ.bounds x).2)
  have heq : (fun x => χ.weight x*((σ.rnDeriv μ x).toReal-2*d x+n))=
      fun x => χ.weight x*(σ.rnDeriv μ x).toReal-2*(χ.weight x*d x)+n*χ.weight x := by
    funext x
    ring
  have ha := integral_add (hRN.sub (hd.const_mul 2)) (hχ.const_mul n)
  simp only [Pi.sub_apply] at ha
  rw [heq,ha,integral_sub hRN (hd.const_mul 2),integral_const_mul,integral_const_mul]
  linarith only [χ.weighted_radon_le_full μ Q σ]

theorem GoodLaplacianCutoff.shifted_inner_density_le
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (σ : Measure X) [IsFiniteMeasure σ] (d : Lp ℝ 2 μ) (n : ℝ)
    (hpos : ∀ᵐ x ∂μ.restrict (closedBall p (2*r)),
      0≤(σ.rnDeriv μ x).toReal-2*d x+n)
    {S : Set X} (hS : MeasurableSet S) (hsub : S⊆ball p r) :
    (∫ x in S, (σ.rnDeriv μ x).toReal-2*d x+n ∂μ) ≤
      (∫ x, χ.weight x ∂σ)-2*(∫ x, χ.weight x*d x ∂μ)+n*(∫ x, χ.weight x ∂μ) := by
  have hp : ∀ᵐ x ∂μ, 0≤χ.weight x*((σ.rnDeriv μ x).toReal-2*d x+n) := by
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp hpos] with x hx
    by_cases hm : x∈closedBall p (2*r)
    · exact mul_nonneg (χ.bounds x).1 (hx hm)
    · rw [χ.zero x (lt_of_not_ge (by simpa only [mem_closedBall,dist_comm] using hm)),zero_mul]
  have heq : (fun x => χ.weight x*((σ.rnDeriv μ x).toReal-2*d x+n))
      =ᵐ[μ.restrict S] fun x => (σ.rnDeriv μ x).toReal-2*d x+n := by
    filter_upwards [ae_restrict_mem hS] with x hx
    rw [χ.one x (hsub hx),one_mul]
  rw [← integral_congr_ae heq]
  exact (integral_mono_measure Measure.restrict_le_self hp
    (χ.shifted_density_integrable μ Q σ d n)).trans (χ.shifted_density_le_full μ Q σ d n)

theorem GoodLaplacianCutoff.shifted_inner_density_eventually_le
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (σ : ℕ → Measure X) [∀ k, IsFiniteMeasure (σ k)] (d : ℕ → Lp ℝ 2 μ) (n : ℝ)
    (hpos : ∀ k, ∀ᵐ x ∂μ.restrict (closedBall p (2*r)),
      0≤((σ k).rnDeriv μ x).toReal-2*d k x+n)
    {S : Set X} (hS : MeasurableSet S) (hsub : S⊆ball p r) {ell B : ℝ}
    (hlim : Tendsto (fun k => (∫ x, χ.weight x ∂σ k)-
      2*(∫ x, χ.weight x*d k x ∂μ)+n*(∫ x, χ.weight x ∂μ)) atTop (𝓝 ell))
    (hB : ell≤B) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k in atTop, (∫ x in S, ((σ k).rnDeriv μ x).toReal-2*d k x+n ∂μ)≤B+ε := by
  filter_upwards [hlim.eventually (gt_mem_nhds (show ell<B+ε by linarith))] with k hk
  exact (χ.shifted_inner_density_le μ Q (σ k) (d k) n (hpos k) hS hsub).trans hk.le

end RegularPointCoordinates

end

end OAI
