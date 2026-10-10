import OAI.Geometry.RCD.Heat.CanonicalHeatHessian
import OAI.Geometry.RCD.Sobolev.L1LimitLocalization

namespace OAI

/-! # Restricting the canonical Hessian to a smaller physical ball -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)

theorem IsCanonicalHeatHessian.restrict_weight
    {w v : SobolevSpace μ Q} {p : X} {r R : ℝ} (hrR : r ≤ R)
    {ψ : X → ℝ} (hψ : AEStronglyMeasurable ψ μ) (B : ℝ≥0)
    (hB : ∀ᵐ x ∂μ, |ψ x| ≤ B)
    (hψone : ∀ x∈closedBall p r, ψ x=1)
    {J : Lp ℝ 1 (μ.restrict (closedBall p R))}
    (hJ : IsCanonicalHeatHessian μ Q w v p R ψ J)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ μ) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂μ, |φ x| ≤ D) :
    ∃ I : Lp ℝ 1 (μ.restrict (closedBall p r)),
      IsCanonicalHeatHessian μ Q w v p r φ I ∧
      I =ᵐ[μ.restrict (closedBall p r)] fun x => φ x*J x := by
  have hsub : closedBall p r⊆closedBall p R := closedBall_subset_closedBall hrR
  have hJi : IntegrableOn (fun x => J x) (closedBall p R) μ :=
    memLp_one_iff_integrable.mp (Lp.memLp J)
  have hJsmall := hJi.mono_set hsub
  have hφJ : Integrable (fun x => φ x*J x) (μ.restrict (closedBall p r)) :=
    hJsmall.bdd_mul hφ.restrict ((ae_restrict_of_ae hD).mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  let I := hφJ.toL1 (fun x => φ x*J x)
  have hIr : I =ᵐ[μ.restrict (closedBall p r)] fun x => φ x*J x := hφJ.coeFn_toL1
  obtain ⟨A,C,hA,hC,hlim⟩ := hJ
  let u (k : ℕ) := heatH1 μ Q (1/(k+1:ℝ)) v
  let F (k : ℕ) (x : X) := ψ x*localHessianAction μ Q w (u k) (u k) (A k) (A k) (C k) x
  have hFi (k : ℕ) : Integrable (F k) μ :=
    (localHessianAction_integrable μ Q w (u k) (u k) (A k) (A k) (C k)).bdd_mul hψ
      (hB.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  have hlimsmall : Tendsto (fun k => ∫ x in closedBall p r, |F k x-J x| ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => integral_nonneg fun x => abs_nonneg _) ?_ hlim
    intro k
    exact setIntegral_mono_set ((hFi k).integrableOn.sub hJi).abs
      (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall hsub)
  have hweighted := integral_abs_bdd_mul_tendsto_zero (μ.restrict (closedBall p r)) F (fun x => J x)
    (fun k => (hFi k).integrableOn) hJsmall hlimsmall φ hφ.restrict D (ae_restrict_of_ae hD)
  refine ⟨I,?_,hIr⟩
  refine ⟨A,C,fun k => ae_restrict_of_ae_restrict_of_subset hsub (hA k),
    fun k => ae_restrict_of_ae_restrict_of_subset hsub (hC k),?_⟩
  apply hweighted.congr'
  refine Eventually.of_forall fun k => integral_congr_ae ?_
  filter_upwards [hIr,ae_restrict_mem measurableSet_closedBall] with x hx hm
  dsimp only [F]
  rw [hψone x hm,one_mul,hx]

end RegularPointCoordinates

end

end OAI
