import OAI.Geometry.RCD.Transport.SobolevPlanVariation
import OAI.Geometry.RCD.Transport.TestPlanLocalProperty

namespace OAI

/-! # One absolutely continuous coefficient family along almost every path -/

open Set Filter MeasureTheory Finset
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem sobolev_frame_plan_variation (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    {n : ℕ} (G : Fin n → SobolevSpace μ Q)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π) :
    ∀ᵐ γ ∂π, ∃ b : Fin n → ℝ → ℝ,
      (∀ i, AbsolutelyContinuousOnInterval (b i) 0 1) ∧
      (∀ i, b i 0=SobolevSpace.toLp μ Q (G i) (γ 0)) ∧
      (∀ i, b i 1=SobolevSpace.toLp μ Q (G i) (γ 1)) ∧
      (∀ i, b i =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
        fun t => SobolevSpace.toLp μ Q (G i) (geodesicExtension γ t)) ∧
      (∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b i) t|)^2≤
        (n:ℝ)*(dist (γ 0) (γ 1))^2*
          ∑ i, ∫ t in Icc (0:ℝ) 1, localGamma μ Q (G i) (G i) (geodesicExtension γ t) := by
  have hv (i : Fin n) := (SobolevSpace.minimalSlope_isRelaxed μ Q (G i)).testPlan_ae_sobolev_variation
    μ π hgeo hC hcomp hD
  have he (i : Fin n) := testPlan_eval_property_on μ π hcomp MeasurableSet.univ
    (Eventually.of_forall fun _ _ => mem_univ _) (show ∀ᵐ x ∂μ.restrict univ,
      localGamma μ Q (G i) (G i) x=(SobolevSpace.minimalSlope μ Q (G i) x)^2 from by
        filter_upwards [ae_restrict_of_ae (localGamma_self μ Q (G i))] with x hx
        exact hx)
  filter_upwards [ae_all_iff.mpr hv,ae_all_iff.mpr he] with γ hv he
  choose b hb h0 h1 heq hvar using hv
  refine ⟨b,hb,h0,h1,heq,?_⟩
  have hsum : (∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b i) t|)^2≤
      (n:ℝ)*∑ i, (∫ t in Icc (0:ℝ) 1, |deriv (b i) t|)^2 := by
    have hh := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin n)) (fun _ => (1:ℝ))
      (fun i => ∫ t in Icc (0:ℝ) 1, |deriv (b i) t|)
    simpa only [one_mul,one_pow,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hh
  apply hsum.trans
  calc
    _ ≤ (n:ℝ)*∑ i, (dist (γ 0) (γ 1))^2*
        ∫ t in Icc (0:ℝ) 1, localGamma μ Q (G i) (G i) (geodesicExtension γ t) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      apply sum_le_sum
      intro i _
      have hh : (∫ t in Icc (0:ℝ) 1, localGamma μ Q (G i) (G i) (geodesicExtension γ t))=
          ∫ t in Icc (0:ℝ) 1, (SobolevSpace.minimalSlope μ Q (G i) (geodesicExtension γ t))^2 :=
        integral_congr_ae (he i)
      rw [hh]
      exact hvar i
    _ = _ := by rw [← mul_sum]; ring

end RegularPointCoordinates

end

end OAI
