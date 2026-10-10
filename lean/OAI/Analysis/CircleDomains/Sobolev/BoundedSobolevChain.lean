import OAI.Analysis.CircleDomains.Sobolev.PositiveSobolevApproximation
import OAI.Analysis.CircleDomains.Sobolev.L2ProductConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace OAI

/-! Smooth scalar composition for the bounded, compactly supported
Sobolev functions needed by the local range argument. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem bounded_sobolev_chain_rule_Icc
    {u : EuclideanPlane → ℝ} (hw : DeGiorgi.MemW1pWitness 2 u univ)
    (hsu : HasCompactSupport u) {a b : ℝ} (hu : ∀ x, u x ∈ Icc a b) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i (fun x => deriv F (u x) * hw.weakGrad x i)
      (F ∘ u) univ := by
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have hgi : MemLp (fun x => hw.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hw.weakGrad_component_memLp i
  let un := planarMollification u
  have hb (n : ℕ) (x : EuclideanPlane) : un n x ∈ Icc a b :=
    planarMollification_mem_Icc huL.aestronglyMeasurable hu n x
  have hsm (n : ℕ) : ContDiff ℝ 1 (un n) :=
    (planarMollification_smooth (huL.locallyIntegrable (by norm_num)) n).of_le (by simp)
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hF.continuous.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    (hF.continuous_deriv le_rfl).continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg (F (u 0))).trans (hB (u 0) (hu 0))
  have hC0 : 0 ≤ C := (norm_nonneg (deriv F (u 0))).trans (hC (u 0) (hu 0))
  have hmeasure : TendstoInMeasure volume un atTop u :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (planarMollification_tendsto_L2 huL)
  obtain ⟨σ, hσ, hae⟩ := hmeasure.exists_seq_tendsto_ae
  intro φ hφ hs hsub
  let v : EuclideanPlane := EuclideanSpace.single i 1
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsdφ : HasCompactSupport (fun x => fderiv ℝ φ x v) := hs.fderiv_apply (𝕜 := ℝ) v
  have hleft := tendsto_integral_of_dominated_convergence
    (F := fun n x => F (un (σ n) x) * fderiv ℝ φ x v)
    (f := fun x => F (u x) * fderiv ℝ φ x v)
    (fun x => B * ‖fderiv ℝ φ x v‖)
    (fun n => ((hF.comp (hsm (σ n))).continuous.aestronglyMeasurable).mul
      hdφ.aestronglyMeasurable)
    ((hdφ.integrable_of_hasCompactSupport hsdφ).norm.const_mul B)
    (fun n => Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _ (hb _ x)) (norm_nonneg _))
    (by filter_upwards [hae] with x hx
        exact ((hF.continuous.tendsto _).comp hx).mul_const _)
  have hright := tendsto_integral_bounded_mul_L2
    (g := fun n x => fderiv ℝ (un (σ n)) x v)
    (G := fun x => hw.weakGrad x i)
    (h := fun n x => deriv F (un (σ n) x))
    (H := fun x => deriv F (u x))
    (φ := φ)
    (fun n => by
      have hd : Continuous (fun x => fderiv ℝ (un (σ n)) x v) :=
        ((hsm (σ n)).continuous_fderiv one_ne_zero).clm_apply continuous_const
      exact hd.memLp_of_hasCompactSupport
        ((planarMollification_hasCompactSupport hsu (σ n)).fderiv_apply (𝕜 := ℝ) v))
    hgi (hφ.continuous.memLp_of_hasCompactSupport hs)
    ((planarMollification_tendsto_gradient_L2 hw i).comp hσ.tendsto_atTop)
    (fun n => ((hF.continuous_deriv le_rfl).comp (hsm (σ n)).continuous).aestronglyMeasurable)
    hC0 (fun n => Eventually.of_forall fun x => hC _ (hb _ x))
    (by filter_upwards [hae] with x hx
        exact ((hF.continuous_deriv le_rfl).tendsto _).comp hx)
  have heq (n : ℕ) :
      (∫ x, F (un (σ n) x) * fderiv ℝ φ x v) =
        -(∫ x, deriv F (un (σ n) x) * fderiv ℝ (un (σ n)) x v * φ x) := by
    have hi := DeGiorgi.HasWeakPartialDeriv.of_contDiff (i := i) isOpen_univ
      (hF.comp (hsm (σ n))) φ hφ hs hsub
    simp only [Measure.restrict_univ] at hi
    have he (x : EuclideanPlane) : fderiv ℝ (F ∘ un (σ n)) x v =
        deriv F (un (σ n) x) * fderiv ℝ (un (σ n)) x v := by
      have hd := (hF.differentiable one_ne_zero (un (σ n) x)).hasDerivAt.comp_hasFDerivAt x
        ((hsm (σ n)).differentiable one_ne_zero x).hasFDerivAt
      simpa only [smul_apply, smul_eq_mul] using
        congrArg (fun L : EuclideanPlane →L[ℝ] ℝ => L v) hd.fderiv
    change (∫ x, F (un (σ n) x) * fderiv ℝ φ x v) =
      -(∫ x, fderiv ℝ (F ∘ un (σ n)) x v * φ x) at hi
    simpa only [he] using hi
  simp only [Measure.restrict_univ]
  exact tendsto_nhds_unique hleft (by simpa only [heq] using hright.neg)

 theorem bounded_sobolev_chain_rule
    {u : EuclideanPlane → ℝ} (hw : DeGiorgi.MemW1pWitness 2 u univ)
    (hsu : HasCompactSupport u) (hu : ∀ x, u x ∈ Icc 0 1) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i (fun x => deriv F (u x) * hw.weakGrad x i)
      (F ∘ u) univ := bounded_sobolev_chain_rule_Icc hw hsu hu hF i

end CircleDomainRigidity

end

end OAI
