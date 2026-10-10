import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Basic
import OAI.Geometry.CAT0Fillings.Compactness.Ascoli
import OAI.Geometry.CAT0Fillings.Compactness.Convolution

namespace OAI

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem totallyBounded_L1_of_translation {ι : Type*}
    (f : ι → E → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (M : ℝ≥0) (hM : ∀ i, (∫ x, |f i x| ∂μ) ≤ M)
    (R : ℝ) (hs : ∀ i, Function.support (f i) ⊆ closedBall (0:E) R)
    {C : ℝ} (hC : 0 ≤ C)
    (ht : ∀ i w, (∫ x, |f i (x+w)-f i x| ∂μ) ≤ C*‖w‖) :
    TotallyBounded (range fun i => (hf i).toL1 (f i)) := by
  apply totallyBounded_range_of_uniform_approx
  intro ε hε
  let δ := ε/(C+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  let η : ContDiffBump (0:E) := ⟨δ/2,δ,half_pos hδ,by linarith⟩
  let ρ := η.normed μ
  let g (i) := f i ⋆[lsmul ℝ ℝ, μ] ρ
  have hρc : HasCompactSupport ρ := η.hasCompactSupport_normed
  have hρ : Continuous ρ := η.continuous_normed
  have hρi : Integrable ρ μ := hρ.integrable_of_hasCompactSupport hρc
  have hg (i) : Integrable (g i) μ := (hf i).integrable_convolution (lsmul ℝ ℝ) hρi
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hρc (η.contDiff_normed (n := (⊤ : ℕ∞))) (by simp)
  obtain ⟨B,hB⟩ := hρ.bounded_above_of_compact_support hρc
  have hB0 : 0 ≤ B := (norm_nonneg (ρ 0)).trans (hB 0)
  have hgs (i) : Function.support (g i) ⊆ closedBall (0:E) (R+δ) := by
    apply convolution_scalar_support (hs i)
    dsimp [ρ]
    rw [η.support_normed_eq]
    exact ball_subset_closedBall
  have hgb (i) (x) : |g i x| ≤ B*M :=
    convolution_scalar_bound (hf i) hB0 (fun y => hB y) (hM i) x
  have hgl (i) : LipschitzWith (K*M) (g i) :=
    convolution_scalar_lipschitz (hf i) hρc hK (hM i)
  refine ⟨fun i => (hg i).toL1 (g i),
    totallyBounded_L1_of_compact_lipschitz_family g hg (K*M) hgl (B*M) (R+δ) hgb hgs,?_⟩
  intro i
  rw [dist_toL1_eq_integral]
  have he := mollifier_error_of_translation (hf i) hC (ht i) η
  have hcomm : (ρ ⋆[lsmul ℝ ℝ, μ] f i) = g i := by
    have hflip : (lsmul ℝ ℝ).flip = lsmul ℝ ℝ := by ext; simp
    simpa only [hflip,g] using (convolution_flip (L := lsmul ℝ ℝ) (f := f i) (g := ρ) (μ := μ))
  rw [hcomm] at he
  apply he.trans_lt
  change C*δ < ε
  dsimp [δ]
  rw [←mul_div_assoc]
  apply (div_lt_iff₀ (by linarith : 0 < C+1)).mpr
  nlinarith

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

lemma integral_le_of_closedBall_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f : E → ℝ} (hf : Integrable f μ) {C : ℝ}
    (hb : ∀ r : ℝ, (∫ x in closedBall (0:E) r, f x ∂μ) ≤ C) :
    (∫ x, f x ∂μ) ≤ C := by
  have hi : IntegrableOn f (⋃ n : ℕ, closedBall (0:E) n) μ := by
    simpa only [iUnion_closedBall_nat,integrableOn_univ] using hf
  have hl := tendsto_setIntegral_of_monotone (fun n : ℕ => measurableSet_closedBall)
    (fun i j hij => closedBall_subset_closedBall (Nat.cast_le.mpr hij)) hi
  simp only [iUnion_closedBall_nat,Measure.restrict_univ] at hl
  exact le_of_tendsto hl (Eventually.of_forall fun n : ℕ => hb n)

lemma full_segment_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : Continuous f') (x w : E) :
    |f (x+w)-f x| ≤ ‖w‖*∫ t in Icc (0:ℝ) 1, ‖f' (x+t • w)‖ := by
  let p (t : ℝ) := x+t • w
  have hp (t : ℝ) : HasDerivAt p w t := by
    simpa only [p,one_smul,id_eq] using ((hasDerivAt_id t).smul_const w).const_add x
  have hd (t : ℝ) := (hf (p t)).comp_hasDerivAt t (hp t)
  have hc : Continuous (fun t => f' (p t) w) := by dsimp [p]; fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (fun t _ => hd t) (hc.intervalIntegrable _ _)
  change (∫ t in (0:ℝ)..1, f' (p t) w) = f (p 1)-f (p 0) at hi
  simp only [p,zero_smul,one_smul,add_zero] at hi
  rw [←hi]
  apply (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
  have hh := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (hc.abs.intervalIntegrable _ _)
    ((show Continuous (fun t : ℝ => ‖w‖*‖f' (p t)‖) by dsimp [p]; fun_prop).intervalIntegrable _ _)
    (fun t _ => by simpa only [Real.norm_eq_abs,mul_comm] using (f' (p t)).le_opNorm w)
  apply hh.trans_eq
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le zero_le_one,
    ←integral_Icc_eq_integral_Ioc]

lemma smooth_translation_integral_bound {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : Continuous f')
    (hfi : Integrable f μ) (hgi : Integrable (fun x => ‖f' x‖) μ) (w : E) :
    (∫ x, |f (x+w)-f x| ∂μ) ≤ ‖w‖*∫ x, ‖f' x‖ ∂μ := by
  let m : Measure ℝ := volume.restrict (Icc 0 1)
  have : IsFiniteMeasure m := by dsimp [m]; infer_instance
  have he (t : ℝ) : (∫ x, ‖f' (x+t • w)‖ ∂μ) = ∫ x, ‖f' x‖ ∂μ :=
    integral_add_right_eq_self (fun x => ‖f' x‖) (t • w)
  have hp : Integrable (fun p : E × ℝ => ‖f' (p.1+p.2 • w)‖) (μ.prod m) := by
    apply (integrable_prod_iff' (show AEStronglyMeasurable
      (fun p : E × ℝ => ‖f' (p.1+p.2 • w)‖) (μ.prod m) from
        (show Continuous (fun p : E × ℝ => ‖f' (p.1+p.2 • w)‖) by fun_prop).aestronglyMeasurable)).mpr
    refine ⟨Eventually.of_forall fun t => hgi.comp_add_right (t • w),?_⟩
    simp only [norm_norm,he]
    exact integrable_const (μ := m) _
  have hh := integral_mono ((hfi.comp_add_right w).sub hfi).abs
    (hp.integral_prod_left.const_mul ‖w‖) (fun x => full_segment_bound hf hf' x w)
  rw [integral_const_mul,integral_integral_swap hp] at hh
  simp only [he,integral_const,smul_eq_mul] at hh
  have hm : m.real univ = 1 := by simp [m,measureReal_def,Real.volume_Icc]
  simpa only [←measureReal_def,hm,one_mul,Pi.sub_apply] using hh

end CAT0Fillings.JointBV
end

end OAI
