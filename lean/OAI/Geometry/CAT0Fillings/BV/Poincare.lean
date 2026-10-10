import Mathlib
import OAI.Geometry.CAT0Fillings.Slices.NormalBudget

namespace OAI

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {ν : Measure E} [IsFiniteMeasure ν]

def DirectionalVariation (f : E → ℝ) (v : E) (μ ν : Measure E) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    |∫ x, (fderiv ℝ φ x) v * f x ∂μ| ≤ ∫ x, |φ x| ∂ν

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] [IsFiniteMeasure ν] in
lemma convolution_direction_bound {f η : E → ℝ} (hf : LocallyIntegrable f μ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x)
    {v : E} (hv : DirectionalVariation f v μ ν) (z : E) :
    |((f ⋆[(lsmul ℝ ℝ).precompR E, μ] fderiv ℝ η) z) v| ≤
      ∫ x, η (z-x) ∂ν := by
  let φ : E → ℝ := fun x => η (z-x)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hη.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.subLeft z)
  have hd (x : E) : fderiv ℝ φ x = -(fderiv ℝ η (z-x)) := by
    have hh := ((hη.differentiable (by simp)) (z-x)).hasFDerivAt.comp x
      ((hasFDerivAt_const z x).sub (hasFDerivAt_id x))
    simpa [φ,Function.comp_def] using hh.fderiv
  have hb := hv φ hφ hcφ
  simp only [hd,neg_apply,neg_mul,integral_neg,abs_neg] at hb
  have he : (fun x => |φ x|) = (fun x => η (z-x)) := by
    funext x
    exact abs_of_nonneg (hη0 _)
  rw [he] at hb
  rw [convolution_precompR_apply (lsmul ℝ ℝ) hf (hc.fderiv ℝ)
    (hη.continuous_fderiv (by simp)), convolution_def]
  simpa only [lsmul_apply,smul_eq_mul,mul_comm] using hb

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma continuous_kernelIntegral {η : E → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) : Continuous (fun z => ∫ x, η (z-x) ∂ν) := by
  obtain ⟨C,hbound⟩ := hη.bounded_above_of_compact_support hc
  exact continuous_of_dominated (bound := fun _ => C)
    (fun z => ((hη.comp (continuous_const.sub continuous_id)).aestronglyMeasurable))
    (fun z => ae_of_all _ fun x => hbound (z-x)) (integrable_const C)
    (ae_of_all _ fun x => hη.comp (continuous_id.sub continuous_const))

lemma kernelIntegral_ball_bound {η : E → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) (hint : ∫ x, η x ∂μ = 1)
    {ε : ℝ} (hs : Function.support η ⊆ closedBall 0 ε) (a : E) (r : ℝ) :
    (∫ z in closedBall a r, ∫ x, η (z-x) ∂ν ∂μ) ≤ ν.real (closedBall a (r+ε)) := by
  let Q := closedBall a r
  let A := closedBall a (r+ε)
  have : IsFiniteMeasure (μ.restrict Q) := ⟨by simp [Q,measure_closedBall_lt_top]⟩
  obtain ⟨C,hC⟩ := hη.bounded_above_of_compact_support hc
  have hp : Integrable (fun p : E × E => η (p.1-p.2)) ((μ.restrict Q).prod ν) :=
    Integrable.of_bound (hη.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable C
      (ae_of_all _ fun p => hC _)
  have hfub := integral_integral_swap (f := fun z x => η (z-x)) hp
  change (∫ z, ∫ x, η (z-x) ∂ν ∂μ.restrict Q) ≤ _
  rw [hfub]
  have hz (x : E) : Integrable (fun z => η (z-x)) μ := by
    exact (hη.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      (hc.comp_homeomorph (Homeomorph.subRight x))
  have hpoint (x : E) : (∫ z in Q, η (z-x) ∂μ) ≤ A.indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      calc _ ≤ ∫ z, η (z-x) ∂μ := setIntegral_le_integral (hz x) (ae_of_all _ fun z => hη0 _)
        _ = 1 := by rw [integral_sub_right_eq_self, hint]
    · rw [indicator_of_notMem hx]
      have he : ∀ z ∈ Q, η (z-x) = 0 := by
        intro z hz
        by_contra hn
        have hn' : z-x ∈ closedBall 0 ε := hs hn
        have hd : dist x a ≤ r+ε := calc
          dist x a ≤ dist x z + dist z a := dist_triangle _ _ _
          _ ≤ ε + r := add_le_add (by simpa [dist_eq_norm, norm_sub_rev] using hn') hz
          _ = r+ε := add_comm _ _
        exact hx hd
      rw [setIntegral_congr_fun measurableSet_closedBall he,integral_zero]
  have hm := integral_mono hp.integral_prod_right
    ((integrable_const (1:ℝ) : Integrable (fun _ : E => (1:ℝ)) ν).indicator measurableSet_closedBall)
    hpoint
  exact hm.trans_eq (by rw [integral_indicator measurableSet_closedBall]; simp)

lemma euclidean_opNorm_le_coordinate_bound {k : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, |L (EuclideanSpace.basisFun (Fin k) ℝ i)| ≤ B) : ‖L‖ ≤ k*B := by
  apply L.opNorm_le_bound (by positivity)
  intro x
  have he := congrArg L ((EuclideanSpace.basisFun (Fin k) ℝ).sum_repr x)
  rw [map_sum] at he
  rw [←he]
  calc _ ≤ ∑ i : Fin k, ‖L (((EuclideanSpace.basisFun (Fin k) ℝ).repr x).ofLp i •
        EuclideanSpace.basisFun (Fin k) ℝ i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k, ‖x‖*B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [map_smul,norm_smul]
      apply mul_le_mul _ (hb i) (abs_nonneg _) (norm_nonneg _)
      simpa using (PiLp.norm_apply_le ((EuclideanSpace.basisFun (Fin k) ℝ).repr x) i)
    _ = k*B*‖x‖ := by simp; ring

lemma mollified_gradient_integral_bound {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {m : Measure (EuclideanSpace ℝ (Fin k))} [m.IsAddHaarMeasure]
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ν]
    (hf : LocallyIntegrable f m)
    (hv : ∀ i, DirectionalVariation f (EuclideanSpace.basisFun (Fin k) ℝ i) m ν)
    (η : ContDiffBump (0 : EuclideanSpace ℝ (Fin k))) (a : EuclideanSpace ℝ (Fin k)) (r : ℝ) :
    (∫ z in closedBall a r,
      ‖(f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), m]
        fderiv ℝ (η.normed m)) z‖ ∂m) ≤ k * ν.real (closedBall a (r+η.rOut)) := by
  have hc := η.hasCompactSupport_normed (μ := m)
  have hd := (η.contDiff_normed (μ := m) (n := (⊤ : ℕ∞))).continuous_fderiv (by simp)
  have hg := (hc.fderiv ℝ).continuous_convolution_right
    ((lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k))) hf hd
  have hb (z : EuclideanSpace ℝ (Fin k)) :
      ‖(f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), m]
          fderiv ℝ (η.normed m)) z‖ ≤ k * ∫ x, η.normed m (z-x) ∂ν := by
    apply euclidean_opNorm_le_coordinate_bound _ (integral_nonneg fun x => η.nonneg_normed _)
    intro i
    exact convolution_direction_bound hf η.contDiff_normed hc η.nonneg_normed (hv i) z
  have hk := (continuous_kernelIntegral (ν := ν) η.continuous_normed hc).const_mul (k:ℝ)
  have hm := integral_mono
    (hg.norm.continuousOn.integrableOn_compact (μ := m) (isCompact_closedBall a r))
    (hk.continuousOn.integrableOn_compact (μ := m) (isCompact_closedBall a r)) hb
  rw [integral_const_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (kernelIntegral_ball_bound η.continuous_normed hc η.nonneg_normed η.integral_normed
      (by rw [η.support_normed_eq]; exact ball_subset_closedBall) a r) (Nat.cast_nonneg k))

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal Pointwise

noncomputable section
namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma setIntegral_translate (g : E → ℝ) (v : E) (s : Set E) :
    (∫ x in s, g (x+v) ∂μ) = ∫ x in (fun x => x+v) '' s, g x ∂μ := by
  let e := (Homeomorph.addRight v).toMeasurableEquiv
  have hmap : Measure.map e μ = μ := (measurePreserving_add_right μ v).map_eq
  have hpre : e ⁻¹' (e '' s) = s := e.injective.preimage_image s
  have hh := setIntegral_map_equiv (μ := μ) e g (e '' s)
  rw [hmap,hpre] at hh
  exact hh.symm

lemma affine_ball_integral_le {g : E → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    {a y : E} {r t : ℝ} (hy : y ∈ closedBall a r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) :
    (∫ x in closedBall a r, g ((1-t) • x + t • y) ∂μ) ≤
      (2:ℝ)^Module.finrank ℝ E * ∫ x in closedBall a r, g x ∂μ := by
  have hR : 0 < 1-t := by linarith
  let s : Set E := (1-t) • closedBall a r
  let A : Set E := (fun x => x + t • y) '' s
  have hsub : A ⊆ closedBall a r := by
    rintro z ⟨w,⟨x,hx,rfl⟩,rfl⟩
    exact convex_closedBall a r hx hy (by linarith) ht0 (by ring)
  have he : (∫ x in closedBall a r, g ((1-t) • x+t • y) ∂μ) =
      ((1-t)^Module.finrank ℝ E)⁻¹ * ∫ x in A, g x ∂μ := by
    rw [Measure.setIntegral_comp_smul_of_pos μ (fun x => g (x+t • y)) _ hR,
      setIntegral_translate]
    rfl
  have hi : IntegrableOn g (closedBall a r) μ :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall a r) hg.continuousOn
  have hm : (∫ x in A, g x ∂μ) ≤ ∫ x in closedBall a r, g x ∂μ :=
    setIntegral_mono_set hi (ae_of_all _ hg0) (ae_of_all _ hsub)
  have hc : ((1-t)^Module.finrank ℝ E)⁻¹ ≤ (2:ℝ)^Module.finrank ℝ E := by
    rw [←inv_pow]
    apply pow_le_pow_left₀ (inv_nonneg.mpr hR.le)
    apply (inv_le_comm₀ hR (by norm_num : (0:ℝ) < 2)).mpr
    norm_num
    linarith
  rw [he]
  exact (mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr (pow_nonneg hR.le _))).trans
    (mul_le_mul_of_nonneg_right hc (integral_nonneg hg0))

def halfMean (g : E → ℝ) (x y : E) : ℝ :=
  ∫ t in Icc (0:ℝ) (1/2), g ((1-t) • x+t • y)

omit [MeasurableSpace E] [BorelSpace E] in
lemma halfMean_continuous {g : E → ℝ} (hg : Continuous g) :
    Continuous (fun p : E × E => halfMean g p.1 p.2) := by
  exact continuous_parametric_integral_of_continuous
    (by change Continuous (fun p : (E × E) × ℝ => g ((1-p.2) • p.1.1+p.2 • p.1.2)); fun_prop)
    isCompact_Icc

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma halfMean_nonneg {g : E → ℝ} (hg0 : ∀ x, 0 ≤ g x) (x y : E) :
    0 ≤ halfMean g x y := integral_nonneg fun _ => hg0 _

lemma halfMean_integral_le {g : E → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    {a y : E} {r : ℝ} (hy : y ∈ closedBall a r) :
    (∫ x in closedBall a r, halfMean g x y ∂μ) ≤
      (1/2:ℝ)*(2:ℝ)^Module.finrank ℝ E * ∫ x in closedBall a r, g x ∂μ := by
  have hi : Integrable (fun p : E × ℝ => g ((1-p.2) • p.1+p.2 • y))
      ((μ.restrict (closedBall a r)).prod (volume.restrict (Icc 0 (1/2)))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact ((isCompact_closedBall a r).prod isCompact_Icc)
      (by fun_prop)
  simp only [halfMean]
  rw [integral_integral_swap hi]
  apply le_trans (setIntegral_mono_on hi.integral_prod_right (integrableOn_const measure_Icc_lt_top.ne)
    measurableSet_Icc (fun t ht => affine_ball_integral_le hg hg0 hy ht.1 ht.2))
  simp only [integral_const,smul_eq_mul,measureReal_def,Measure.restrict_apply_univ,Real.volume_Icc]
  norm_num
  ring_nf
  exact le_rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma half_segment_bound {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : Continuous f') (x y : E) :
    |f x-f ((1/2:ℝ) • x+(1/2:ℝ) • y)| ≤ ‖y-x‖*halfMean (fun z => ‖f' z‖) x y := by
  let p (t : ℝ) := (1-t) • x+t • y
  have hp (t : ℝ) : HasDerivAt p (y-x) t := by
    convert (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).smul_const x).add
      ((hasDerivAt_id t).smul_const y) using 1 <;> simp [p,sub_eq_add_neg,add_comm,Pi.add_def]
  have hder (t : ℝ) := (hf (p t)).comp_hasDerivAt t (hp t)
  have hc : Continuous (fun t => f' (p t) (y-x)) := by dsimp [p]; fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1/2) (fun t _ => hder t) (hc.intervalIntegrable _ _)
  have hp0 : p 0 = x := by simp [p]
  have hp1 : p (1/2) = (1/2:ℝ) • x+(1/2:ℝ) • y := by norm_num [p]
  change (∫ t in (0:ℝ)..1/2, f' (p t) (y-x)) = f (p (1/2))-f (p 0) at hint
  rw [hp0,hp1] at hint
  rw [abs_sub_comm,←hint]
  apply (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0:ℝ) ≤ 1/2)).trans
  have hh := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1/2)
    (hc.abs.intervalIntegrable _ _)
    ((show Continuous (fun t : ℝ => ‖y-x‖*‖f' (p t)‖) by dsimp [p]; fun_prop).intervalIntegrable _ _)
    (fun t _ => by simpa only [Real.norm_eq_abs,mul_comm] using (f' (p t)).le_opNorm (y-x))
  apply hh.trans_eq
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2),
    ←integral_Icc_eq_integral_Ioc]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma segment_pair_bound {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : Continuous f')
    {a x y : E} {r : ℝ} (hx : x ∈ closedBall a r) (hy : y ∈ closedBall a r) :
    |f x-f y| ≤ 2*r*(halfMean (fun z => ‖f' z‖) x y + halfMean (fun z => ‖f' z‖) y x) := by
  have h1 := half_segment_bound hf hf' x y
  have h2 := half_segment_bound hf hf' y x
  have hd : ‖y-x‖ ≤ 2*r := by
    rw [←dist_eq_norm]
    exact (dist_triangle y a x).trans (by rw [dist_comm a x]; linarith [mem_closedBall.mp hy,mem_closedBall.mp hx])
  have hs : ‖x-y‖ = ‖y-x‖ := norm_sub_rev _ _
  have he : (1/2:ℝ) • y+(1/2:ℝ) • x = (1/2:ℝ) • x+(1/2:ℝ) • y := add_comm _ _
  rw [he,hs] at h2
  have ht := abs_sub_le (f x) (f ((1/2:ℝ) • x+(1/2:ℝ) • y)) (f y)
  rw [abs_sub_comm (f ((1/2:ℝ) • x+(1/2:ℝ) • y)) (f y)] at ht
  calc _ ≤ ‖y-x‖*(halfMean (fun z => ‖f' z‖) x y + halfMean (fun z => ‖f' z‖) y x) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hd (add_nonneg (halfMean_nonneg (fun _ => norm_nonneg _) x y)
      (halfMean_nonneg (fun _ => norm_nonneg _) y x))

theorem smooth_ball_poincare {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : Continuous f') (a : E) {r : ℝ} (hr : 0 < r) :
    (∫ x in closedBall a r, |f x-(⨍ y in closedBall a r, f y ∂μ)| ∂μ) ≤
      2*(2:ℝ)^Module.finrank ℝ E*r*∫ x in closedBall a r, ‖f' x‖ ∂μ := by
  let Q := closedBall a r
  let H := halfMean (fun z => ‖f' z‖)
  let J := ∫ x in Q, ‖f' x‖ ∂μ
  let A := (1/2:ℝ)*(2:ℝ)^Module.finrank ℝ E*J
  have hQ : IsCompact Q := isCompact_closedBall a r
  have hQm : MeasurableSet Q := hQ.measurableSet
  have hQ0 : 0 < μ.real Q := ENNReal.toReal_pos
    (ne_of_gt ((measure_ball_pos μ a hr).trans_le (measure_mono ball_subset_closedBall)))
    measure_closedBall_lt_top.ne
  have : IsFiniteMeasure (μ.restrict Q) := ⟨by simpa using hQ.measure_lt_top⟩
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hH : Continuous (fun p : E × E => H p.1 p.2) := halfMean_continuous hf'.norm
  have hHI : Integrable (fun p : E × E => H p.1 p.2) ((μ.restrict Q).prod (μ.restrict Q)) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact (hQ.prod hQ) hH.continuousOn
  have hPI : Integrable (fun p : E × E => |f p.1-f p.2|) ((μ.restrict Q).prod (μ.restrict Q)) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact (hQ.prod hQ) (by fun_prop)
  have hHbound : (∫ x in Q, ∫ y in Q, H x y ∂μ ∂μ) ≤ μ.real Q*A := by
    rw [integral_integral_swap hHI]
    apply le_trans (setIntegral_mono_on hHI.integral_prod_right (integrable_const A)
      hQm (fun y hy => halfMean_integral_le hf'.norm (fun _ => norm_nonneg _) hy))
    simp [integral_const,smul_eq_mul]
  have hdouble : (∫ x in Q, ∫ y in Q, |f x-f y| ∂μ ∂μ) ≤ 4*r*(μ.real Q*A) := by
    have hpoint (x : E) (hx : x ∈ Q) :
        (∫ y in Q, |f x-f y| ∂μ) ≤ 2*r*((∫ y in Q, H x y ∂μ)+(∫ y in Q, H y x ∂μ)) := by
      have hi1 : IntegrableOn (fun y => H x y) Q μ :=
        ContinuousOn.integrableOn_compact hQ (hH.comp (continuous_const.prodMk continuous_id)).continuousOn
      have hi2 : IntegrableOn (fun y => H y x) Q μ :=
        ContinuousOn.integrableOn_compact hQ (hH.comp (continuous_id.prodMk continuous_const)).continuousOn
      rw [←integral_add hi1 hi2,←integral_const_mul]
      exact setIntegral_mono_on
        (ContinuousOn.integrableOn_compact hQ (by fun_prop)) ((hi1.add hi2).const_mul _) hQm
        (fun y hy => segment_pair_bound hf hf' hx hy)
    have hh := setIntegral_mono_on hPI.integral_prod_left
      ((hHI.integral_prod_left.add hHI.integral_prod_right).const_mul (2*r)) hQm hpoint
    rw [integral_const_mul] at hh
    simp only [Pi.add_apply] at hh
    rw [integral_add hHI.integral_prod_left hHI.integral_prod_right] at hh
    have hswap := integral_integral_swap (f := fun x y => H x y) hHI
    rw [←hswap] at hh
    exact hh.trans (by nlinarith)
  have hfi : IntegrableOn f Q μ := ContinuousOn.integrableOn_compact hQ hfc.continuousOn
  have hmean (x : E) :
      |f x-(⨍ y in Q, f y ∂μ)| ≤ (μ.real Q)⁻¹*∫ y in Q, |f x-f y| ∂μ := by
    have he : f x-(⨍ y in Q, f y ∂μ) = (μ.real Q)⁻¹*∫ y in Q, f x-f y ∂μ := by
      rw [integral_sub (integrable_const (f x)) hfi,integral_const,setAverage_eq]
      simp only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul]
      field_simp [show (μ Q).toReal ≠ 0 from hQ0.ne']
    rw [he,abs_mul,abs_of_nonneg (inv_nonneg.mpr hQ0.le)]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.mpr hQ0.le)
  have hosc := setIntegral_mono_on
    (ContinuousOn.integrableOn_compact hQ (hfc.sub continuous_const).abs.continuousOn)
    (hPI.integral_prod_left.const_mul ((μ.real Q)⁻¹)) hQm (fun x _ => hmean x)
  rw [integral_const_mul] at hosc
  apply (hosc.trans (mul_le_mul_of_nonneg_left hdouble (inv_nonneg.mpr hQ0.le))).trans_eq
  dsimp [A,J]
  have hn : μ.real Q ≠ 0 := hQ0.ne'
  change (μ.real Q)⁻¹*(4*r*(μ.real Q*((1/2:ℝ)*2^Module.finrank ℝ E*(∫ x in Q, ‖f' x‖ ∂μ)))) = _
  field_simp [hn]
  ring

end CAT0Fillings.JointBV

end
end

end OAI
