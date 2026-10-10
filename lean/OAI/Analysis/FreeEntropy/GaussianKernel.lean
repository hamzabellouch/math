import OAI.Analysis.FreeEntropy.GaussianDensity

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal Topology
namespace FiniteEntropySeparation
 variable {ι : Type u1} [Fintype ι]
 def normalKernel (s : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
    Real.exp (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)-‖x‖^2/(2*s))
 theorem normalKernel_pos (s : ℝ) (x : EuclideanSpace ℝ ι) : 0<normalKernel s x := Real.exp_pos _
 theorem normalKernel_formula {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    normalKernel s x = (Real.sqrt (2*Real.pi*s))⁻¹^(Fintype.card ι)*Real.exp (-‖x‖^2/(2*s)) := by
  rw [normalKernel,sub_eq_add_neg,Real.exp_add]
  simp only [neg_div]
  congr 1
  have hp : 0<2*Real.pi*s := by positivity
  rw [← Real.exp_log (show 0<(Real.sqrt (2*Real.pi*s))⁻¹^(Fintype.card ι) by positivity),Real.log_pow,Real.log_inv,Real.log_sqrt hp.le]
  congr 1
  ring
 theorem normalKernel_product {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    normalKernel s x = ∏ i,gaussianPDFReal 0 ⟨s,hs.le⟩ (x i) := by
  classical
  rw [normalKernel_formula hs]
  simp only [gaussianPDFReal,sub_zero,prod_mul_distrib,prod_const,card_univ,← Real.exp_sum]
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs,sq_abs,← sum_div,sum_neg_distrib]
  rfl
 theorem normalKernel_integrable {s : ℝ} (hs : 0<s) : Integrable (normalKernel (ι := ι) s) := by
  rw [← (PiLp.volume_preserving_toLp ι).integrable_comp_emb (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simpa only [Function.comp_def,normalKernel_product hs,WithLp.ofLp_toLp,volume_pi] using
    Integrable.fintype_prod (fun _ : ι => integrable_gaussianPDFReal 0 ⟨s,hs.le⟩)
 theorem normalKernel_integral {s : ℝ} (hs : 0<s) : ∫ x : EuclideanSpace ℝ ι,normalKernel s x = 1 := by
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simp only [normalKernel_product hs,integral_fintype_prod_volume_eq_prod]
  have h : (∫ x : ℝ,gaussianPDFReal 0 ⟨s,hs.le⟩ x)=1 := integral_gaussianPDFReal_eq_one 0 (fun h => hs.ne' (congrArg (fun z : ℝ≥0 => (z:ℝ)) h))
  simp only [h,prod_const_one]
 theorem normalKernel_continuous_space (s : ℝ) : Continuous (normalKernel (ι := ι) s) := by
  unfold normalKernel
  fun_prop
 theorem normalKernel_continuousOn : ContinuousOn (fun z : ℝ × EuclideanSpace ℝ ι => normalKernel z.1 z.2) {z | 0<z.1} := by
  unfold normalKernel
  apply Real.continuous_exp.comp_continuousOn
  apply ContinuousOn.sub
  · apply continuousOn_const.mul
    apply ContinuousOn.log
    · fun_prop
    · intro z hz; exact ne_of_gt (by dsimp at hz ⊢; positivity)
  · apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro z hz; exact ne_of_gt (by dsimp at hz ⊢; positivity)
 theorem normalKernel_hasDeriv_time {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    HasDerivAt (fun t => normalKernel t x)
      ((-(Fintype.card ι:ℝ)/(2*s)+‖x‖^2/(2*s^2))*normalKernel s x) s := by
  have hp : 2*Real.pi*s≠0 := by positivity
  have hd := (((((hasDerivAt_id s).const_mul (2*Real.pi)).log hp).const_mul (-(Fintype.card ι:ℝ)/2)).sub
    ((hasDerivAt_const s (‖x‖^2)).div ((hasDerivAt_id s).const_mul 2) (by positivity))).exp
  convert hd using 1
  · rfl
  · dsimp only [normalKernel,id_eq,Pi.sub_apply,Pi.div_apply]
    rw [mul_comm _ (Real.exp _)]
    congr 1
    field_simp [hs.ne',Real.pi_ne_zero]
    ring
 theorem normalKernel_hasDeriv_coordinate [DecidableEq ι] (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    HasDerivAt (fun t : ℝ => normalKernel s (x+t • EuclideanSpace.single i 1))
      (-(x i)/s*normalKernel s x) 0 := by
  classical
  have hd : HasDerivAt (fun t : ℝ => ‖x+t • EuclideanSpace.single i 1‖^2) (2*x i) 0 := by
    have h := ((hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id 0).smul_const (EuclideanSpace.single i 1))).norm_sq
    simpa [real_inner_comm,PiLp.inner_apply,EuclideanSpace.single] using h
  have h := ((hasDerivAt_const 0 (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s))).sub (hd.div_const (2*s))).exp
  convert h using 1
  · rfl
  · dsimp only [Pi.sub_apply]
    simp only [zero_smul,add_zero,normalKernel]
    ring
end FiniteEntropySeparation

end

end OAI
