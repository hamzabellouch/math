import Mathlib
import OAI.Geometry.PrescribedPotential.FiniteSobolevEmbedding
import OAI.Geometry.PrescribedPotential.SobolevProduct

namespace OAI

/-! Strong Derivatives. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartzCoord_dense (s : ℝ) : DenseRange (schwartzCoord (E := E) s) := by
  apply (SchwartzMap.denseRange_toLpCLM (E := E) (F := ℂ) (p := 2)
    (μ := volume) (by norm_num)).mono
  rintro u ⟨f, rfl⟩
  let ψ := SchwartzMap.fourierMultiplierCLM ℂ
    (fun x : E => (((1 + ‖x‖^2)^((-s)/2) : ℝ) : ℂ)) f
  refine ⟨ψ, ?_⟩
  apply l2_injective
  change (schwartzCoord s ψ : 𝓢'(E,ℂ)) = ((f.toLp 2 volume : L2 E) : 𝓢'(E,ℂ))
  rw [schwartzCoord_distribution]
  have hψ : (ψ : 𝓢'(E,ℂ)) = besselPotential E ℂ (-s) (f : 𝓢'(E,ℂ)) :=
    (fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop) f).symm
  rw [hψ, besselPotential_besselPotential_apply, neg_add_cancel,
    besselPotential_zero, ContinuousLinearMap.id_apply]
  exact (Lp.toTemperedDistribution_toLp_eq f).symm

lemma exists_schwartz_approx (s : ℝ) (u : L2 E) :
    ∃ f : ℕ → 𝓢(E,ℂ), Tendsto (fun n => schwartzCoord s (f n)) atTop (nhds u) := by
  obtain ⟨v,hv,ht⟩ := mem_closure_iff_seq_limit.mp (schwartzCoord_dense s u)
  choose f hf using hv
  refine ⟨f, ?_⟩
  simpa only [hf] using ht

 
def derivativeCoord (s : ℝ) (v : E) : L2 E →L[ℂ] L2 E :=
  liftOperator s (s-1) (lineDerivOpCLM ℂ 𝓢'(E,ℂ) v) (fun _ hu => hu.lineDerivOp)

lemma derivativeCoord_schwartz (s : ℝ) (v : E) (f : 𝓢(E,ℂ)) :
    derivativeCoord s v (schwartzCoord s f) = schwartzCoord (s-1) (∂_{v} f) := by
  apply realize_injective (s-1)
  exact (realize_liftOperator s (s-1) _ _ _).trans (by
    rw [realize_schwartzCoord, realize_schwartzCoord]
    exact lineDerivOp_toTemperedDistributionCLM_eq f v)

lemma strong_hasLineDerivAt (s : ℝ)
    (hs : (Module.finrank ℝ E : ℝ) < 2*s)
    (hs' : (Module.finrank ℝ E : ℝ) < 2*(s-1)) (u : L2 E) (x v : E) :
    HasLineDerivAt ℝ (strongEmbedding s hs u : E → ℂ)
      (strongEmbedding (s-1) hs' (derivativeCoord s v u) x) x v := by
  obtain ⟨f,hf⟩ := exists_schwartz_approx s u
  have h0 := ((strongEmbedding s hs).continuous.tendsto u).comp hf
  have h1 := ((strongEmbedding (s-1) hs').continuous.tendsto
    (derivativeCoord s v u)).comp (((derivativeCoord s v).continuous.tendsto u).comp hf)
  change Tendsto (fun n => strongEmbedding (s-1) hs'
    (derivativeCoord s v (schwartzCoord s (f n)))) atTop
    (nhds (strongEmbedding (s-1) hs' (derivativeCoord s v u))) at h1
  change Tendsto (fun n => strongEmbedding s hs (schwartzCoord s (f n))) atTop
    (nhds (strongEmbedding s hs u)) at h0
  simp_rw [derivativeCoord_schwartz, strongEmbedding_schwartz] at h1
  simp_rw [strongEmbedding_schwartz] at h0
  have h1' := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h1).comp
    (fun t : ℝ => x + t • v)
  have h0' := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h0
  have hd : ∀ n (t : ℝ), HasDerivAt (fun t : ℝ => f n (x + t • v))
      ((∂_{v} (f n) : 𝓢(E,ℂ)) (x + t • v)) t := by
    intro n t
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, one_smul, Function.comp_def, id_eq] using
      (f n).differentiableAt.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const v |>.const_add x)
  have hh := hasDerivAt_of_tendstoUniformly h1' (Eventually.of_forall hd)
    (fun t => h0'.tendsto_at (x+t • v)) 0
  simpa only [HasLineDerivAt, Function.comp_apply, zero_smul, add_zero] using hh

lemma strong_lineDeriv (s : ℝ)
    (hs : (Module.finrank ℝ E : ℝ) < 2*s)
    (hs' : (Module.finrank ℝ E : ℝ) < 2*(s-1)) (u : L2 E) (x v : E) :
    lineDeriv ℝ (strongEmbedding s hs u : E → ℂ) x v =
      strongEmbedding (s-1) hs' (derivativeCoord s v u) x :=
  (strong_hasLineDerivAt s hs hs' u x v).lineDeriv

lemma strong_fderiv (s : ℝ)
    (hs : (Module.finrank ℝ E : ℝ) < 2*s)
    (hs' : (Module.finrank ℝ E : ℝ) < 2*(s-1))
    (hN : (Module.finrank ℝ E : ℝ) < 2*(s-2)) (u : L2 E) (x v : E) :
    fderiv ℝ (strongEmbedding s hs u : E → ℂ) x v =
      strongEmbedding (s-1) hs' (derivativeCoord s v u) x := by
  have hd := (strongEmbedding_contDiff s hs 1 (by simpa using hN) u).differentiable
    (by norm_num)
  rw [← (hd x).lineDeriv_eq_fderiv]
  exact strong_lineDeriv s hs hs' u x v

lemma strong_second_fderiv (s : ℝ)
    (hs : (Module.finrank ℝ E : ℝ) < 2*s)
    (h1 : (Module.finrank ℝ E : ℝ) < 2*(s-1))
    (h2 : (Module.finrank ℝ E : ℝ) < 2*((s-1)-1))
    (hN : (Module.finrank ℝ E : ℝ) < 2*(s-4)) (u : L2 E) (x v w : E) :
    fderiv ℝ (fderiv ℝ (strongEmbedding s hs u : E → ℂ)) x v w =
      strongEmbedding ((s-1)-1) h2
        (derivativeCoord (s-1) v (derivativeCoord s w u)) x := by
  have hf := strongEmbedding_contDiff s hs 2 (by norm_num; exact hN) u
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have he : (fun y => fderiv ℝ (strongEmbedding s hs u : E → ℂ) y w) =
      (strongEmbedding (s-1) h1 (derivativeCoord s w u) : E → ℂ) := by
    funext y
    exact strong_fderiv s hs h1 (by linarith) u y w
  have hh : fderiv ℝ (fun y => fderiv ℝ (strongEmbedding s hs u : E → ℂ) y w) x v =
      fderiv ℝ (fderiv ℝ (strongEmbedding s hs u : E → ℂ)) x v w := by
    rw [fderiv_clm_apply (hd x) (differentiableAt_const w)]
    simp
  rw [← hh, he]
  exact strong_fderiv (s-1) h1 h2 (by linarith) (derivativeCoord s w u) x v

end SobolevChart

end
end

end OAI
