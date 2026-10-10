import Mathlib
import OAI.Probability.Perceptron.Brownian.CountableGaussianField
import OAI.Probability.Perceptron.Variational.GaussianBlock

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

lemma stdGaussian_radial_preserving (n : ℕ) :
    MeasurePreserving (fun p : Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1 => p.1.val •p.2.val)
      ((gaussianRadiusLaw n).prod (unitSphereLaw (n+1))) (stdGaussian (Spin (n+1))) := by
  refine ⟨by fun_prop,?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (by fun_prop),lintegral_prod _ (by fun_prop)]
  exact (stdGaussian_polar_lintegral n F hF).symm

def cavityBlockNormalize (N L : ℕ) (p : Spin N×Spin L) : Spin N×Spin L :=
  let a := (Real.sqrt (‖p.1‖^2+‖p.2‖^2))⁻¹
  (a •p.1,a •p.2)

lemma cavityBlockNormalize_measurable (N L : ℕ) : Measurable (cavityBlockNormalize N L) := by
  unfold cavityBlockNormalize
  fun_prop

lemma gaussianBlockSplit_normalize (N L : ℕ) (x : Spin (N+L)) :
    gaussianBlockSplit N L (‖x‖⁻¹ •x)=cavityBlockNormalize N L (gaussianBlockSplit N L x) := by
  unfold cavityBlockNormalize
  rw [←gaussianBlockSplit_norm_sq,Real.sqrt_sq (norm_nonneg x)]
  apply Prod.ext <;> ext i <;> rfl

lemma sphereBlock_gaussian_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map (fun u => gaussianBlockSplit (n+1) L u.val)=
      ((stdGaussian (Spin (n+1))).prod (stdGaussian (Spin L))).map (cavityBlockNormalize (n+1) L) := by
  have hd : (stdGaussian (Spin (n+1+L))).map (fun x => ‖x‖⁻¹ •x)=
      (unitSphereLaw (n+1+L)).map Subtype.val := by
    have he : n+1+L=(n+L)+1 := by omega
    rw [he]
    exact stdGaussian_direction_law (n+L)
  have h := congrArg (fun μ : Measure (Spin (n+1+L)) => μ.map (gaussianBlockSplit (n+1) L)) hd
  rw [Measure.map_map (gaussianBlockSplit_measurable _ _) (by fun_prop),
    Measure.map_map (gaussianBlockSplit_measurable _ _) measurable_subtype_coe] at h
  simp only [Function.comp_def] at h
  rw [←h,←(gaussianBlockSplit_preserving (n+1) L).map_eq,
    Measure.map_map (cavityBlockNormalize_measurable _ _) (gaussianBlockSplit_measurable _ _)]
  congr 1
  funext x
  exact gaussianBlockSplit_normalize (n+1) L x

def cavityRadialBlock (n L : ℕ) (p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L) : Spin (n+1)×Spin L :=
  let a := (Real.sqrt (p.1.1.val^2+‖p.2‖^2))⁻¹
  ((a*p.1.1.val) •p.1.2.val,a •p.2)

lemma cavityRadialBlock_measurable (n L : ℕ) : Measurable (cavityRadialBlock n L) := by
  unfold cavityRadialBlock
  fun_prop

lemma cavityRadialBlock_eq (n L : ℕ) (p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L) :
    cavityRadialBlock n L p=cavityBlockNormalize (n+1) L (p.1.1.val •p.1.2.val,p.2) := by
  have hn : ‖p.1.2.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.1.2.prop
  simp only [cavityRadialBlock,cavityBlockNormalize,norm_smul,Real.norm_eq_abs,
    abs_of_pos (show (0:ℝ)<p.1.1.val from p.1.1.prop),hn,mul_one,smul_smul]

theorem sphereBlock_radial_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map (fun u => gaussianBlockSplit (n+1) L u.val)=
      (((gaussianRadiusLaw n).prod (unitSphereLaw (n+1))).prod (stdGaussian (Spin L))).map
        (cavityRadialBlock n L) := by
  rw [sphereBlock_gaussian_law]
  have hp := (stdGaussian_radial_preserving n).prod (MeasurePreserving.id (stdGaussian (Spin L)))
  rw [←hp.map_eq,Measure.map_map (cavityBlockNormalize_measurable _ _) hp.measurable]
  congr 1
  funext p
  exact (cavityRadialBlock_eq n L p).symm

lemma countableGaussian_eval_preserving (i : ℕ) :
    MeasurePreserving (fun g : ℕ→ℝ=>g i) countableGaussianLaw (gaussianReal 0 1) :=
  ⟨measurable_pi_apply i,Measure.infinitePi_map_eval _ i⟩

lemma countableGaussian_square_strongLaw :
    ∀ᵐ g ∂countableGaussianLaw,
      Tendsto (fun n : ℕ=>(∑ i∈Finset.range n,(g i)^2)/(n:ℝ)) atTop (𝓝 1) := by
  have hi (i : ℕ) : IdentDistrib (fun g : ℕ→ℝ=>g i) (fun x : ℝ=>x)
      countableGaussianLaw (gaussianReal 0 1) :=
    ⟨(measurable_pi_apply i).aemeasurable,measurable_id.aemeasurable,by
      change Measure.map _ _ = Measure.map id _
      rw [Measure.map_id]; exact (countableGaussian_eval_preserving i).map_eq⟩
  have hint : Integrable (fun g : ℕ→ℝ=>(g 0)^2) countableGaussianLaw :=
    ((gaussian_square_memLp_two 1).comp_measurePreserving
      (countableGaussian_eval_preserving 0)).integrable (by norm_num)
  have hind := iIndepFun_infinitePi (P:=fun _ : ℕ=>gaussianReal 0 1)
    (X:=fun _ : ℕ=>fun x : ℝ=>x^2) (fun _=>by fun_prop)
  have h := strong_law_ae_real (fun i (g : ℕ→ℝ)=>(g i)^2) hint
    (fun i j hij=>hind.indepFun hij) (fun i=>(hi i).sq.trans (hi 0).sq.symm)
  have hm : (∫ g,(g 0)^2 ∂countableGaussianLaw)=1 := by
    rw [(hi 0).sq.integral_eq,gaussian_square_mean]; rfl
  rwa [hm] at h

def cavityCoupledScale (n L : ℕ) (g : ℕ→ℝ) (z : Spin L) : ℝ :=
  Real.sqrt ((n+1+L:ℕ):ℝ) / Real.sqrt ((∑ i∈Finset.range (n+1),(g i)^2)+‖z‖^2)

lemma cavityCoupledScale_measurable (n L : ℕ) :
    Measurable (Function.uncurry (cavityCoupledScale n L)) := by
  unfold cavityCoupledScale Function.uncurry
  fun_prop

lemma cavityCoupledScale_tendsto (L : ℕ) (g : ℕ→ℝ) (z : Spin L)
    (hg : Tendsto (fun n : ℕ=>(∑ i∈Finset.range n,(g i)^2)/(n:ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n=>cavityCoupledScale n L g z) atTop (𝓝 1) := by
  have hs := hg.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun n : ℕ=> (n+1:ℕ)⁻¹ : ℕ→ℝ) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hnum : Tendsto (fun n : ℕ=> ((n+1+L:ℕ):ℝ)/(n+1:ℕ)) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x:=(1:ℝ))).add (hi.const_mul (L:ℝ))
    convert ht using 1
    · funext n
      push_cast
      field_simp
    · simp
  have hden : Tendsto (fun n : ℕ=> ((∑ i∈Finset.range (n+1),(g i)^2)+‖z‖^2)/(n+1:ℕ)) atTop (𝓝 1) := by
    simpa only [Function.comp_apply,div_eq_mul_inv,add_mul,mul_zero,add_zero] using hs.add (hi.const_mul (‖z‖^2))
  have ht := hnum.sqrt.div hden.sqrt (by norm_num : Real.sqrt (1:ℝ)≠0)
  simp only [Real.sqrt_one,div_one] at ht
  apply ht.congr'
  filter_upwards [] with n
  change Real.sqrt (_/_)/Real.sqrt (_/_) = _
  unfold cavityCoupledScale
  rw [Real.sqrt_div (by positivity),Real.sqrt_div (by positivity)]
  have hn : Real.sqrt ((n+1:ℕ):ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

end SphericalPerceptronFreeEnergy
end

end OAI
