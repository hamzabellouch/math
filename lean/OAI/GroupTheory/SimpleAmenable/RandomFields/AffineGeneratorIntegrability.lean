import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AffineIntegrability
import OAI.GroupTheory.SimpleAmenable.RandomFields.NoiseContinuity

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AffineGeneratorIntegrability
open Classical MeasureTheory Matrix

theorem affineNoiseGenerator_integrable_square {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (L : Matrix ι ι ℝ) (v : ι → ℝ) :
    Integrable (fun x : ι → ℝ => affineNoiseGenerator f L v x^2) := by
  let a : (ι → ℝ) → ℝ := fun x => ∑i,L i i*singletonNoise f .diagonal i x
  let b : (ι → ℝ) → ℝ := fun x => ∑i,v i*singletonNoise f .score i x
  let c : (ι → ℝ) → ℝ := fun x => ∑p : NoisePair ι,L p.val.1 p.val.2*pairNoise f p x
  have h : ∀u∈({a,b,c} : Finset ((ι → ℝ) → ℝ)),
      ∀w∈({a,b,c} : Finset ((ι → ℝ) → ℝ)),Integrable (fun x => u x*w x)
        (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
    intro u hu w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hw
    rcases hu with rfl|rfl|rfl <;> rcases hw with rfl|rfl|rfl <;>
      dsimp only [a,b,c,singletonNoise,pairNoise] <;> apply noise_sum_integrable_product hf hc
  have haa := h a (by simp) a (by simp)
  have hbb := h b (by simp) b (by simp)
  have hcc := h c (by simp) c (by simp)
  have hab := h a (by simp) b (by simp)
  have hac := h a (by simp) c (by simp)
  have hbc := h b (by simp) c (by simp)
  convert! ((((haa.add hbb).add hcc).add (hab.const_mul 2)).add
    ((hac.const_mul 2).add (hbc.const_mul 2))).congr (Filter.Eventually.of_forall (fun x => ?_)) using 1
  change a x*a x+b x*b x+c x*c x+2*(a x*b x)+(2*(a x*c x)+2*(b x*c x))=
    (a x+b x+c x)^2
  ring

theorem affineNoiseRootDerivative_integrable_square {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (A L : Matrix ι ι ℝ) (a v : ι → ℝ) (hA : IsUnit A.det) :
    Integrable (fun y => (-affineNoiseGenerator f L v (A⁻¹*ᵥ(y-a))/Real.sqrt A.det)^2) := by
  simpa only [div_pow,neg_sq] using
    (integrable_matrix_affine_inverse A a hA (affineNoiseGenerator_integrable_square hf hc L v)).div_const
      ((Real.sqrt A.det)^2)

end AffineGeneratorIntegrability

section NoiseInterpolation
open Classical Matrix MeasureTheory Set
open scoped Matrix.Norms.Elementwise

noncomputable def noiseInterpolationRoot {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (B C : Matrix ι ι ℝ) (a h : ι → ℝ) (t : ℝ) : (ι → ℝ) → ℝ :=
  affineNoiseRoot f (1+covarianceSegment B C t) (a+t • h)

noncomputable def noiseInterpolationDerivative {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (B C : Matrix ι ι ℝ) (a h : ι → ℝ) (t : ℝ) (y : ι → ℝ) : ℝ :=
  let T := 1+covarianceSegment B C t;
  -affineNoiseGenerator f (T⁻¹*(C-B)) (T⁻¹*ᵥh) (T⁻¹*ᵥ(y-(a+t • h)))/Real.sqrt T.det

theorem covarianceSegment_hasDerivAt {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (t : ℝ) :
    HasDerivAt (fun s => 1+covarianceSegment B C s) (C-B) t := by
  simp_rw [covarianceSegment_affine]
  convert! (hasDerivAt_const t (1+B)).add ((hasDerivAt_id t).smul_const (C-B)) using 1
  simp

theorem noiseInterpolation_hasDerivAt {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (B C : Matrix ι ι ℝ)
    (hB : B.PosSemidef) (hC : C.PosSemidef) (a h y : ι → ℝ)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    HasDerivAt (fun s => noiseInterpolationRoot f B C a h s y)
      (noiseInterpolationDerivative f B C a h t y) t := by
  have hp := (Matrix.PosDef.one.add_posSemidef (covarianceSegment_posSemidef B C hB hC ht)).det_pos
  exact affineNoiseRoot_hasDerivAt (hf.differentiable (by norm_num))
    (covarianceSegment_hasDerivAt B C t)
    (by convert! (hasDerivAt_const t a).add ((hasDerivAt_id t).smul_const h) using 1
        simp) hp y

local instance {ι : Type*} : MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))
local instance {ι : Type*} [Fintype ι] : BorelSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (BorelSpace (ι → ι → ℝ))

theorem noiseInterpolationDerivative_measurable {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (B C : Matrix ι ι ℝ) (a h : ι → ℝ) :
    Measurable (Function.uncurry (noiseInterpolationDerivative f B C a h)) := by
  let T : (ℝ×(ι → ℝ)) → Matrix ι ι ℝ := fun p => 1+covarianceSegment B C p.1
  have hT : Continuous T := by unfold T covarianceSegment; fun_prop
  have hi := matrix_inverse_measurable hT.measurable
  have hg : Continuous (fun p : (Matrix ι ι ℝ)×(ι → ℝ)×(ι → ℝ) =>
      affineNoiseGenerator f p.1 p.2.1 p.2.2) :=
    affineNoiseGenerator_continuous_comp hf continuous_fst
      continuous_snd.fst continuous_snd.snd
  have hx : Measurable (fun p : ℝ×(ι → ℝ) => p.2-(a+p.1 • h)) := by fun_prop
  have hij (i j : ι) : Measurable (fun p => (T p)⁻¹ i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hi)
  have hL : Measurable (fun p => (T p)⁻¹*(C-B)) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ (fun k _ => (hij i k).mul_const _)
  have hv : Measurable (fun p => (T p)⁻¹*ᵥh) := by
    apply Measurable.of_eval
    intro i
    simp only [Matrix.mulVec,dotProduct]
    exact Finset.measurable_sum _ (fun k _ => (hij i k).mul_const _)
  have hxx : Measurable (fun p => (T p)⁻¹*ᵥ(p.2-(a+p.1 • h))) := by
    apply Measurable.of_eval
    intro i
    simp only [Matrix.mulVec,dotProduct]
    exact Finset.measurable_sum _ (fun k _ => (hij i k).mul ((measurable_pi_apply k).comp hx))
  exact (hg.measurable.comp (hL.prodMk (hv.prodMk hxx))).neg.div
    (hT.matrix_det.measurable.sqrt)

theorem noiseInterpolationDerivative_continuousOn {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (B C : Matrix ι ι ℝ)
    (hB : B.PosSemidef) (hC : C.PosSemidef) (a h y : ι → ℝ) :
    ContinuousOn (fun t => noiseInterpolationDerivative f B C a h t y) (Icc (0:ℝ) 1) := by
  intro t ht
  let T : ℝ → Matrix ι ι ℝ := fun s => 1+covarianceSegment B C s
  have hT : Continuous T := by unfold T covarianceSegment; fun_prop
  have hp : 0<(T t).det :=
    (Matrix.PosDef.one.add_posSemidef (covarianceSegment_posSemidef B C hB hC ht)).det_pos
  have hi := matrix_inverse_continuousAt hT.continuousAt hp.ne'
  have hg : Continuous (fun p : (Matrix ι ι ℝ)×(ι → ℝ)×(ι → ℝ) =>
      affineNoiseGenerator f p.1 p.2.1 p.2.2) :=
    affineNoiseGenerator_continuous_comp hf continuous_fst
      continuous_snd.fst continuous_snd.snd
  have hL : ContinuousAt (fun s => (T s)⁻¹*(C-B)) t := by fun_prop
  have hv : ContinuousAt (fun s => (T s)⁻¹*ᵥh) t := by
    fun_prop
  have hx : ContinuousAt (fun s => (T s)⁻¹*ᵥ(y-(a+s • h))) t := by
    fun_prop
  exact ((hg.continuousAt.comp (hL.prodMk (hv.prodMk hx))).neg.div
    hT.matrix_det.continuousAt.sqrt (Real.sqrt_ne_zero'.mpr hp)).continuousWithinAt

theorem noiseInterpolationDerivative_energy {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hn : (∫x : ℝ,f x^2)=1) (he : Function.Even f)
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef) (a h : ι → ℝ)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (∫y : ι → ℝ,noiseInterpolationDerivative f B C a h t y^2)≤
      affineNoiseEnergyConstant f*(matrixHSNorm (C-B)^2+
        ((1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh))^2) := by
  let P := covarianceSegment B C t
  have hP := covarianceSegment_posSemidef B C hB hC ht
  have hp := (Matrix.PosDef.one.add_posSemidef hP).det_pos
  have hd : (∫y : ι → ℝ,noiseInterpolationDerivative f B C a h t y^2)≤
      affineNoiseEnergyConstant f*(matrixHSNorm ((1+P)⁻¹*(C-B))^2+
        finiteL2Norm ((1+P)⁻¹*ᵥh)^2) := by
    simp only [noiseInterpolationDerivative,div_pow,neg_sq,Real.sq_sqrt hp.le]
    rw [integral_div,integral_matrix_affine_inverse (1+covarianceSegment B C t) (a+t • h)
      (isUnit_iff_ne_zero.mpr hp.ne')
      (fun x => affineNoiseGenerator f ((1+covarianceSegment B C t)⁻¹*(C-B))
        ((1+covarianceSegment B C t)⁻¹*ᵥh) x^2),abs_of_pos hp,mul_div_cancel_left₀ _ hp.ne']
    rw [matrixHSNorm_sq,finiteL2Norm_sq]
    convert! affineNoiseGenerator_energy hf hc he hn ((1+P)⁻¹*(C-B)) ((1+P)⁻¹*ᵥh) using 1
  apply hd.trans
  apply mul_le_mul_of_nonneg_left _ (affineNoiseEnergyConstant_nonneg f)
  exact add_le_add
    (pow_le_pow_left₀ (matrixHSNorm_nonneg _) (matrixHSNorm_inverse_contraction P (C-B) hP) 2)
    (pow_le_pow_left₀ (finiteL2Norm_nonneg _) (covarianceSegment_inverse_signal B C hB hC h ht) 2)

end NoiseInterpolation

end SimpleAmenable
end
end

end OAI
