import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyMomentLevels

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def hierarchyPressure : (n : ℕ) → (Fin n → ℝ) → (ParameterSpace n → ℝ) → ℝ → ℝ
  | 0,_,f => f
  | n+1,m,f => hierarchyPressure n (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) f)

theorem hierarchyPressure_boundedDerivs (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) :
    BoundedDerivs (hierarchyPressure n m f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih _ _ (hf.gaussianStep _)

theorem hierarchyPathWeight_const (n : ℕ) (p : ℝ) (f : ParameterSpace n → ℝ)
    (z : ParameterSpace n) :
    hierarchyPathWeight n (fun _ => p) f z =
      Real.exp (p*(f z-hierarchyPressure n (fun _ => p) f (parameter n z))) := by
  induction n with
  | zero => simp [hierarchyPathWeight,hierarchyPressure,parameter]
  | succ n ih =>
    rw [hierarchyPathWeight,ih,← Real.exp_add]
    apply congrArg Real.exp
    change p*(f z-gaussianStep p f z.1)+p*(gaussianStep p f z.1-
      hierarchyPressure n (fun _ => p) (gaussianStep p f) (parameter n z.1)) = _
    change _ = p*(f z-hierarchyPressure n (fun _ => p) (gaussianStep p f) (parameter n z.1))
    ring

theorem parameter_ae_fiberGaussian (n : ℕ) (x : ℝ) :
    ∀ᵐ z ∂fiberGaussian n x, parameter n z = x := by
  induction n with
  | zero => simp [fiberGaussian,parameter]
  | succ n ih =>
    change ∀ᵐ z ∂(fiberGaussian n x).prod (gaussianReal 0 1), parameter n z.1 = x
    exact Measure.quasiMeasurePreserving_fst.ae ih

theorem hierarchyPathLaw_const (n : ℕ) (p : ℝ) (f : ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (x : ℝ) :
    hierarchyPathLaw n (fun _ => p) f x = (fiberGaussian n x).tilted (fun z => p*f z) := by
  let A := hierarchyPressure n (fun _ => p) f x
  have hweight : hierarchyPathWeight n (fun _ => p) f =ᵐ[fiberGaussian n x]
      (fun z => Real.exp (p*f z)/Real.exp (p*A)) := by
    filter_upwards [parameter_ae_fiberGaussian n x] with z hz
    rw [hierarchyPathWeight_const,hz,mul_sub,Real.exp_sub]
  have hZ : (∫ z, Real.exp (p*f z) ∂fiberGaussian n x) = Real.exp (p*A) := by
    have hn := (hierarchyPathWeight_normalized n (fun _ => p) f hf x).2
    rw [integral_congr_ae hweight,integral_div] at hn
    exact (div_eq_one_iff_eq (Real.exp_ne_zero _)).mp hn
  rw [hierarchyPathLaw,Measure.tilted,hZ]
  apply withDensity_congr_ae
  exact hweight.fun_comp ENNReal.ofReal

end SK.Analytic
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def parameterAppend : (a b : ℕ) → CascadeSpace (ParameterSpace a) b ≃L[ℝ] ParameterSpace (a+b)
  | a,0 => ContinuousLinearEquiv.refl ℝ (ParameterSpace a)
  | a,b+1 => (parameterAppend a b).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

@[simp] theorem parameterAppend_zero (a : ℕ) (x : ParameterSpace a) : parameterAppend a 0 x = x := rfl
@[simp] theorem parameterAppend_succ (a b : ℕ) (x : CascadeSpace (ParameterSpace a) b) (y : ℝ) :
    parameterAppend a (b+1) (x,y) = (parameterAppend a b x,y) := rfl

theorem gaussianStep_append (a b : ℕ) (p : ℝ) (f : ParameterSpace (a+(b+1)) → ℝ) :
    gaussianStep p (fun z => f (parameterAppend a (b+1) z)) =
      fun z => gaussianStep p f (parameterAppend a b z) := by
  rfl

theorem hierarchyPressure_split (a b : ℕ) (m : Fin (a+b) → ℝ)
    (f : ParameterSpace (a+b) → ℝ) :
    hierarchyPressure (a+b) m f = hierarchyPressure a (fun i => m (Fin.castAdd b i))
      (cascadePressure b (fun i => m (Fin.natAdd a i)) (fun z => f (parameterAppend a b z))) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change hierarchyPressure ((a+b)+1) m f = _
    rw [hierarchyPressure,ih,cascadePressure,gaussianStep_append]
    rfl

section CascadeRoot
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cascadeRoot : (b : ℕ) → CascadeSpace E b →L[ℝ] E
  | 0 => ContinuousLinearMap.id ℝ E
  | b+1 => (cascadeRoot b).comp (ContinuousLinearMap.fst ℝ (CascadeSpace E b) ℝ)
end CascadeRoot

theorem gaussianAverage_append (a b : ℕ) (p : ℝ) (f g : ParameterSpace (a+(b+1)) → ℝ) :
    gaussianAverage p (fun z => f (parameterAppend a (b+1) z)) (fun z => g (parameterAppend a (b+1) z)) =
      fun z => gaussianAverage p f g (parameterAppend a b z) := rfl

theorem hierarchyMomentLevel_last (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) : hierarchyMomentLevel n m f g (Fin.last n) = g := by
  cases n with
  | zero => rfl
  | succ n => simp only [hierarchyMomentLevel,Fin.lastCases_last]

theorem hierarchyLevel_last (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) : hierarchyLevel n m f (Fin.last n) = f := by
  cases n with
  | zero => rfl
  | succ n => simp only [hierarchyLevel,Fin.lastCases_last]

theorem hierarchyMomentLevel_split (a b : ℕ) (m : Fin (a+b) → ℝ)
    (f g : ParameterSpace (a+b) → ℝ) (z : CascadeSpace (ParameterSpace a) b) :
    hierarchyMomentLevel (a+b) m f g ⟨a,by omega⟩ (parameterAppend a b z) =
      cascadeMoment b (fun i => m (Fin.natAdd a i)) (fun z => f (parameterAppend a b z))
        (fun z => g (parameterAppend a b z)) (cascadeRoot (E := ParameterSpace a) b z) := by
  induction b with
  | zero =>
    change hierarchyMomentLevel a m f g (Fin.last a) z = g z
    rw [hierarchyMomentLevel_last]
  | succ b ih =>
    change hierarchyMomentLevel ((a+b)+1) m f g (Fin.castSucc ⟨a,by omega⟩)
      (parameterAppend a b z.1,z.2) = _
    rw [hierarchyMomentLevel,Fin.lastCases_castSucc,ih]
    rw [cascadeMoment,gaussianStep_append,gaussianAverage_append]
    rfl

theorem hierarchyLevel_split (a b : ℕ) (m : Fin (a+b) → ℝ)
    (f : ParameterSpace (a+b) → ℝ) (z : CascadeSpace (ParameterSpace a) b) :
    hierarchyLevel (a+b) m f ⟨a,by omega⟩ (parameterAppend a b z) =
      cascadePressure b (fun i => m (Fin.natAdd a i)) (fun z => f (parameterAppend a b z))
        (cascadeRoot (E := ParameterSpace a) b z) := by
  induction b with
  | zero =>
    change hierarchyLevel a m f (Fin.last a) z = f z
    rw [hierarchyLevel_last]
  | succ b ih =>
    change hierarchyLevel ((a+b)+1) m f (Fin.castSucc ⟨a,by omega⟩)
      (parameterAppend a b z.1,z.2) = _
    rw [hierarchyLevel,Fin.lastCases_castSucc,ih]
    rw [cascadePressure,gaussianStep_append]
    rfl

end SK.Analytic
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Translate
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BoundedDerivs.translate {f : E → ℝ} (hf : BoundedDerivs f) (a : E) :
    BoundedDerivs (fun z => f (a+z)) := by
  obtain ⟨hf,C,D,hC,hD,h₁,h₂⟩ := hf
  have hd := hf.differentiable (by norm_num)
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have he : fderiv ℝ (fun z => f (a+z)) = fun z => fderiv ℝ f (a+z) := by
    funext z
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def] using
      ((hd (a+z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_add a)).fderiv
  refine ⟨hf.comp (contDiff_const.add contDiff_id),C,D,hC,hD,?_,?_⟩
  · intro z; rw [he]; exact h₁ _
  · intro z
    rw [he]
    have H := ((hdd (a+z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_add a)).fderiv
    simp only [ContinuousLinearMap.comp_id,Function.comp_def] at H
    rw [H]
    exact h₂ _

def parameterEmbed : (b : ℕ) → E → ParameterSpace b → CascadeSpace E b
  | 0,x,_ => x
  | b+1,x,z => (parameterEmbed b x z.1,z.2)

def parameterNoise : (b : ℕ) → ParameterSpace b →L[ℝ] CascadeSpace E b
  | 0 => 0
  | b+1 => (parameterNoise b).prodMap (ContinuousLinearMap.id ℝ ℝ)

theorem parameterEmbed_eq (b : ℕ) (x : E) (z : ParameterSpace b) :
    parameterEmbed b x z = cascadeLift b x+parameterNoise (E := E) b z := by
  induction b with
  | zero => simp only [parameterEmbed,cascadeLift,parameterNoise,_root_.zero_apply,add_zero]
  | succ b ih =>
    change (parameterEmbed b x z.1,z.2) = (cascadeLift b x+parameterNoise (E := E) b z.1,0+z.2)
    rw [ih,zero_add]

theorem BoundedDerivs.parameterEmbed {b : ℕ} {f : CascadeSpace E b → ℝ}
    (hf : BoundedDerivs f) (x : E) : BoundedDerivs (fun z => f (parameterEmbed b x z)) := by
  simpa only [parameterEmbed_eq] using (hf.translate (cascadeLift b x)).compCLM (parameterNoise (E := E) b)

theorem parameterEmbed_continuous (b : ℕ) (x : E) : Continuous (parameterEmbed b x) := by
  have he : parameterEmbed b x = fun z => cascadeLift b x+parameterNoise (E := E) b z := funext (parameterEmbed_eq b x)
  rw [he]
  exact continuous_const.add (parameterNoise (E := E) b).continuous

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianStep_parameterEmbed (b : ℕ) (p : ℝ) (f : CascadeSpace E (b+1) → ℝ) (x : E) :
    gaussianStep p (fun z => f (parameterEmbed (b+1) x z)) =
      fun z => gaussianStep p f (parameterEmbed b x z) := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianAverage_parameterEmbed (b : ℕ) (p : ℝ) (f g : CascadeSpace E (b+1) → ℝ) (x : E) :
    gaussianAverage p (fun z => f (parameterEmbed (b+1) x z)) (fun z => g (parameterEmbed (b+1) x z)) =
      fun z => gaussianAverage p f g (parameterEmbed b x z) := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem cascadeMoment_parameterEmbed (b : ℕ) (m : Fin b → ℝ)
    (f g : CascadeSpace E b → ℝ) (x : E) (y : ℝ) :
    cascadeMoment b m f g x = hierarchyAverage b m (fun z => f (parameterEmbed b x z))
      (fun z => g (parameterEmbed b x z)) y := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [cascadeMoment,ih,hierarchyAverage,gaussianStep_parameterEmbed,gaussianAverage_parameterEmbed]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem cascadePressure_parameterEmbed (b : ℕ) (m : Fin b → ℝ)
    (f : CascadeSpace E b → ℝ) (x : E) (y : ℝ) :
    cascadePressure b m f x = hierarchyPressure b m (fun z => f (parameterEmbed b x z)) y := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [cascadePressure,ih,hierarchyPressure,gaussianStep_parameterEmbed]

theorem cascadeMoment_const_integral (b : ℕ) (p : ℝ) (f g : CascadeSpace E b → ℝ)
    (hf : BoundedDerivs f) (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C) (x : E) :
    cascadeMoment b (fun _ => p) f g x =
      ∫ z, g (parameterEmbed b x z) ∂(fiberGaussian b 0).tilted (fun z => p*f (parameterEmbed b x z)) := by
  have hg' : Continuous (fun z => g (parameterEmbed b x z)) := by
    simpa only [Function.comp_def] using hg.comp (parameterEmbed_continuous b x)
  rw [cascadeMoment_parameterEmbed b (fun _ => p) f g x 0]
  rw [hierarchyAverage_eq_integral b (fun _ => p) (fun z => f (parameterEmbed b x z))
    (hf.parameterEmbed x) (fun z => g (parameterEmbed b x z)) hg' hC (fun z => hb _) 0]
  rw [hierarchyPathLaw_const b p _ (hf.parameterEmbed x) 0]
end Translate
end SK.Analytic

end
end

end

end OAI
