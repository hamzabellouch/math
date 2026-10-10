import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! The scalar spectral measure of a vector in a representation of C(X). -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
namespace KadisonSimilarity.VectorSpectralMeasure
variable {X H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
def realCM (f : C(X,ℝ)) : C(X,ℂ) := ⟨fun x => (f x : ℂ),by fun_prop⟩
@[simp] lemma realCM_apply (f : C(X,ℝ)) (x : X) : realCM f x = (f x : ℂ) := rfl
@[simp] lemma realCM_add (f g : C(X,ℝ)) : realCM (f+g) = realCM f+realCM g := by ext; simp
@[simp] lemma realCM_sub (f g : C(X,ℝ)) : realCM (f-g) = realCM f-realCM g := by ext; simp
@[simp] lemma realCM_smul (c : ℝ) (f : C(X,ℝ)) : realCM (c • f) = (c:ℂ) • realCM f := by ext; simp
@[simp] lemma realCM_one : realCM (1:C(X,ℝ)) = 1 := by ext; simp
variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma real_nonneg (f : C(X,ℝ)) (hf : 0 ≤ f) : 0 ≤ (⟪v, Φ (realCM f) v⟫_ℂ).re := by
  let g : C(X,ℂ) := realCM ⟨fun x => Real.sqrt (f x),by fun_prop⟩
  have he : star g * g = realCM f := by
    ext x
    simp only [ContinuousMap.mul_apply,ContinuousMap.star_apply,realCM_apply,g,ContinuousMap.coe_mk,Complex.star_def,Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    exact congrArg Complex.ofReal (Real.mul_self_sqrt (show 0 ≤ f x from hf x))
  rw [← he,map_mul,map_star]
  change 0 ≤ (⟪v, (star (Φ g)) ((Φ g) v)⟫_ℂ).re
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (x := (Φ g) v)

def functional : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := (⟪v,Φ (realCM f.toContinuousMap) v⟫_ℂ).re
  map_add' f g := by
    change (⟪v,Φ (realCM (f.toContinuousMap+g.toContinuousMap)) v⟫_ℂ).re = _
    simp [inner_add_right]
  map_smul' c f := by
    change (⟪v,Φ (realCM (c • f.toContinuousMap)) v⟫_ℂ).re = c * _
    rw [realCM_smul,map_smul]
    simp only [FunLike.coe_smul,Pi.smul_apply,inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  monotone' f g hfg := by
    have he := real_nonneg Φ v (g.toContinuousMap-f.toContinuousMap) (sub_nonneg.mpr hfg)
    simpa [inner_sub_right] using he

def measure : Measure X := RealRMK.rieszMeasure (functional Φ v)
instance : IsFiniteMeasure (measure Φ v) := by dsimp [measure]; infer_instance
instance : (measure Φ v).Regular := by dsimp [measure]; infer_instance
lemma integral_real (f : C(X,ℝ)) : ∫ x, f x ∂measure Φ v = (⟪v,Φ (realCM f) v⟫_ℂ).re := by
  exact RealRMK.integral_rieszMeasure (functional Φ v) (CompactlySupportedContinuousMap.continuousMapEquiv f)
lemma integral_complex (f : C(X,ℂ)) : ∫ x, f x ∂measure Φ v = ⟪v,Φ f v⟫_ℂ := by
  let fr : C(X,ℝ) := ⟨fun x => (f x).re,by fun_prop⟩
  let fi : C(X,ℝ) := ⟨fun x => (f x).im,by fun_prop⟩
  have he : f = realCM fr + Complex.I • realCM fi := by
    ext x
    simpa [fr,fi,smul_eq_mul,mul_comm] using (Complex.re_add_im (f x)).symm
  have hi_real (g : C(X,ℝ)) : (⟪v,Φ (realCM g) v⟫_ℂ).im = 0 := by
    have hs : star (Φ (realCM g)) = Φ (realCM g) := by
      rw [← map_star]; congr 1; ext x; simp
    have ht := inner_conj_symm (𝕜 := ℂ) v (Φ (realCM g) v)
    rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,hs] at ht
    have hh := congrArg Complex.im ht
    simp only [Complex.conj_im] at hh
    linarith
  have hb (g : C(X,ℝ)) : ∫ x, (g x : ℂ) ∂measure Φ v = ⟪v,Φ (realCM g) v⟫_ℂ := by
    rw [integral_complex_ofReal,integral_real]
    exact Complex.ext (by simp) (by simp [hi_real])
  rw [he,map_add,map_smul]
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,realCM_apply,add_apply,
    smul_apply,inner_add_right,inner_smul_right]
  have hir : Integrable (fun x => (fr x : ℂ)) (measure Φ v) :=
    (Complex.continuous_ofReal.comp fr.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hii : Integrable (fun x => (fi x : ℂ)) (measure Φ v) :=
    (Complex.continuous_ofReal.comp fi.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = (∫ x, (fr x : ℂ) ∂measure Φ v) +
        (∫ x, Complex.I • (fi x : ℂ) ∂measure Φ v) := integral_add hir (hii.smul Complex.I)
    _ = _ := by rw [integral_smul,hb,hb]; rfl
lemma measure_univ : (measure Φ v).real Set.univ = ‖v‖^2 := by
  have he := integral_real Φ v (1:C(X,ℝ))
  simp only [ContinuousMap.one_apply,integral_const,smul_eq_mul,mul_one,realCM_one,map_one,one_apply_eq_self] at he
  exact he.trans (inner_self_eq_norm_sq (𝕜 := ℂ) v)
end KadisonSimilarity.VectorSpectralMeasure

end

end OAI
