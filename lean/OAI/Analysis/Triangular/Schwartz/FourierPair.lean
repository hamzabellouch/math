import OAI.Analysis.Triangular.Schwartz.InputCLM
import OAI.Analysis.Triangular.Schwartz.FourierCLM
import OAI.Analysis.Triangular.Schwartz.Realness

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma h_pos : 0 < h := by norm_num [h]
lemma H_pos : 0 < H := by norm_num [H]

def transformedInput (a : InputCoefficients) (s : ℂ) : ℂ :=
  tailSpectral a (transformedFunction h h h_pos s) +
    finiteSpectral a (transformedFunction H h H_pos s)
def outputComplex (a : InputCoefficients) (x : Plane) : ℂ :=
  exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*transformedInput a (radial x)
lemma integrable_spectral (S : C(Spectrum,ℂ) →L[ℂ] ℂ) {k : ℝ} (hk : 0 < k) :
    Integrable (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) := by
  have hh := S.integrable_comp (integrable_atomFunction hk)
  simpa only [atomFunction,map_smul,smul_eq_mul,Function.comp_def] using hh
lemma inputComplex_spectral (a : InputCoefficients) (x : Plane) : inputComplex a x =
    exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailSpectral a (phaseFunction (radial x:ℂ)) +
    exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteSpectral a (phaseFunction (radial x:ℂ)) := by
  rw [tailSpectral_phase,finiteSpectral_phase]
  rfl
lemma fourier_inputComplex (a : InputCoefficients) : 𝓕 (inputComplex a) = outputComplex a := by
  ext w
  simp only [Real.fourier_eq,inputComplex_spectral,smul_add]
  rw [integral_add ((Real.fourierIntegral_convergent_iff w).mpr (integrable_spectral (tailSpectral a) h_pos))
    ((Real.fourierIntegral_convergent_iff w).mpr (integrable_spectral (finiteSpectral a) H_pos))]
  change 𝓕 (fun x => exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailSpectral a (phaseFunction (radial x:ℂ))) w +
    𝓕 (fun x => exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteSpectral a (phaseFunction (radial x:ℂ))) w = _
  rw [fourier_spectral _ h_pos h,fourier_spectral _ H_pos h]
  simp only [outputComplex,transformedInput,mul_add]

lemma coe_complexInputSchwartz (a : InputCoefficients) :
    (complexInputSchwartz a : Plane → ℂ) = inputComplex a := funext (complexInputSchwartz_apply a)
lemma coe_fourier_input (a : InputCoefficients) :
    ((𝓕 (complexInputSchwartz a) : 𝓢(Plane,ℂ)) : Plane → ℂ) = outputComplex a := by
  rw [SchwartzMap.fourier_coe,coe_complexInputSchwartz,fourier_inputComplex]
lemma outputComplex_real (a : InputCoefficients) (x : Plane) : conj (outputComplex a x) = outputComplex a x := by
  rw [← fourier_inputComplex]
  exact fourier_conj_even _ (inputComplex_real a) (inputComplex_even a) x
lemma inputComplex_radial (a : InputCoefficients) (x y : Plane) (hxy : ‖x‖=‖y‖) : inputComplex a x = inputComplex a y := by
  simp only [inputComplex,radial,hxy]
lemma outputComplex_radial (a : InputCoefficients) (x y : Plane) (hxy : ‖x‖=‖y‖) : outputComplex a x = outputComplex a y := by
  simp only [outputComplex,radial,hxy]
lemma fourier_outputComplex (a : InputCoefficients) : 𝓕 (outputComplex a) = inputComplex a := by
  have hh := (complexInputSchwartz a).continuous.fourierInv_fourier_eq
    (complexInputSchwartz a).integrable (𝓕 (complexInputSchwartz a)).integrable
  rw [coe_complexInputSchwartz,fourier_inputComplex,Real.fourierInv_eq_fourier_comp_neg] at hh
  have he : (fun x => outputComplex a (-x)) = outputComplex a := by
    ext x
    exact outputComplex_radial a (-x) x (norm_neg x)
  rwa [he] at hh

def pairComplex (a₁ a₂ : InputCoefficients) : Plane → ℂ := inputComplex a₁ + outputComplex a₂
def pairSchwartz (a₁ a₂ : InputCoefficients) : 𝓢(Plane,ℝ) :=
  (complexInputSchwartz a₁ + 𝓕 (complexInputSchwartz a₂)).postcompCLM Complex.reCLM
lemma pairSchwartz_apply (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairSchwartz a₁ a₂ x = (pairComplex a₁ a₂ x).re := by
  simp only [pairSchwartz,SchwartzMap.postcompCLM_apply,Complex.reCLM_apply,add_apply,
    coe_fourier_input,complexInputSchwartz_apply,pairComplex,Pi.add_apply]
lemma pairComplex_real (a₁ a₂ : InputCoefficients) (x : Plane) : conj (pairComplex a₁ a₂ x) = pairComplex a₁ a₂ x := by
  simp only [pairComplex,Pi.add_apply,map_add,inputComplex_real,outputComplex_real]
lemma pairComplex_eq (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairComplex a₁ a₂ x = (pairSchwartz a₁ a₂ x:ℂ) := by
  rw [pairSchwartz_apply]
  exact (Complex.conj_eq_iff_re.mp (pairComplex_real a₁ a₂ x)).symm
lemma fourier_pairComplex (a₁ a₂ : InputCoefficients) : 𝓕 (pairComplex a₁ a₂) = pairComplex a₂ a₁ := by
  have hi : Integrable (inputComplex a₁) := by
    rw [← coe_complexInputSchwartz]
    exact (complexInputSchwartz a₁).integrable
  have ho : Integrable (outputComplex a₂) := by
    rw [← coe_fourier_input]
    exact (𝓕 (complexInputSchwartz a₂)).integrable
  ext w
  simp only [pairComplex,Pi.add_apply,Real.fourier_eq,smul_add]
  rw [integral_add ((Real.fourierIntegral_convergent_iff w).mpr hi)
    ((Real.fourierIntegral_convergent_iff w).mpr ho)]
  change 𝓕 (inputComplex a₁) w + 𝓕 (outputComplex a₂) w = _
  rw [fourier_inputComplex,fourier_outputComplex]
  exact add_comm _ _
lemma pairSchwartz_radial (a₁ a₂ : InputCoefficients) : Radial (pairSchwartz a₁ a₂) := by
  intro x y hxy
  simp only [pairSchwartz_apply,pairComplex,Pi.add_apply,inputComplex_radial a₁ x y hxy,
    outputComplex_radial a₂ x y hxy]
lemma pairSchwartz_fourier (a₁ a₂ : InputCoefficients) (w : Plane) :
    realFourier (pairSchwartz a₁ a₂) w = (pairSchwartz a₂ a₁ w:ℂ) := by
  simp only [realFourier,← pairComplex_eq]
  rw [fourier_pairComplex,pairComplex_eq]
end AtomicTriangular.Construction
end

end OAI
