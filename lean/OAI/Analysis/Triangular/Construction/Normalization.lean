import OAI.Analysis.Triangular.Schwartz.FourierPair
import OAI.Analysis.Triangular.Signs.FarSigns

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma waveFunctionJet_transformed_zero (q : Fin 2) (s : ℂ) :
    waveFunctionJet q 1 0 s=transformedFunction (damping q) h (damping_pos q) s := by
  simp only [waveFunctionJet,waveAmplitudeFunction,wavePhaseFunction,Fin.val_one,Nat.one_ne_zero,↓reduceIte,pow_zero,mul_one,transformedFunction]
lemma inputJJet_transformed_zero (a : InputCoefficients) (s : ℂ) :
    inputJJet a 1 0 s=transformedInput a s := by
  rw [inputJJet,waveFunctionJet_transformed_zero,waveFunctionJet_transformed_zero]
  rfl
lemma inputComplex_radialJ (a : InputCoefficients) (x : Plane) :
    inputComplex a x=exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*inputJJet a 0 0 (radial x) := by
  rw [inputComplex_spectral,inputJJet,waveFunctionJet_zero_phase,waveFunctionJet_direct_zero]
  simp only [map_smul,smul_eq_mul,mul_add,←mul_assoc,damping,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  rw [←exp_add]
  congr 3
  ring
lemma pairComplex_radialJ (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairComplex a₁ a₂ x=exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*pairJJet a₁ a₂ 0 (radial x) := by
  simp only [pairComplex,Pi.add_apply,inputComplex_radialJ,outputComplex,pairJJet,inputJJet_transformed_zero,mul_add]
lemma pairSchwartz_radialJ (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairSchwartz a₁ a₂ x=Real.exp (-Real.pi*h*radial x)*pairJ a₁ a₂ (radial x) := by
  rw [pairSchwartz_apply,pairComplex_radialJ]
  have he : exp (-(Real.pi:ℂ)*h*(radial x:ℂ))=(Real.exp (-Real.pi*h*radial x):ℝ) := by simp
  rw [he,mul_re]
  simp only [ofReal_re,ofReal_im,zero_mul,sub_zero,pairJ]

lemma normalizingDen_pos {z : ℝ} (hz : 0<z) : 0<normalizingDen z := by
  exact mul_pos (mul_pos Q_one_pos hz) (Real.exp_pos _)
def actualSchwartz (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z ≤ Z) : 𝓢(Plane,ℝ) :=
  (normalizingDen z)⁻¹ • pairSchwartz (actualInput side z hz hzB) (actualInput (otherSide side) z hz hzB)
lemma actualSchwartz_apply (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (x : Plane) :
    actualSchwartz side z hz hzB x=Real.exp (-Real.pi*h*radial x)*actualJ side z hz hzB (radial x)/normalizingDen z := by
  simp only [actualSchwartz,smul_apply,smul_eq_mul,pairSchwartz_radialJ,actualJ]
  ring
lemma actualSchwartz_radial (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    Radial (actualSchwartz side z hz hzB) := by
  intro x y hxy
  simp only [actualSchwartz_apply,radial,hxy]
lemma complex_fourier_smul (c : ℂ) (f : Plane → ℂ) : 𝓕 (c • f)=c • 𝓕 f := by
  ext w
  simp only [Real.fourier_eq,Pi.smul_apply,smul_comm _ c,MeasureTheory.integral_smul]
lemma actualSchwartz_fourier_side (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (x : Plane) :
    realFourier (actualSchwartz side z hz hzB) x=(actualSchwartz (otherSide side) z hz hzB x:ℂ) := by
  unfold actualSchwartz
  simp only [realFourier,smul_apply,smul_eq_mul,ofReal_mul]
  change 𝓕 (((((normalizingDen z)⁻¹:ℝ):ℂ)) • (fun x => (pairSchwartz (actualInput side z hz hzB) (actualInput (otherSide side) z hz hzB) x:ℂ))) x=_
  rw [complex_fourier_smul]
  change (((normalizingDen z)⁻¹:ℝ):ℂ)*realFourier (pairSchwartz (actualInput side z hz hzB) (actualInput (otherSide side) z hz hzB)) x=_
  rw [pairSchwartz_fourier]
  fin_cases side <;> rfl
lemma actualSchwartz_fourier {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (x : Plane) :
    realFourier (actualSchwartz 0 z hz hzB) x=(actualSchwartz 1 z hz hzB x:ℂ) :=
  actualSchwartz_fourier_side 0 hz hzB x
lemma radial_nonneg (x : Plane) : 0 ≤ radial x := mul_nonneg b_pos.le (sq_nonneg ‖x‖)
lemma gaussian_normalization {α : ℝ} (hα : 1 ≤ α) (x : Plane) :
    Real.exp (-Real.pi*h*radial x)*gaussianG (gaussianZ α) (radial x)/normalizingDen (gaussianZ α)=
      AtomicTriangular.gaussian α x := by
  have hz := (gaussianZ_bounds hα).1
  have he : (-Real.pi*h*radial x)+(1-radial x)/gaussianZ α-1/gaussianZ α = -Real.pi*α*‖x‖^2 := by
    simp only [gaussianZ,radial]
    field_simp [b_pos.ne']
    ring
  rw [gaussianG,normalizingDen,AtomicTriangular.gaussian]
  have hc : Q 1*gaussianZ α≠0 := mul_ne_zero Q_one_pos.ne' hz.ne'
  calc
    _ = Real.exp (-Real.pi*h*radial x)*Real.exp ((1-radial x)/gaussianZ α)/Real.exp (1/gaussianZ α) := by field_simp [Q_one_pos.ne',hz.ne']
    _ = _ := by rw [←Real.exp_add,←Real.exp_sub,he]
lemma actualSchwartz_signs {α : ℝ} (hα : 1 ≤ α) (x : Plane) :
    actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x ≤ AtomicTriangular.gaussian α x ∧
      0 ≤ actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x := by
  have hj := global_signs (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le (radial_nonneg x)
  rw [actualSchwartz_apply,actualSchwartz_apply,←gaussian_normalization hα x]
  exact ⟨div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hj.1 (Real.exp_pos _).le) (normalizingDen_pos (gaussianZ_bounds hα).1).le,
    div_nonneg (mul_nonneg (Real.exp_pos _).le hj.2) (normalizingDen_pos (gaussianZ_bounds hα).1).le⟩
lemma actualSchwartz_node {α : ℝ} (hα : 1 ≤ α) (x : Plane) (n : Node) (hx : radial x=n.val) :
    actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x = AtomicTriangular.gaussian α x ∧
      actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x=0 := by
  have hj := actual_interpolation (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le n
  rw [actualSchwartz_apply,actualSchwartz_apply,←gaussian_normalization hα x,hx,hj.1,hj.2.2.1]
  simp
end AtomicTriangular.Construction
end

end OAI
