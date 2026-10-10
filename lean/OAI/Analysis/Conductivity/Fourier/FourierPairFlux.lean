import Mathlib
import OAI.Analysis.Conductivity.Fourier.FourierEndConcomitant
import OAI.Analysis.Conductivity.Fourier.FourierEndFlux
import OAI.Analysis.Conductivity.Flux.FlatBackgroundTensor

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma torusCellIntegral_congr_slice {T t : ℝ} {f g : Coord3 → ℝ}
    (h : ∀ x,x 0=t → f x=g x) : torusCellIntegral T f t=torusCellIntegral T g t := by
  apply intervalIntegral.integral_congr
  intro y _
  apply intervalIntegral.integral_congr
  intro z _
  exact h ![t,y,z] rfl

theorem fourier_pair_boundary_flux {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a b pa pb : (Fin 2 → ℤ) → ℝ} {Ba Bb ga gb t : ℝ}
    (ha : ∀ h,|a h|≤Ba) (hb : ∀ h,|b h|≤Bb) (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h) (hrb : ∀ h,b h≠0 → gb≤torusRate s h)
    (α β : ℝ) (ht : 0<t) {u : Coord3 → Fin 2 → ℝ}
    (hu : Differentiable ℝ u)
    (he0 : ∀ x,x 0=t → (fun y => u y 0)=ᶠ[𝓝 x] affineFourierField s a pa α β)
    (he1 : ∀ x,x 0=t → (fun y => u y 1)=ᶠ[𝓝 x] flatFourier s b pb) :
    torusCellIntegral (2*Real.pi)
      (fun x => (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col 0 0) t=(2*Real.pi)^2*α ∧
    torusCellIntegral (2*Real.pi)
      (fun x => (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col 1 0) t=0 ∧
    torusCellIntegral (2*Real.pi) (fun x => symmetricCrossFlux (fun _ => flatBackgroundTensor s) u x 0) t=0 := by
  have hf0 := torusCellIntegral_congr_slice (T:=2*Real.pi)
    (f:=fun x => (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col 0 0)
    (g:=fun x => fderiv ℝ (affineFourierField s a pa α β) x (flatAxis 0))
    (fun x hx => by
      rw [flatBackgroundTensor_flux hu]
      change fderiv ℝ (fun y => u y 0) x (flatAxis 0)=_
      rw [(he0 x hx).fderiv_eq])
  have hf1 := torusCellIntegral_congr_slice (T:=2*Real.pi)
    (f:=fun x => (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col 1 0)
    (g:=fun x => fderiv ℝ (flatFourier s b pb) x (flatAxis 0))
    (fun x hx => by
      rw [flatBackgroundTensor_flux hu]
      change fderiv ℝ (fun y => u y 1) x (flatAxis 0)=_
      rw [(he1 x hx).fderiv_eq])
  have hfc := torusCellIntegral_congr_slice (T:=2*Real.pi)
    (f:=fun x => symmetricCrossFlux (fun _ => flatBackgroundTensor s) u x 0)
    (g:=fun x => flatCrossFlux s (affineFourierField s a pa α β) (flatFourier s b pb) x 0)
    (fun x hx => by
      rw [flatBackgroundTensor_crossFlux hu]
      change u x 1*fderiv ℝ (fun y => u y 0) x (flatAxis 0)-
        u x 0*fderiv ℝ (fun y => u y 1) x (flatAxis 0)=_
      have hv0 : u x 0=affineFourierField s a pa α β x := (he0 x hx).self_of_nhds
      have hv1 : u x 1=flatFourier s b pb x := (he1 x hx).self_of_nhds
      rw [(he0 x hx).fderiv_eq,(he1 x hx).fderiv_eq,hv0,hv1]
      rfl)
  exact ⟨hf0.trans (affine_fourier_mean_axial_flux hs ha hga hra α β ht),
    hf1.trans (flatFourier_mean_axial_flux_zero hs hb hgb hrb ht),
    hfc.trans (affine_fourier_cross_flux_zero hs ha hb hga hgb hra hrb α β ht)⟩

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatFourier_add {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a b phase : (Fin 2 → ℤ) → ℝ} {A B : ℝ}
    (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B) {x : Coord3} (hx : 0<x 0) :
    flatFourier s (fun h => a h+b h) phase x=flatFourier s a phase x+flatFourier s b phase x := by
  unfold flatFourier
  simp only [add_mul]
  exact (flatFourier_summable hs ha hx).tsum_add (flatFourier_summable hs hb hx)

lemma flatFourier_single (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (c : ℝ)
    (phase : (Fin 2 → ℤ) → ℝ) (x : Coord3) :
    flatFourier s (Pi.single h c) phase x=c*flatPhaseMode s h (phase h) x := by
  classical
  unfold flatFourier
  rw [tsum_eq_single h]
  · simp
  · intro k hk
    simp [Pi.single_eq_of_ne hk]

lemma flatFourier_zero (s : Fin 3 → ℝ) (phase : (Fin 2 → ℤ) → ℝ) (x : Coord3) :
    flatFourier s (fun _ => 0) phase x=0 := by simp [flatFourier]

lemma flatFourier_const_mul (s : Fin 3 → ℝ) (a phase : (Fin 2 → ℤ) → ℝ) (c : ℝ) (x : Coord3) :
    flatFourier s (fun h => c*a h) phase x=c*flatFourier s a phase x := by
  simp only [flatFourier,mul_assoc,tsum_mul_left]

lemma flatFourier_translation (s : Fin 3 → ℝ) (a phase : (Fin 2 → ℤ) → ℝ) (T : ℝ) (x : Coord3) :
    flatFourier s a phase (x+![T,0,0])=
      flatFourier s (fun h => a h*exp (-torusRate s h*T)) phase x := by
  unfold flatFourier
  apply tsum_congr
  intro h
  rw [flatPhaseMode_translation]
  ring

lemma translated_fourier_coeff_bound {s : Fin 3 → ℝ} {a : (Fin 2 → ℤ) → ℝ} {B T : ℝ}
    (ha : ∀ h,|a h|≤B) (hT : 0≤T) (h : Fin 2 → ℤ) :
    |a h*exp (-torusRate s h*T)|≤B := by
  have he : exp (-torusRate s h*T)≤1 := exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sqrt_nonneg _)) hT)
  rw [abs_mul,abs_of_pos (exp_pos _)]
  exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans (by simpa using ha h)

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def normalizedFourierCoefficients (s : Fin 3 → ℝ) (lam T : ℝ)
    (a : (Fin 2 → ℤ) → ℝ) (h : Fin 2 → ℤ) : ℝ := a h*exp (-(torusRate s h-lam)*T)

lemma normalizedFourierCoefficients_zero_iff (s : Fin 3 → ℝ) (lam T : ℝ)
    (a : (Fin 2 → ℤ) → ℝ) (h : Fin 2 → ℤ) :
    normalizedFourierCoefficients s lam T a h=0 ↔ a h=0 := by
  simp [normalizedFourierCoefficients,exp_ne_zero]

lemma normalizedFourierCoefficients_bound {s : Fin 3 → ℝ} {lam T B : ℝ}
    {a : (Fin 2 → ℤ) → ℝ} (ha : ∀ h,|a h|≤B) (hT : 0≤T)
    (hr : ∀ h,a h≠0 → lam≤torusRate s h) (h : Fin 2 → ℤ) :
    |normalizedFourierCoefficients s lam T a h|≤B := by
  by_cases hz : a h=0
  · simpa only [normalizedFourierCoefficients,hz,zero_mul,abs_zero] using
      (abs_nonneg (a h)).trans (ha h)
  have he : exp (-(torusRate s h-lam)*T)≤1 := exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr (hr h hz))) hT)
  rw [normalizedFourierCoefficients,abs_mul,abs_of_pos (exp_pos _)]
  exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans (by simpa using ha h)

lemma flatFourier_normalized_translation (s : Fin 3 → ℝ) (lam T : ℝ)
    (a phase : (Fin 2 → ℤ) → ℝ) (x : Coord3) :
    flatFourier s (normalizedFourierCoefficients s lam T a) phase x=
      exp (lam*T)*flatFourier s a phase (x+![T,0,0]) := by
  rw [flatFourier_translation,←flatFourier_const_mul]
  unfold flatFourier
  apply tsum_congr
  intro h
  have he : exp (-(torusRate s h-lam)*T)=exp (lam*T)*exp (-torusRate s h*T) := by
    rw [←exp_add]
    congr 1
    ring
  simp only [normalizedFourierCoefficients,he]
  ring

lemma pureWallMode_eq_flatPhaseMode (s : Fin 3 → ℝ) (k : ℤ) (x : Coord3) :
    pureWallMode 1 (torusRate s ![0,k]) (k:ℝ) (boxCoordinates x)=flatPhaseMode s ![0,k] 0 x := by
  simp [pureWallMode,flatPhaseMode,torusAngular,boxCoordinates_apply]

lemma single_fourier_coeff_bound (h : Fin 2 → ℤ) (k : Fin 2 → ℤ) : |(Pi.single h (1:ℝ) : (Fin 2 → ℤ) → ℝ) k|≤1 := by
  classical
  by_cases hk : k=h
  · subst k; simp
  · simp [Pi.single_eq_of_ne hk]

end ScalarConductivity

end

end OAI
