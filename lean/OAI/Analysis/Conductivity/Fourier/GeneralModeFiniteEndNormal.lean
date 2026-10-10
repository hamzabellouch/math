import Mathlib
import OAI.Analysis.Conductivity.Scalarization.GeneralModeEndingScalarization
import OAI.Analysis.Conductivity.Fourier.FourierFiniteEndingNormal

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

local instance generalModeFiniteEndNormalMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance generalModeFiniteEndNormalBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

theorem general_mode_finite_ending_raw_normal {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {h₀ : Fin 2 → ℤ} (hh₀ : h₀≠0)
    {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s h₀+gb≤torusRate s h)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ) (k : ℤ),
      Q.det=1 ∧ 0<k ∧ h₀ ᵥ* Q=![0,k] ∧
      ∃ p T c C : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧ 7<T ∧ 0<c ∧ c≤C ∧
      ∃ (v : Coord3 → Fin 2 → ℝ) (E : Coord3 → Mat3)
        (hsym : ∀ x,(E x).IsSymm),
        ContDiff ℝ 2 v ∧ Measurable E ∧
        AngularPeriodic (2*Real.pi) v ∧ AngularPeriodic (2*Real.pi) E ∧
        (∀ x w,c*(w ⬝ᵥ w)≤w ⬝ᵥ (E x*ᵥw) ∧ w ⬝ᵥ (E x*ᵥw)≤C*(w ⬝ᵥ w)) ∧
        (∀ x,x 0∈Icc 0 (1/2) → v x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0
              (Real.sqrt (angularNormalization Q)*(10+1/p)) a) pa
              (angularNormalizedLift Q (angularRealTranslation θ x))/Real.sqrt (angularNormalization Q),
            flatPhaseMode s h₀ (pb h₀) (angularNormalizedLift Q (angularRealTranslation θ x))+
              flatFourier s (normalizedFourierCoefficients s (torusRate s h₀)
                (Real.sqrt (angularNormalization Q)*(10+1/p)) b) pb
                (angularNormalizedLift Q (angularRealTranslation θ x))]) ∧
        (∀ x,x 0∈Icc 0 (1/2) → E x=flatBackgroundTensor (normalizedAngularTensor s Q)) ∧
        (∀ x,T≤x 0 → v x=![x 0,0]) ∧
        (∀ x,7≤x 0 → E x*ᵥPi.single 0 1=Pi.single 0 1) ∧
        (∀ᵐ x : Coord3,0<x 0 → x∈regularRegion v (fun y => ⟨E y,hsym y⟩) {y : Coord3 | 0<y 0}) ∧
        (∃ G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ, ContDiff ℝ 1 G ∧
          ∀ᵐ x : Coord3,E x*gradientColumns (fderiv ℝ v x)=G x) ∧
        ∀ (j : Fin 2) (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val →
          tsupport ψ.val ⊆ {x : Coord3 | 0<x 0} →
          Integrable (fun x => ∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
            (smoothDirection (Pi.single i 1) ψ).val x) ∧
          (∫ x,∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
            (smoothDirection (Pi.single i 1) ψ).val x)=0 := by
  obtain ⟨k,Q,hk,hQ,he⟩ := leading_frequency_SL2_alignment hh₀
  let m := Real.sqrt (angularNormalization Q)
  have hm : 0 < m := Real.sqrt_pos.mpr (angularNormalization_pos Q)
  let e := angularFrequencyEquiv Q hQ
  let θ : Fin 2 → ℝ := ![0,-pb h₀/(k:ℝ)]
  let a' : (Fin 2 → ℤ) → ℝ := fun h => a (e.symm h)/m
  let b' : (Fin 2 → ℤ) → ℝ := b ∘ e.symm
  let pa' := angularShiftPhase (pa ∘ e.symm) θ
  let pb' := angularShiftPhase (pb ∘ e.symm) θ
  have hphase : pb' ![0,k]=0 := by
    have he0 : e.symm ![0,k]=h₀ := by
      rw [←he]
      exact e.symm_apply_apply h₀
    dsimp [pb',angularShiftPhase]
    rw [he0]
    exact alignedPhaseTranslation_zero hk (pb h₀)
  have hmode (x : Coord3) :
      flatPhaseMode s h₀ (pb h₀) (angularNormalizedLift Q (angularRealTranslation θ x))=
      flatPhaseMode (normalizedAngularTensor s Q) ![0,k] 0 x := by
    rw [flatPhaseMode_angular_conjugacy s hQ,he,flatPhaseMode_angular_translation]
    rw [show pb h₀+((![0,k] : Fin 2 → ℤ) 0:ℝ)*θ 0+
      ((![0,k] : Fin 2 → ℤ) 1:ℝ)*θ 1=0 from alignedPhaseTranslation_zero hk (pb h₀)]
  have hab : ∀ h,|a' h|≤A/m := by
    intro h
    dsimp [a']
    rw [abs_div,abs_of_pos hm]
    exact (div_le_div_iff_of_pos_right hm).2 (ha _)
  have hbb : ∀ h,|b' h|≤B := fun h => hb (e.symm h)
  have hgapA := angular_conjugacy_gap s hQ (a:=a) (lam:=0) hga
    (fun h hh => by simpa only [zero_add] using hra h hh)
  have hgapB := angular_conjugacy_gap s hQ hgb hrb
  have hrate : torusRate (normalizedAngularTensor s Q) ![0,k]=m*torusRate s h₀ := by
    rw [←he,torusRate_angular_conjugacy s hQ]
  have hra' : ∀ h,a' h≠0 → m*ga≤torusRate (normalizedAngularTensor s Q) h := by
    intro h hh
    have hh' : (a ∘ e.symm) h≠0 := by
      intro hz
      apply hh
      dsimp [a']
      rw [show a (e.symm h)=0 from hz,zero_div]
    simpa only [mul_zero,zero_add] using hgapA.2 h hh'
  have hrb' : ∀ h,b' h≠0 → torusRate (normalizedAngularTensor s Q) ![0,k]+m*gb≤
      torusRate (normalizedAngularTensor s Q) h := by
    intro h hh
    rw [hrate]
    exact hgapB.2 h hh
  obtain ⟨p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hv,hEm,hvp,hEp,⟨hsym,hreg⟩,hbound,hvin,hEin,hterm,hnormal,_hrank,hG,hpde⟩ :=
    aligned_fourier_finite_ending_with_normal (pa:=pa')
      (normalizedAngularTensor_lower hs hQ) hk (div_nonneg hA hm.le) hB hab hbb
      (mul_pos hm hga) (mul_pos hm hgb) hra' hrb' hphase hδ
  refine ⟨Q,θ,k,hQ,hk,he,p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hsym,hv,hEm,hvp,hEp,hbound,?_,hEin,hterm,hnormal,hreg,hG,hpde⟩
  intro x hx
  rw [hvin x hx,hmode]
  congr 1
  · congr 1
    rw [normalizedFourierCoefficients_div,flatFourier_div_coefficients]
    congr 1
    simpa only [pa',e,Function.comp_def,mul_zero] using normalized_flatFourier_angular_conjugacy s hQ a pa 0 (10+1/p) θ x
  · rw [hrate]
    congr 2
    simpa only [b',pb',m,e,Function.comp_apply] using normalized_flatFourier_angular_conjugacy s hQ b pb (torusRate s h₀) (10+1/p) θ x

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def angularInverseLift (A : Matrix (Fin 2) (Fin 2) ℤ) (x : Coord3) : Coord3 :=
  ![x 0/Real.sqrt (angularNormalization A),
    (A 1 1:ℝ)*x 1-(A 0 1:ℝ)*x 2,-(A 1 0:ℝ)*x 1+(A 0 0:ℝ)*x 2]

def angularNormalizedLinear (A : Matrix (Fin 2) (Fin 2) ℤ) : Coord3 →ₗ[ℝ] Coord3 where
  toFun := angularNormalizedLift A
  map_add' x y := by ext i; fin_cases i <;> simp [angularNormalizedLift] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [angularNormalizedLift] <;> ring

def angularInverseLinear (A : Matrix (Fin 2) (Fin 2) ℤ) : Coord3 →ₗ[ℝ] Coord3 where
  toFun := angularInverseLift A
  map_add' x y := by ext i; fin_cases i <;> simp [angularInverseLift] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [angularInverseLift] <;> ring

lemma real_angular_det_one {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) :
    (A 0 0:ℝ)*(A 1 1:ℝ)-(A 0 1:ℝ)*(A 1 0:ℝ)=1 := by
  have h : A 0 0*A 1 1-A 0 1*A 1 0=1 := by simpa only [Matrix.det_fin_two] using hA
  exact_mod_cast h

lemma angularNormalizedLift_inverse {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) (x : Coord3) :
    angularNormalizedLift A (angularInverseLift A x)=x := by
  have hd := real_angular_det_one hA
  have hm : Real.sqrt (angularNormalization A)≠0 := (Real.sqrt_pos.mpr (angularNormalization_pos A)).ne'
  ext i
  fin_cases i
  · change Real.sqrt (angularNormalization A) * (x 0 / Real.sqrt (angularNormalization A)) = x 0
    field_simp [hm]
  · change (A 0 0:ℝ)*((A 1 1:ℝ)*x 1-(A 0 1:ℝ)*x 2)+
      (A 0 1:ℝ)*(-(A 1 0:ℝ)*x 1+(A 0 0:ℝ)*x 2)=x 1
    nlinarith [congrArg (fun z : ℝ => z*x 1) hd]
  · change (A 1 0:ℝ)*((A 1 1:ℝ)*x 1-(A 0 1:ℝ)*x 2)+
      (A 1 1:ℝ)*(-(A 1 0:ℝ)*x 1+(A 0 0:ℝ)*x 2)=x 2
    nlinarith [congrArg (fun z : ℝ => z*x 2) hd]

lemma angularInverseLift_normalized {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1) (x : Coord3) :
    angularInverseLift A (angularNormalizedLift A x)=x := by
  have hd := real_angular_det_one hA
  have hm : Real.sqrt (angularNormalization A)≠0 := (Real.sqrt_pos.mpr (angularNormalization_pos A)).ne'
  ext i
  fin_cases i
  · simp [angularNormalizedLift,angularInverseLift,hm]
  · change (A 1 1:ℝ)*((A 0 0:ℝ)*x 1+(A 0 1:ℝ)*x 2)-
      (A 0 1:ℝ)*((A 1 0:ℝ)*x 1+(A 1 1:ℝ)*x 2)=x 1
    nlinarith [congrArg (fun z : ℝ => z*x 1) hd]
  · change -(A 1 0:ℝ)*((A 0 0:ℝ)*x 1+(A 0 1:ℝ)*x 2)+
      (A 0 0:ℝ)*((A 1 0:ℝ)*x 1+(A 1 1:ℝ)*x 2)=x 2
    nlinarith [congrArg (fun z : ℝ => z*x 2) hd]

def angularNormalizedEquiv (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det=1) : Coord3 ≃L[ℝ] Coord3 :=
  (LinearEquiv.ofLinearMap (angularNormalizedLinear A) (angularInverseLinear A)
    (by apply LinearMap.ext; intro x; exact angularNormalizedLift_inverse hA x)
    (by apply LinearMap.ext; intro x; exact angularInverseLift_normalized hA x)).toContinuousLinearEquiv

@[simp] lemma angularNormalizedEquiv_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det=1) (x : Coord3) :
    angularNormalizedEquiv A hA x=angularNormalizedLift A x := rfl

@[simp] lemma angularNormalizedEquiv_symm_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det=1) (x : Coord3) :
    (angularNormalizedEquiv A hA).symm x=angularInverseLift A x := rfl

def angularLiftMatrix (A : Matrix (Fin 2) (Fin 2) ℤ) : Mat3 :=
  !![Real.sqrt (angularNormalization A),0,0;
    0,(A 0 0:ℝ),(A 0 1:ℝ);0,(A 1 0:ℝ),(A 1 1:ℝ)]

lemma operatorMatrix_angularNormalizedEquiv (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det=1) :
    operatorMatrix (angularNormalizedEquiv A hA : Coord3 →L[ℝ] Coord3)=angularLiftMatrix A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorMatrix,angularLiftMatrix,angularNormalizedEquiv,angularNormalizedLinear,
      angularNormalizedLift]

end ScalarConductivity

end
end

end OAI
