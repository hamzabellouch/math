import Mathlib
import OAI.Analysis.Conductivity.Fourier.UndoAngularWeakPair

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real
open scoped Matrix.Norms.Elementwise

lemma undoAngularValue_periodic {F : Coord3 → Fin 2 → ℝ} {P : ℝ}
    (hF : AngularPeriodic P F) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (θ : Fin 2 → ℝ) (d lam : ℝ) : AngularPeriodic P (undoAngularValue A θ d lam F) := by
  have h := hF.undoAngularPoint A θ d
  intro n x
  unfold undoAngularValue
  rw [show F (undoAngularPoint A θ d (x+angularShift P n))=F (undoAngularPoint A θ d x) from h n x]

lemma undoAngularTensor_periodic {E : Coord3 → Mat3} {P : ℝ}
    (hE : AngularPeriodic P E) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (θ : Fin 2 → ℝ) (d : ℝ) : AngularPeriodic P (undoAngularTensor A θ d E) := by
  have h := hE.undoAngularPoint A θ d
  intro n x
  unfold undoAngularTensor
  rw [show E (undoAngularPoint A θ d (x+angularShift P n))=E (undoAngularPoint A θ d x) from h n x]

lemma angularLiftMatrix_normal (A : Matrix (Fin 2) (Fin 2) ℤ) :
    angularLiftMatrix A*ᵥPi.single 0 1=sqrt (angularNormalization A) • Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,
    angularLiftMatrix,Pi.single_apply]

lemma angularLiftMatrix_transpose_normal (A : Matrix (Fin 2) (Fin 2) ℤ) :
    (angularLiftMatrix A)ᵀ*ᵥPi.single 0 1=sqrt (angularNormalization A) • Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,
    angularLiftMatrix,Pi.single_apply]

lemma undoAngularTensor_normal {A : Matrix (Fin 2) (Fin 2) ℤ}
    (θ : Fin 2 → ℝ) (d : ℝ) {E : Coord3 → Mat3} {x : Coord3}
    (hE : E (undoAngularPoint A θ d x)*ᵥPi.single 0 1=Pi.single 0 1) :
    undoAngularTensor A θ d E x*ᵥPi.single 0 1=Pi.single 0 1 := by
  rw [undoAngularTensor,Matrix.smul_mulVec,←Matrix.mulVec_mulVec,
    angularLiftMatrix_transpose_normal,←Matrix.mulVec_mulVec,Matrix.mulVec_smul,hE,
    Matrix.mulVec_smul,angularLiftMatrix_normal,smul_smul,smul_smul]
  rw [mul_assoc,←sq,sq_sqrt (angularNormalization_pos A).le,
    inv_mul_cancel₀ (angularNormalization_pos A).ne',one_smul]

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real
open scoped Matrix.Norms.Elementwise

theorem original_mode_finite_ending {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {h₀ : Fin 2 → ℤ} (hh₀ : h₀≠0)
    {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s h₀+gb≤torusRate s h) :
    ∃ d e R : ℝ,0<d ∧ 0<e ∧ d+e<R ∧
      ∃ w : WeakFiniteTensorPair {x : Coord3 | d<x 0},
        AngularPeriodic (2*Real.pi) w.v ∧ AngularPeriodic (2*Real.pi) w.E ∧
        (∀ x,x 0∈Icc d (d+e) → w.v x=
          ![x 0+flatFourier s a pa x,flatPhaseMode s h₀ (pb h₀) x+flatFourier s b pb x]) ∧
        (∀ x,x 0∈Icc d (d+e) → w.E x=flatBackgroundTensor s) ∧
        (∀ x,R≤x 0 → w.v x=![x 0,0]) ∧
        (∀ x,R≤x 0 → w.E x*ᵥPi.single 0 1=Pi.single 0 1) := by
  obtain ⟨Q,θ,hQ,p,T,hp,_hpδ,hT,z,hzp,hEp,hzin,hEin,hzt,hEn⟩ :=
    general_mode_weak_finite_ending (pa:=pa) (pb:=pb) hs hh₀ hA hB ha hb hga hgb hra hrb (by norm_num : (0:ℝ)<1)
  let m := sqrt (angularNormalization Q)
  have hm : 0 < m := sqrt_pos.mpr (angularNormalization_pos Q)
  let d := m*(10+1/p)
  let e := m/2
  let R := d+m*T
  let w := z.undoAngular hQ θ d (torusRate s h₀)
  have hd : 0<d := mul_pos hm (by linarith [one_div_pos.mpr hp.1])
  have he : 0<e := div_pos hm (by norm_num)
  have hdeR : d+e<R := by dsimp [R,e]; nlinarith
  have hxy (x : Coord3) (hx : x 0∈Icc d (d+e)) :
      (x 0-d)/sqrt (angularNormalization Q)∈Icc 0 (1/2) := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hm.le
    · apply (div_le_iff₀ hm).mpr
      dsimp [e] at hx
      linarith [hx.2]
  refine ⟨d,e,R,hd,he,hdeR,w,?_,?_,?_,?_,?_,?_⟩
  · rw [WeakFiniteTensorPair.undoAngular_v]
    exact undoAngularValue_periodic hzp Q θ d _
  · rw [WeakFiniteTensorPair.undoAngular_E]
    exact undoAngularTensor_periodic hEp Q θ d
  · intro x hx
    rw [WeakFiniteTensorPair.undoAngular_v]
    exact undoAngularValue_matching hQ θ d h₀ a b pa pb hzin (hxy x hx)
  · intro x hx
    rw [WeakFiniteTensorPair.undoAngular_E]
    exact undoAngularTensor_matching hQ θ d hEin (hxy x hx)
  · intro x hx
    rw [WeakFiniteTensorPair.undoAngular_v]
    exact undoAngularValue_terminal Q θ d _ T hzt hx
  · intro x hx
    rw [WeakFiniteTensorPair.undoAngular_E]
    apply undoAngularTensor_normal
    apply hEn
    rw [undoAngularPoint_zero]
    apply (le_div_iff₀ hm).mpr
    dsimp [R] at hx
    nlinarith

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

local instance undoAngularPropertiesMeasurableSpaceMat3 : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance undoAngularPropertiesBorelSpaceMat3 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

theorem general_mode_finite_ending_raw {s : Fin 3 → ℝ}
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
  obtain ⟨p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hv,hEm,hvp,hEp,⟨hsym,hreg⟩,hbound,hvin,hEin,hterm,_hrank,hG,hpde⟩ :=
    aligned_fourier_finite_ending (pa:=pa')
      (normalizedAngularTensor_lower hs hQ) hk (div_nonneg hA hm.le) hB hab hbb
      (mul_pos hm hga) (mul_pos hm hgb) hra' hrb' hphase hδ
  refine ⟨Q,θ,k,hQ,hk,he,p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hsym,hv,hEm,hvp,hEp,hbound,?_,hEin,hterm,hreg,hG,hpde⟩
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

end OAI
