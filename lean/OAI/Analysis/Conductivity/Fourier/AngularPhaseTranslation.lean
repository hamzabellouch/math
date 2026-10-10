import Mathlib
import OAI.Analysis.Conductivity.Fourier.AngularFourierConjugacy

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

def angularRealTranslation (v : Fin 2 → ℝ) (x : Coord3) : Coord3 :=
  ![x 0,x 1+v 0,x 2+v 1]

def angularShiftPhase (phase : (Fin 2 → ℤ) → ℝ) (v : Fin 2 → ℝ)
    (h : Fin 2 → ℤ) : ℝ := phase h+(h 0:ℝ)*v 0+(h 1:ℝ)*v 1

lemma flatPhaseMode_angular_translation (s : Fin 3 → ℝ) (h : Fin 2 → ℤ)
    (phase : ℝ) (v : Fin 2 → ℝ) (x : Coord3) :
    flatPhaseMode s h phase (angularRealTranslation v x)=
      flatPhaseMode s h (phase+(h 0:ℝ)*v 0+(h 1:ℝ)*v 1) x := by
  unfold flatPhaseMode
  congr 1
  congr 1
  simp only [torusAngular,_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  dsimp [angularRealTranslation]
  ring

theorem flatFourier_angular_translation (s : Fin 3 → ℝ)
    (a phase : (Fin 2 → ℤ) → ℝ) (v : Fin 2 → ℝ) (x : Coord3) :
    flatFourier s a phase (angularRealTranslation v x)=
      flatFourier s a (angularShiftPhase phase v) x := by
  unfold flatFourier
  apply tsum_congr
  intro h
  rw [flatPhaseMode_angular_translation]
  rfl

lemma alignedPhaseTranslation_zero {k : ℤ} (hk : 0<k) (phase : ℝ) :
    phase+((![0,k] : Fin 2 → ℤ) 0:ℝ)*((![0,-phase/(k:ℝ)] : Fin 2 → ℝ) 0)+
      ((![0,k] : Fin 2 → ℤ) 1:ℝ)*((![0,-phase/(k:ℝ)] : Fin 2 → ℝ) 1)=0 := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  simp only [cons_val_zero,cons_val_one,Int.cast_zero,zero_mul,add_zero]
  field_simp
  ring

theorem leading_mode_normalized_alignment {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {h : Fin 2 → ℤ} (hh : h≠0) (phase : ℝ) :
    ∃ (k : ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℝ),
      0<k ∧ A.det=1 ∧ h ᵥ* A=![0,k] ∧
      (∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ normalizedAngularTensor s A 0*x^2+
        2*normalizedAngularTensor s A 1*x*y+normalizedAngularTensor s A 2*y^2) ∧
      (∀ x,flatPhaseMode s h phase (angularNormalizedLift A (angularRealTranslation v x))=
        flatPhaseMode (normalizedAngularTensor s A) ![0,k] 0 x) ∧
      MeasurePreserving (fun x : UnitAddTorus (Fin 2) => angularIntMap A (x+
        fun i => ((v i/(2*Real.pi):ℝ) : UnitAddCircle))) volume volume := by
  obtain ⟨k,A,hk,hA,he⟩ := leading_frequency_SL2_alignment hh
  let v : Fin 2 → ℝ := ![0,-phase/(k:ℝ)]
  refine ⟨k,A,v,hk,hA,he,normalizedAngularTensor_lower hs hA,?_,?_⟩
  · intro x
    rw [flatPhaseMode_angular_conjugacy s hA,he,flatPhaseMode_angular_translation]
    rw [show phase+((![0,k] : Fin 2 → ℤ) 0:ℝ)*v 0+
      ((![0,k] : Fin 2 → ℤ) 1:ℝ)*v 1=0 from alignedPhaseTranslation_zero hk phase]
  · exact (angularIntMap_measurePreserving hA).comp (measurePreserving_add_right volume _)

end ScalarConductivity

end
end

end OAI
