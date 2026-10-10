import Mathlib
import OAI.Analysis.Conductivity.Sources.AngularGraph
import OAI.Analysis.Conductivity.Fourier.AngularPeriodization

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
local instance torusSmoothModeJetMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusSmoothModeJetIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma torusAngles_shift (n : Fin 2 → ℤ) (x : Coord3) :
    torusAngles (x+angularShift (2*Real.pi) n)=torusAngles x := by
  have hπ : 2*Real.pi≠0 := by positivity
  ext i
  fin_cases i <;> simp [torusAngles,angularShift,add_div,hπ,mul_div_cancel_left₀]

def angularFrequency (h : TorusModes) : Coord3 →L[ℝ] ℂ :=
  (Complex.I*(h 0:ℂ)) • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1)+
  (Complex.I*(h 1:ℂ)) • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 2)

lemma angularFrequency_apply (h : TorusModes) (x : Coord3) :
    angularFrequency h x=(torusAngular h x:ℂ)*Complex.I := by
  simp [angularFrequency,torusAngular]
  ring

def flatSmoothMode (q : ℝ → ℂ) (h : TorusModes) (x : Coord3) : ℂ :=
  q (x 0)*Complex.exp (angularFrequency h x)

lemma flatSmoothMode_eq (q : ℝ → ℂ) (h : TorusModes) (x : Coord3) :
    flatSmoothMode q h x=q (x 0)*mFourier h (torusAngles x) := by
  rw [flatSmoothMode,angularFrequency_apply,mFourier_torusAngles]

lemma flatSmoothMode_smooth {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (h : TorusModes) : ContDiff ℝ (↑(⊤:ℕ∞)) (flatSmoothMode q h) :=
  (hq.comp (contDiff_apply ℝ ℝ (0:Fin 3))).mul (angularFrequency h).contDiff.cexp

lemma flatSmoothMode_periodic (q : ℝ → ℂ) (h : TorusModes) :
    AngularPeriodic (2*Real.pi) (flatSmoothMode q h) := by
  intro n x
  rw [flatSmoothMode_eq,flatSmoothMode_eq,torusAngles_shift]
  simp [angularShift]

def smoothModePointJet (q : ℝ → ℂ) (h : TorusModes) (j : Fin 4)
    (z : ℝ × UnitAddTorus (Fin 2)) : ℂ :=
  ![q z.1,deriv q z.1,(Complex.I*(h 0))*q z.1,(Complex.I*(h 1))*q z.1] j*mFourier h z.2

lemma flatSmoothMode_derivative {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (h : TorusModes) (x : Coord3) (j : Fin 3) :
    fderiv ℝ (flatSmoothMode q h) x (Pi.single j 1)=
      smoothModePointJet q h j.succ (x 0,torusAngles x) := by
  have hq' := ((hq.differentiable (by simp) (x 0)).hasDerivAt.hasFDerivAt).comp x (f:=fun y : Coord3 => y 0)
    ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 3 => ℝ) 0).hasFDerivAt (x:=x))
  have he := ((angularFrequency h).hasFDerivAt (x:=x)).cexp
  have hd := hq'.mul he
  change HasFDerivAt (flatSmoothMode q h) _ x at hd
  rw [hd.fderiv]
  rw [smoothModePointJet,mFourier_torusAngles,←angularFrequency_apply]
  fin_cases j <;> simp [angularFrequency] <;> ring

lemma smoothCylinderModeJet_ae {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (h : TorusModes) (j : Fin 4) :
    smoothCylinderModeJet hq R h j=ᵐ[(FiniteAxisMeasure R).prod volume]
      smoothModePointJet q h j := by
  have h1 := (Measure.quasiMeasurePreserving_fst
    (μ:=FiniteAxisMeasure R) (ν:=(volume : Measure (UnitAddTorus (Fin 2))))).ae
      (smoothAxisModeJet_ae hq R h j)
  have h2 := (Measure.quasiMeasurePreserving_snd
    (μ:=FiniteAxisMeasure R) (ν:=(volume : Measure (UnitAddTorus (Fin 2))))).ae
      (coeFn_mFourierLp 2 h)
  have hc : smoothCylinderModeJet hq R h j=
      cylinderTensor (smoothAxisModeJet hq R h j) (mFourierLp 2 h) := by
    fin_cases j <;> rfl
  rw [hc]
  filter_upwards [cylinderTensor_ae (smoothAxisModeJet hq R h j) (mFourierLp 2 h),h1,h2]
    with z hz ht hθ
  rw [hz,ht,hθ]
  rfl

end ScalarConductivity

end
end

end OAI
