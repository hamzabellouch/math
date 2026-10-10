import Mathlib
import OAI.Analysis.Conductivity.Fourier.EndPoissonJets
import OAI.Analysis.Conductivity.Flux.CylinderGreen

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

local instance cylinderModeGreenMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance cylinderModeGreenProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def flatCylinderEnergy (s : Fin 3 → ℝ) {R : ℝ} (u v : FiniteCylinderJets R) : ℂ :=
  inner ℂ (u 1) (v 1)+(s 0:ℂ)*inner ℂ (u 2) (v 2)+
    (s 1:ℂ)*(inner ℂ (u 2) (v 3)+inner ℂ (u 3) (v 2))+
    (s 2:ℂ)*inner ℂ (u 3) (v 3)

lemma flatCylinderEnergy_continuous_left (s : Fin 3 → ℝ) {R : ℝ} (v : FiniteCylinderJets R) :
    Continuous (fun u => flatCylinderEnergy s u v) := by
  unfold flatCylinderEnergy
  fun_prop

lemma flatCylinderEnergy_continuous_right (s : Fin 3 → ℝ) {R : ℝ} (u : FiniteCylinderJets R) :
    Continuous (fun v => flatCylinderEnergy s u v) := by
  unfold flatCylinderEnergy
  fun_prop

lemma cylinderMode_inner (R : ℝ) (h k : TorusModes) (f g : FiniteAxisL2 R) :
    inner ℂ (cylinderMode (FiniteAxisMeasure R) h f) (cylinderMode (FiniteAxisMeasure R) k g)=
      if h=k then inner ℂ f g else 0 := by
  by_cases he : h=k
  · subst k
    rw [ite_eq_left rfl]
    exact (cylinderMode (FiniteAxisMeasure R) h).inner_map_map f g
  · rw [ite_eq_right he]
    exact cylinderMode_orthogonal (FiniteAxisMeasure R) he f g

def smoothCylinderModeJet {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (k : TorusModes) : FiniteCylinderJets R :=
  WithLp.toLp 2 ![cylinderMode (FiniteAxisMeasure R) k (smoothFiniteAxisLp hq.continuous R),
    cylinderMode (FiniteAxisMeasure R) k (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R),
    cylinderMode (FiniteAxisMeasure R) k ((Complex.I*(k 0:ℂ))•smoothFiniteAxisLp hq.continuous R),
    cylinderMode (FiniteAxisMeasure R) k ((Complex.I*(k 1:ℂ))•smoothFiniteAxisLp hq.continuous R)]

lemma flatCylinderEnergy_distinct_modes (s : Fin 3 → ℝ) {q : ℝ → ℂ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (R : ℝ) (h k : TorusModes) (a : ℂ) (hne : h≠k) :
    flatCylinderEnergy s (endPoissonModeJet s R h a) (smoothCylinderModeJet hq R k)=0 := by
  simp only [flatCylinderEnergy,endPoissonModeJet,smoothCylinderModeJet,WithLp.ofLp_toLp,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    cylinderMode_inner,ite_eq_right hne,mul_zero,add_zero]

lemma torusRate_sq_of_lower (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (h : TorusModes) :
    torusRate s h^2=torusQuadratic s h := by
  apply Real.sq_sqrt
  exact (show (0:ℝ)≤(1/2)*((h 0:ℝ)^2+(h 1:ℝ)^2) by positivity).trans (hs _ _)

lemma flatCylinderEnergy_same_mode (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (R : ℝ) (h : TorusModes) (a : ℂ) :
    flatCylinderEnergy s (endPoissonModeJet s R h a) (smoothCylinderModeJet hq R h)=
      inner ℂ (finiteDecayLp (torusRate s h) R (-(torusRate s h:ℂ)*a))
        (smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R)+
      ((torusRate s h)^2:ℝ)*inner ℂ (finiteDecayLp (torusRate s h) R a)
        (smoothFiniteAxisLp hq.continuous R) := by
  simp only [flatCylinderEnergy,endPoissonModeJet,smoothCylinderModeJet,WithLp.ofLp_toLp,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    cylinderMode_inner,ite_true,endModeCoefficient]
  simp only [finiteDecayLp_smul,inner_smul_left,inner_smul_right,map_mul,map_intCast,Complex.conj_I]
  rw [torusRate_sq_of_lower s hs h]
  simp only [torusQuadratic,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_intCast,Complex.ofReal_ofNat]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem flatCylinder_mode_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (R : ℝ) (hR : 0≤R)
    (h k : TorusModes) (a : ℂ) :
    flatCylinderEnergy s (endPoissonModeJet s R h a) (smoothCylinderModeJet hq R k)=
      if h=k then
        (torusRate s h:ℂ)*inner ℂ a (q 0)-
          (torusRate s h*Real.exp (-torusRate s h*R):ℝ)*inner ℂ a (q R)
      else 0 := by
  by_cases he : h=k
  · subst k
    rw [ite_eq_left rfl,flatCylinderEnergy_same_mode s hs hq R h a]
    exact finiteDecay_green_inner hq _ R hR a
  · rw [ite_eq_right he]
    exact flatCylinderEnergy_distinct_modes s hq R h k a he

end ScalarConductivity

end

end OAI
