import Mathlib
import OAI.Probability.SKSupport.Moments.SquareEquation
import OAI.Probability.SKSupport.Regularity.TimeFields

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def compactJet (W : BrownianSystem Ω) (γ : OrderParameter) (T : ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  iteratedDeriv n (compactGradient W γ T t) x

lemma compactJet_hasDerivAt (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) (t x : ℝ) :
    HasDerivAt (compactJet W γ T n t) (compactJet W γ T (n+1) t x) x :=
  by
    have hh : ContDiff ℝ ∞ (compactJet W γ T n t) :=
      (((compactGradient_family W γ hT0 hT1).iteratedDeriv n).regular t).smooth
    have he : compactJet W γ T (n+1) t x=deriv (compactJet W γ T n t) x := by
      unfold compactJet
      rw [iteratedDeriv_succ]
    rw [he]
    exact (hh.differentiable (by simp) x).hasDerivAt

lemma deriv_compactJet (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) (t : ℝ) :
    deriv (compactJet W γ T n t)=compactJet W γ T (n+1) t :=
  funext (fun x => (compactJet_hasDerivAt W γ hT0 hT1 n t x).deriv)

def compactJetField (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) : TimeField T where
  f := compactJet W γ T n
  d := fun t x => iteratedDeriv (n+1) (compactValueRate W γ T t) x
  smooth := (compactGradient_family W γ hT0 hT1).iteratedDeriv n
  rate_smooth := (compactValueRate_family W γ hT0 hT1).iteratedDeriv (n+1)
  continuous := compactGradient_derivative_continuous W γ hT0 hT1 n
  rate_right := fun t x => (compactValueRate_rightSmooth W γ hT0 hT1 (n+1) t x).mono Ioi_subset_Ici_self
  time_deriv := by
    intro t ht0 htT x
    have hh := value_derivative_hasDerivWithinAt_right W γ hT0 hT1 ht0 htT (n+1) x
    apply hh.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htT)] with s hs hsT
      unfold compactJet compactGradient gradient
      rw [stripClamp_eq ⟨ht0.trans hs.le,hsT.le⟩,iteratedDeriv_succ']
    · unfold compactJet compactGradient gradient
      rw [stripClamp_eq ⟨ht0,htT.le⟩,iteratedDeriv_succ']

lemma compactRate_jet_one (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    deriv (compactValueRate W γ T t) x= -(1/2:ℝ)*compactJet W γ T 2 t x-
      compactCoeff γ T t*compactJet W γ T 0 t x*compactJet W γ T 1 t x := by
  simpa only [compactJet,iteratedDeriv_succ,iteratedDeriv_zero] using deriv_compactValueRate W γ hT0 hT1 t x

lemma compactRate_jet_two (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    iteratedDeriv 2 (compactValueRate W γ T t) x= -(1/2:ℝ)*compactJet W γ T 3 t x-
      compactCoeff γ T t*((compactJet W γ T 1 t x)^2+compactJet W γ T 0 t x*compactJet W γ T 2 t x) := by
  have he : deriv (compactValueRate W γ T t)=fun y => -(1/2:ℝ)*compactJet W γ T 2 t y-
      compactCoeff γ T t*compactJet W γ T 0 t y*compactJet W γ T 1 t y := funext (compactRate_jet_one W γ hT0 hT1 t)
  have hd (n : ℕ) := compactJet_hasDerivAt W γ hT0 hT1 n t x
  have hh := ((hd 2).const_mul (-(1/2:ℝ))).sub (((hd 0).const_mul (compactCoeff γ T t)).mul (hd 1))
  have hdv := hh.deriv
  change deriv (fun y => -(1/2:ℝ)*compactJet W γ T 2 t y-
      compactCoeff γ T t*compactJet W γ T 0 t y*compactJet W γ T 1 t y) x = _ at hdv
  simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at ⊢
  rw [he,hdv]
  ring

lemma compactRate_jet_three (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    iteratedDeriv 3 (compactValueRate W γ T t) x= -(1/2:ℝ)*compactJet W γ T 4 t x-
      compactCoeff γ T t*(3*compactJet W γ T 1 t x*compactJet W γ T 2 t x+
        compactJet W γ T 0 t x*compactJet W γ T 3 t x) := by
  have he : iteratedDeriv 2 (compactValueRate W γ T t)=fun y => -(1/2:ℝ)*compactJet W γ T 3 t y-
      compactCoeff γ T t*((compactJet W γ T 1 t y)^2+compactJet W γ T 0 t y*compactJet W γ T 2 t y) :=
    funext (compactRate_jet_two W γ hT0 hT1 t)
  have hd (n : ℕ) := compactJet_hasDerivAt W γ hT0 hT1 n t x
  have hh := ((hd 3).const_mul (-(1/2:ℝ))).sub
    ((((hd 1).pow 2).add ((hd 0).mul (hd 2))).const_mul (compactCoeff γ T t))
  have hdv := hh.deriv
  change deriv (fun y => -(1/2:ℝ)*compactJet W γ T 3 t y-
      compactCoeff γ T t*((compactJet W γ T 1 t y)^2+compactJet W γ T 0 t y*compactJet W γ T 2 t y)) x = _ at hdv
  rw [show (3:ℕ)=2+1 from rfl,iteratedDeriv_succ,he,hdv]
  ring

lemma compactJetField_generator_one (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    (compactJetField W γ hT0 hT1 1).generator (compactDrift W γ T) t x=
      -compactCoeff γ T t*(compactJet W γ T 1 t x)^2 := by
  dsimp only [TimeField.generator,compactJetField]
  rw [deriv_compactJet W γ hT0 hT1,deriv_compactJet W γ hT0 hT1,
    compactRate_jet_two W γ hT0 hT1]
  change compactJet W γ T 2 t x*(compactCoeff γ T t*compactJet W γ T 0 t x)+_+_= _
  ring

lemma compactJetField_generator_two (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    (compactJetField W γ hT0 hT1 2).generator (compactDrift W γ T) t x=
      -3*compactCoeff γ T t*compactJet W γ T 1 t x*compactJet W γ T 2 t x := by
  dsimp only [TimeField.generator,compactJetField]
  rw [deriv_compactJet W γ hT0 hT1,deriv_compactJet W γ hT0 hT1,
    compactRate_jet_three W γ hT0 hT1]
  change compactJet W γ T 3 t x*(compactCoeff γ T t*compactJet W γ T 0 t x)+_+_= _
  ring

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def curvatureField (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) : TimeField T :=
  (compactJetField W γ hT0 hT1 1).mul (compactJetField W γ hT0 hT1 1)

def secondCurvatureField (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (c : ℝ) : TimeField T :=
  ((compactJetField W γ hT0 hT1 2).mul (compactJetField W γ hT0 hT1 2)).add
    (((curvatureField W γ hT0 hT1).mul (compactJetField W γ hT0 hT1 1)).const_mul (-2*c))

lemma curvatureField_deriv (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    deriv ((curvatureField W γ hT0 hT1).f t) x=
      2*compactJet W γ T 1 t x*compactJet W γ T 2 t x := by
  have hd := compactJet_hasDerivAt W γ hT0 hT1 1 t x
  exact (hd.mul hd).deriv.trans (by ring)

lemma curvatureField_generator (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    (curvatureField W γ hT0 hT1).generator (compactDrift W γ T) t x=
      (secondCurvatureField W γ hT0 hT1 (compactCoeff γ T t)).f t x := by
  unfold curvatureField
  rw [TimeField.generator_mul,compactJetField_generator_one W γ hT0 hT1]
  dsimp only [compactJetField]
  rw [deriv_compactJet W γ hT0 hT1]
  dsimp only [secondCurvatureField,curvatureField,TimeField.add,TimeField.mul,TimeField.const_mul,compactJetField]
  ring

lemma secondCurvatureField_generator (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (c t x : ℝ) (hc : compactCoeff γ T t=c) :
    (secondCurvatureField W γ hT0 hT1 c).generator (compactDrift W γ T) t x=
      (compactJet W γ T 3 t x)^2-12*c*compactJet W γ T 1 t x*(compactJet W γ T 2 t x)^2+
        6*c^2*(compactJet W γ T 1 t x)^4 := by
  unfold secondCurvatureField
  rw [TimeField.generator_add,TimeField.generator_const_mul,TimeField.generator_mul,TimeField.generator_mul,
    curvatureField_generator W γ hT0 hT1,compactJetField_generator_one W γ hT0 hT1,
    compactJetField_generator_two W γ hT0 hT1,curvatureField_deriv W γ hT0 hT1]
  dsimp only [compactJetField]
  rw [deriv_compactJet W γ hT0 hT1,deriv_compactJet W γ hT0 hT1]
  dsimp only [secondCurvatureField,curvatureField,TimeField.add,TimeField.mul,TimeField.const_mul,compactJetField]
  rw [hc]
  ring

lemma curvatureField_eq (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    (curvatureField W γ hT0 hT1).f t x=(compactJet W γ T 1 t x)^2 := by
  dsimp only [curvatureField,TimeField.mul,compactJetField]
  ring

lemma secondCurvatureField_eq (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (c t x : ℝ) :
    (secondCurvatureField W γ hT0 hT1 c).f t x=
      (compactJet W γ T 2 t x)^2-2*c*(compactJet W γ T 1 t x)^3 := by
  dsimp only [secondCurvatureField,curvatureField,TimeField.add,TimeField.mul,TimeField.const_mul,compactJetField]
  ring

end ZeroTemperatureSK

end
end

end OAI
