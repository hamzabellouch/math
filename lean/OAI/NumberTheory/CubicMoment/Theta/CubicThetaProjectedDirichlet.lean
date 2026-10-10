import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSelectedAngularMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoefficientMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularFunctionalEquation

namespace OAI

/-! Entire continued Dirichlet series for the actual primary-projected
cusp pair, with the initial series fixed by the literal coefficients. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaBoundedScaledAxis_mellin {a : Eisenstein→ℂ} {C r : ℝ}
    (hC : 0≤C) (ha : ∀ n,‖a n‖≤C) (hr : 0<r) (z : ℂ) (ℓ : ℤ)
    {s : ℂ} (hs : 3/2<s.re) :
    mellin (cubicThetaBoundedScaledAxis a ℓ z r) (2*s+(ℓ.natAbs:ℂ)-1)=
      (r:ℂ)^(-(2*s+(ℓ.natAbs:ℂ)-1))*
        ((1/4:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2*(s+(ℓ.natAbs:ℂ)/2))*
          Complex.Gamma (s+(ℓ.natAbs:ℂ)/2+1/6)*Complex.Gamma (s+(ℓ.natAbs:ℂ)/2-1/6)*
          cubicThetaDirichlet (fun n => theta ℓ n*cubicThetaCoefficientTwist a z n) (2*s-1)) := by
  unfold cubicThetaBoundedScaledAxis
  rw [mellin_comp_mul_left (fun v : ℝ => cubicThetaNonconstant
    (cubicThetaAngularCoefficient a ℓ) (z,v)) _ hr,cubicThetaCoefficient_mellin hC ha z ℓ hs]
  rfl

lemma cubicThetaProjectedAngularCompleted_initial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : 3/2<s.re) :
    cubicThetaProjectedAngularCompleted g hc rev k (2*s+(k:ℂ)-1)=
      cubicThetaAngularCompletion (g 1 0) k s*
        cubicThetaDirichlet (fun n => theta (cubicThetaCircleOrder rev k) n*
          cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
            (cubicThetaPrimaryDualCenter g) n) (2*s-1) := by
  rw [←(cubicThetaProjectedAngular_mellin g hc rev hk _).2]
  have H := cubicThetaBoundedScaledAxis_mellin (by norm_num : (0:ℝ)≤243)
    (cubicThetaProjectedCoefficient_bound g hc) (cubicThetaLevelScale_pos hc)
    (cubicThetaPrimaryDualCenter g) (cubicThetaCircleOrder rev k) hs
  have habs : (cubicThetaCircleOrder rev k).natAbs=k := by cases rev <;> simp [cubicThetaCircleOrder]
  rw [habs] at H
  rw [cubicThetaProjectedAngularAxis,H]
  unfold cubicThetaAngularCompletion
  rw [show -2*(s+(k:ℂ)/2)=-(2*s+(k:ℂ)) by ring]
  ring

lemma cubicThetaSelectedAngularCompleted_initial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : 3/2<s.re) :
    cubicThetaSelectedAngularCompleted g hc rev k (2*s+(k:ℂ)-1)=
      cubicThetaAngularCompletion (g 1 0) k s*
        cubicThetaDirichlet (fun n => theta (cubicThetaCircleOrder (!rev) k) n*
          cubicThetaCoefficientTwist cubicThetaSelectedCoefficient
            (cubicThetaPrimaryCuspCenter g) n) (2*s-1) := by
  rw [←(cubicThetaSelectedAngular_mellin g hc rev hk _).2]
  have H := cubicThetaBoundedScaledAxis_mellin (by norm_num : (0:ℝ)≤81)
    cubicThetaSelectedCoefficient_norm (cubicThetaLevelScale_pos hc)
    (cubicThetaPrimaryCuspCenter g) (cubicThetaCircleOrder (!rev) k) hs
  have habs : (cubicThetaCircleOrder (!rev) k).natAbs=k := by cases rev <;> simp [cubicThetaCircleOrder]
  rw [habs] at H
  rw [cubicThetaSelectedAngularAxis,H]
  unfold cubicThetaAngularCompletion
  rw [show -2*(s+(k:ℂ)/2)=-(2*s+(k:ℂ)) by ring]
  ring

def cubicThetaProjectedDirichlet (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (rev : Bool) (k : ℕ) (s : ℂ) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) k s*
    cubicThetaProjectedAngularCompleted g hc rev k (2*s+(k:ℂ)-1)

def cubicThetaSelectedDirichlet (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (rev : Bool) (k : ℕ) (s : ℂ) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) k s*
    cubicThetaSelectedAngularCompleted g hc rev k (2*s+(k:ℂ)-1)

lemma cubicThetaAngularUncompletion_entire {q : Eisenstein} (hq : primary q) (k : ℕ) :
    Differentiable ℂ (cubicThetaAngularUncompletion q k) := by
  have hρ : (cubicThetaLevelScale q:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaLevelScale_pos hq).ne'
  have hπ : ((2*Real.pi:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hA : Differentiable ℂ (fun s : ℂ => 2*s+(k:ℂ)-1) := by fun_prop
  have hB : Differentiable ℂ (fun s : ℂ => 2*s+(k:ℂ)) := by fun_prop
  have hC : Differentiable ℂ (fun s : ℂ => s+(k:ℂ)/2+1/6) := by fun_prop
  have hD : Differentiable ℂ (fun s : ℂ => s+(k:ℂ)/2-1/6) := by fun_prop
  exact ((((hA.const_cpow (Or.inl hρ)).const_mul 4).mul (hB.const_cpow (Or.inl hπ))).mul
    (Complex.differentiable_one_div_Gamma.comp hC)).mul
      (Complex.differentiable_one_div_Gamma.comp hD)

theorem cubicThetaProjectedDirichlet_entire (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) :
    Differentiable ℂ (cubicThetaProjectedDirichlet g hc rev k) :=
  (cubicThetaAngularUncompletion_entire hc k).mul
    ((cubicThetaProjectedAngularCompleted_entire g hc rev k).comp (by fun_prop))

theorem cubicThetaSelectedDirichlet_entire (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) :
    Differentiable ℂ (cubicThetaSelectedDirichlet g hc rev k) :=
  (cubicThetaAngularUncompletion_entire hc k).mul
    ((cubicThetaSelectedAngularCompleted_entire g hc rev k).comp (by fun_prop))

lemma cubicThetaAngular_initial_gamma {s : ℂ} (hs : 3/2<s.re) (k : ℕ) :
    Complex.Gamma (s+(k:ℂ)/2+1/6)≠0 ∧ Complex.Gamma (s+(k:ℂ)/2-1/6)≠0 := by
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  constructor <;> apply Complex.Gamma_ne_zero_of_re_pos <;>
    simp only [Complex.add_re,Complex.sub_re,Complex.div_ofNat_re,Complex.natCast_re,Complex.one_re] <;>
    linarith

theorem cubicThetaProjectedDirichlet_initial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : 3/2<s.re) :
    cubicThetaProjectedDirichlet g hc rev k s=
      cubicThetaDirichlet (fun n => theta (cubicThetaCircleOrder rev k) n*
        cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
          (cubicThetaPrimaryDualCenter g) n) (2*s-1) := by
  obtain ⟨h₁,h₂⟩ := cubicThetaAngular_initial_gamma hs k
  rw [cubicThetaProjectedDirichlet,cubicThetaProjectedAngularCompleted_initial g hc rev hk hs,
    ←mul_assoc,mul_comm (cubicThetaAngularUncompletion (g 1 0) k s),
    cubicThetaAngular_completion_cancel hc k s h₁ h₂,one_mul]

theorem cubicThetaSelectedDirichlet_initial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : 3/2<s.re) :
    cubicThetaSelectedDirichlet g hc rev k s=
      cubicThetaDirichlet (fun n => theta (cubicThetaCircleOrder (!rev) k) n*
        cubicThetaCoefficientTwist cubicThetaSelectedCoefficient
          (cubicThetaPrimaryCuspCenter g) n) (2*s-1) := by
  obtain ⟨h₁,h₂⟩ := cubicThetaAngular_initial_gamma hs k
  rw [cubicThetaSelectedDirichlet,cubicThetaSelectedAngularCompleted_initial g hc rev hk hs,
    ←mul_assoc,mul_comm (cubicThetaAngularUncompletion (g 1 0) k s),
    cubicThetaAngular_completion_cancel hc k s h₁ h₂,one_mul]

end CubicFirstMoment

end

end OAI
