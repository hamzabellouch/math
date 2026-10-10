import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularDirichletContinuation

namespace OAI

/-! The functional equation for the actual continued additive angular Dirichlet series.
Gamma cancellation is required only on the dual side. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaAngularUncompletion (q : Eisenstein) (k : ℕ) (s : ℂ) : ℂ :=
  4*(cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1)*((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ))*
    (Complex.Gamma (s+(k:ℂ)/2+1/6))⁻¹*(Complex.Gamma (s+(k:ℂ)/2-1/6))⁻¹

def cubicThetaAngularCompletion (q : Eisenstein) (k : ℕ) (s : ℂ) : ℂ :=
  (1/4:ℂ)*(cubicThetaLevelScale q:ℂ)^(-(2*s+(k:ℂ)-1))*
    ((2*Real.pi:ℝ):ℂ)^(-(2*s+(k:ℂ)))*
      Complex.Gamma (s+(k:ℂ)/2+1/6)*Complex.Gamma (s+(k:ℂ)/2-1/6)

lemma cubicThetaAngular_completion_cancel {q : Eisenstein} (hq : primary q)
    (k : ℕ) (s : ℂ)
    (hG₁ : Complex.Gamma (s+(k:ℂ)/2+1/6)≠0)
    (hG₂ : Complex.Gamma (s+(k:ℂ)/2-1/6)≠0) :
    cubicThetaAngularCompletion q k s*cubicThetaAngularUncompletion q k s=1 := by
  have hρ : (cubicThetaLevelScale q:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaLevelScale_pos hq).ne'
  have hπ : ((2*Real.pi:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hρp : (cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1)≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hρ)
  have hπp : ((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ))≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
  unfold cubicThetaAngularCompletion cubicThetaAngularUncompletion
  rw [Complex.cpow_neg,Complex.cpow_neg]
  calc
    _ = (((cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1))⁻¹*
          (cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1))*
        ((((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ)))⁻¹*((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ)))*
        (Complex.Gamma (s+(k:ℂ)/2+1/6)*(Complex.Gamma (s+(k:ℂ)/2+1/6))⁻¹)*
        (Complex.Gamma (s+(k:ℂ)/2-1/6)*(Complex.Gamma (s+(k:ℂ)/2-1/6))⁻¹) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hρp,inv_mul_cancel₀ hπp,mul_inv_cancel₀ hG₁,mul_inv_cancel₀ hG₂]; norm_num

lemma cubicThetaAngularDirichletContinuation_factor (q x y : Eisenstein) (rev : Bool)
    (k : ℕ) (s : ℂ) :
    cubicThetaAngularDirichletContinuation q x y rev k s=
      cubicThetaAngularUncompletion q k s*
        cubicThetaLevelAngularCompleted q x y rev k (2*s+(k:ℂ)-1) := rfl

lemma cubicThetaAngularDirichletContinuation_complete {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (rev : Bool) (k : ℕ) (s : ℂ)
    (hG₁ : Complex.Gamma (s+(k:ℂ)/2+1/6)≠0)
    (hG₂ : Complex.Gamma (s+(k:ℂ)/2-1/6)≠0) :
    cubicThetaLevelAngularCompleted q x y rev k (2*s+(k:ℂ)-1)=
      cubicThetaAngularCompletion q k s*cubicThetaAngularDirichletContinuation q x y rev k s := by
  rw [cubicThetaAngularDirichletContinuation_factor,←mul_assoc,
    cubicThetaAngular_completion_cancel hq k s hG₁ hG₂,one_mul]

theorem cubicThetaLevelAngularCompleted_paired {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool) {k : ℕ} (hk : 0<k) (s : ℂ) :
    cubicThetaLevelAngularCompleted q x y rev k (2*s+(k:ℂ)-1)=
      cubicThetaLevelAngularPhase q x rev k*
        cubicThetaLevelAngularCompleted q (-y) (-x) (!rev) k (2*(1-s)+(k:ℂ)-1) := by
  have hpair : q∣9*(-y)*(-x)-1 := by convert hxy using 1; ring
  have H := (cubicThetaLevelAngular_mellin hq (-y) (-x) hpair (!rev) hk
    (2*(1-s)+(k:ℂ)-1)).2
  have he : ((2*k:ℕ):ℂ)-(2*s+(k:ℂ)-1)=2*(1-s)+(k:ℂ)-1 := by push_cast; ring
  rw [cubicThetaLevelAngularCompleted_functional hq x y hxy rev hk,he]
  rw [←H]
  have hz : -(3*((-y:Eisenstein):ℂ)/(q:ℂ))=3*(y:ℂ)/(q:ℂ) := by push_cast; ring
  rw [hz]

theorem cubicThetaAngularDirichletContinuation_functional {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : s.re<5/6+(k:ℝ)/2) :
    cubicThetaAngularDirichletContinuation q x y rev k s=
      cubicThetaAngularUncompletion q k s*cubicThetaLevelAngularPhase q x rev k*
        cubicThetaAngularCompletion q k (1-s)*
          cubicThetaAngularDirichletContinuation q (-y) (-x) (!rev) k (1-s) := by
  have h₁ : 0<(1-s+(k:ℂ)/2+1/6).re := by
    simp only [Complex.add_re,Complex.sub_re,Complex.div_ofNat_re,Complex.natCast_re,Complex.one_re]
    linarith
  have h₂ : 0<(1-s+(k:ℂ)/2-1/6).re := by
    simp only [Complex.add_re,Complex.sub_re,Complex.div_ofNat_re,Complex.natCast_re,Complex.one_re]
    linarith
  rw [cubicThetaAngularDirichletContinuation_factor,
    cubicThetaLevelAngularCompleted_paired hq x y hxy rev hk,
    cubicThetaAngularDirichletContinuation_complete hq (-y) (-x) (!rev) k (1-s)
      (Complex.Gamma_ne_zero_of_re_pos h₁) (Complex.Gamma_ne_zero_of_re_pos h₂)]
  ring

end CubicFirstMoment

end

end OAI
