import OAI.NumberTheory.CubicMoment.Estimates.ResidueGaussianScale

namespace OAI

/-! The unit phase introduced by a harmonic Gaussian at the self-dual
Eisenstein conductor scale. -/
noncomputable section
namespace CubicFirstMoment

def angularConductorPhase (q : Eisenstein) : ℂ :=
  (-2*(Real.pi:ℂ)*Complex.I*(residueHeckeScale q:ℂ))/star ((q:ℂ)*traceLambda)

def angularConductorPhaseNeg (q : Eisenstein) : ℂ :=
  (-2*(Real.pi:ℂ)*Complex.I*(residueHeckeScale q:ℂ))/((q:ℂ)*traceLambda)

lemma conductor_abs (q : Eisenstein) :
    ‖(q:ℂ)*traceLambda‖ = 2*Real.pi*residueHeckeScale q := by
  have he : ‖(q:ℂ)*traceLambda‖^2 = 3*norm q := by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_mul,traceLambda_normSq]
    change norm q*3 = _
    ring
  have hs := residueHeckeScale_squared q
  have hA : 0 ≤ residueHeckeScale q := by unfold residueHeckeScale; positivity
  apply (sq_eq_sq₀ (_root_.norm_nonneg ((q:ℂ)*traceLambda)) (by positivity)).mp
  calc
    _ = 3*norm q := he
    _ = 4*Real.pi^2*(residueHeckeScale q)^2 := hs.symm
    _ = _ := by ring

lemma angularConductorPhase_norm {q : Eisenstein} (hq : q ≠ 0) :
    ‖angularConductorPhase q‖ = 1 := by
  have hA := residueHeckeScale_pos hq
  have hn : ‖(2:ℂ)‖ = 2 := by norm_num
  unfold angularConductorPhase
  rw [norm_div,norm_mul,norm_mul,norm_mul,norm_neg,hn,
    Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_I,mul_one,
    Complex.norm_real,Real.norm_of_nonneg hA.le,norm_star,conductor_abs]
  exact div_self (by positivity)

lemma angularConductorPhaseNeg_norm {q : Eisenstein} (hq : q ≠ 0) :
    ‖angularConductorPhaseNeg q‖ = 1 := by
  have he : ‖angularConductorPhaseNeg q‖ = ‖angularConductorPhase q‖ := by
    simp only [angularConductorPhaseNeg,angularConductorPhase,norm_div,norm_star]
  rw [he,angularConductorPhase_norm hq]

end CubicFirstMoment

end

end OAI
