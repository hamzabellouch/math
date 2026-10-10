import OAI.NumberTheory.DirichletL.Energy.CanonicalReferencePaid

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyChildEnvelopeFitting
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentSecondNonexceptionalChosenBlock
local notation "O" => HeckeFamily.O

lemma radical_product_power (R C:Ideal O)(hR:R≠0)(hC:C≠0)
    (Z BR BC ε:ℝ)(hZ:0<Z)(hε:0≤ε)
    (hRN:(R.absNorm:ℝ)≤Z^BR)(hCN:(C.absNorm:ℝ)≤Z^BC):
    ((R*C).radical.absNorm:ℝ)^ε≤Z^((BR+BC)*ε):=by
  have hRC:R*C≠0:=mul_ne_zero hR hC
  have hr:((R*C).radical.absNorm:ℝ)≤(R*C).absNorm:=by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hRC))
      (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I:=R*C))))
  have hh:(R*C).absNorm≤Z^(BR+BC):=by
    rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
    exact mul_le_mul hRN hCN (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hZ _).le
  rw [Real.rpow_mul hZ.le]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (hr.trans hh) hε

lemma independent_height (v height:ℝ)(hheight:0≤height)(degree:ℕ):
    (1+(|v|+height))^degree≤(1+height)^degree*(1+‖v‖)^(2*degree):=by
  have hh:1+(|v|+height)≤(1+height)*(1+‖v‖):=by
    rw [Real.norm_eq_abs]
    nlinarith [mul_nonneg hheight (abs_nonneg v)]
  have hp:=pow_le_pow_left₀ (by positivity:0≤1+(|v|+height)) hh degree
  rw [mul_pow] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith [norm_nonneg v]:1≤1+‖v‖) (by omega:degree≤2*degree)) (by positivity))

def coefficient {a b:ℝ}(Cc C₀ C₁:ℝ)(p:Profiles a b)(T:Finset (ℕ×ℕ))
    (height:ℝ)(degree:ℕ)(Z exponent:ℝ):ℝ:=
  Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
    (p.control T)^2*(1+height)^degree*Z^exponent

lemma coefficient_nonneg {a b:ℝ}(Cc C₀ C₁:ℝ)(p:Profiles a b)(T:Finset (ℕ×ℕ))
    (height:ℝ)(degree:ℕ)(Z exponent:ℝ)(hC:0≤Cc)(h₀:0≤C₀)(h₁:0≤C₁)
    (hH:0≤height)(hZ:0≤Z):0≤coefficient Cc C₀ C₁ p T height degree Z exponent:=by
  unfold coefficient
  have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile
  positivity

theorem paid_rhs_fit {a b:ℝ}(Cc C₀ C₁:ℝ)(p:Profiles a b)(T:Finset (ℕ×ℕ))
    (R C:Ideal O)(hR:R≠0)(hC:C≠0)(τ:Character)(Q:Ideal O)(dyad:Fin 4→ℤ)
    (v height:ℝ)(degree:ℕ)(Z BR BC εmask exponent loss reference ratio:ℝ)
    (hCc:0≤Cc)(h₀:0≤C₀)(h₁:0≤C₁)(hH:0≤height)(hZ:1≤Z)(hε:0≤εmask)
    (hRN:(R.absNorm:ℝ)≤Z^BR)(hCN:(C.absNorm:ℝ)≤Z^BC)
    (hloss:exponent≤loss)(href:0≤reference)(hratio:0≤ratio):
    Cc*((R*C).radical.absNorm:ℝ)^εmask*(C₀+C₁)*
      diagonalControl (canonicalRadial τ Q dyad).profile*(p.control T)^2*
      (1+(|v|+height))^degree*reference*ratio^((1:ℝ)/6)*Z^exponent≤
    coefficient Cc C₀ C₁ p T height degree Z ((BR+BC)*εmask+loss)*
      reference*ratio^((1:ℝ)/6)*(1+‖v‖)^(2*degree):=by
  have hZ0:0<Z:=zero_lt_one.trans_le hZ
  have hr:=radical_product_power R C hR hC Z BR BC εmask hZ0 hε hRN hCN
  have ht:=independent_height v height hH degree
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ hloss
  have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile
  have hsum:0≤C₀+C₁:=add_nonneg h₀ h₁
  change Cc*((R*C).radical.absNorm:ℝ)^εmask*(C₀+C₁)*
    diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*(p.control T)^2*
    (1+(|v|+height))^degree*reference*ratio^((1:ℝ)/6)*Z^exponent≤_
  calc
    _≤Cc*Z^((BR+BC)*εmask)*(C₀+C₁)*
      diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*(p.control T)^2*
      ((1+height)^degree*(1+‖v‖)^(2*degree))*reference*ratio^((1:ℝ)/6)*Z^loss:=by
        gcongr
    _=_:=by
      unfold coefficient
      rw [Real.rpow_add hZ0]
      ring

end SevenEighths.CenteredMomentEnergyChildEnvelopeFitting

end

end OAI
