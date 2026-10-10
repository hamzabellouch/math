import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTwistedTail

namespace OAI

/-! The natural metaplectic dual cutoff and its exact exponent algebra. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma metaplectic_tail_scale_identity {R X T J : ℝ}
    (hR : 0 < R) (hX : 0 < X) (hT : 0 < T) (hJ : 0 < J)
    (ε σ : ℝ) (m : ℕ) :
    R^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*J^(-(((m:ℝ)-1/2)-σ))*T^(4*m) =
      R^ε*T^2*(R^2*T^4/X)^σ*((R^2*T^4/X)/J)^(((m:ℝ)-1/2)-σ) := by
  let A : ℝ := (m:ℝ)-1/2
  let D : ℝ := R^2*T^4/X
  have hD : 0 < D := by dsimp [D]; positivity
  have hcut : D^σ*(D/J)^(A-σ) = D^A*J^(-(A-σ)) := by
    rw [Real.div_rpow hD.le hJ.le,div_eq_mul_inv,←Real.rpow_neg hJ.le,
      ←mul_assoc,←Real.rpow_add hD]
    congr 2
    ring
  have hdpow : D^A = R^(2*A)*T^(4*A)*X^(-A) := by
    dsimp [D]
    rw [Real.div_rpow (by positivity) hX.le,Real.mul_rpow (by positivity) (by positivity),
      ←Real.rpow_natCast_mul hR.le,←Real.rpow_natCast_mul hT.le,
      div_eq_mul_inv,←Real.rpow_neg hX.le]
    norm_num
  have hTpow : T^(4*A)*T^2 = T^(4*m) := by
    rw [←Real.rpow_two,←Real.rpow_add hT]
    have he : 4*A+2 = ((4*m:ℕ):ℝ) := by dsimp [A]; push_cast; ring
    rw [he,Real.rpow_natCast]
  change R^(ε+2*A)*X^(-A)*J^(-(A-σ))*T^(4*m) = R^ε*T^2*D^σ*(D/J)^(A-σ)
  rw [show R^ε*T^2*D^σ*(D/J)^(A-σ) = R^ε*T^2*(D^σ*(D/J)^(A-σ)) by ring,
    hcut,hdpow,Real.rpow_add hR]
  calc
    _ = (R^ε*R^(2*A)*X^(-A)*J^(-(A-σ)))*(T^(4*A)*T^2) := by rw [hTpow]
    _ = _ := by ring

lemma metaplectic_height_nat_power {T t : ℝ} (hT : 1 ≤ T) (ht : |t| ≤ 2*T) (m : ℕ) :
    (1+|t|)^(4*m) ≤ 3^(4*m)*T^(4*m) := by
  rw [←mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  linarith

/-- The cutoff is independent of t throughout the full dyadic height
range. Constants retain the harmless fixed factor 3^(4m). -/
theorem metaplectic_twisted_tail_natural_cutoff
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    (ℓ : ℤ) (m : ℕ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hm : σ ≤ (m:ℝ)-1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ X J T : ℝ, 0 < X → 0 < J → 1 ≤ T → ∀ t : ℝ, |t| ≤ 2*T →
      ‖∑' nd, metaplecticFarTailTerm a r ℓ (fun x => W x*mellinPhase t x)
          ((m:ℝ)-1/2) X J nd‖ ≤
        C*norm r^ε*T^2*(norm r^2*T^4/X)^σ*
          ((norm r^2*T^4/X)/J)^(((m:ℝ)-1/2)-σ) := by
  obtain ⟨C,hC,hbound⟩ := metaplectic_twisted_tail_bound ha ℓ m W hW hpos hsm hε hσ hm
  refine ⟨C*3^(4*m),mul_nonneg hC (by positivity),?_⟩
  intro r hr hsr X J T hX hJ hT t ht
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hTp : 0 < T := zero_lt_one.trans_le hT
  calc
    _ ≤ C*norm r^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*
        J^(-(((m:ℝ)-1/2)-σ))*(1+|t|)^(4*m) := hbound r hr hsr X J hX hJ t
    _ ≤ C*norm r^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*
        J^(-(((m:ℝ)-1/2)-σ))*(3^(4*m)*T^(4*m)) :=
      mul_le_mul_of_nonneg_left (metaplectic_height_nat_power hT ht m) (by positivity)
    _ = (C*3^(4*m))*(norm r^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*
        J^(-(((m:ℝ)-1/2)-σ))*T^(4*m)) := by ring
    _ = _ := by rw [metaplectic_tail_scale_identity hR hX hTp hJ]; ring

end CubicFirstMoment

end

end OAI
