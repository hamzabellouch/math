import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedLow

namespace OAI

/-! Exact exponent bookkeeping for truncating the metaplectic dual
series. The cutoff is in the actual norm N(d³ν). -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def metaplecticDualNorm (nd : MetaplecticDualArgument × PrimaryArgument) : ℝ :=
  norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)

lemma metaplecticDualNorm_pos (nd : MetaplecticDualArgument × PrimaryArgument) :
    0 < metaplecticDualNorm nd :=
  mul_pos (pow_pos (norm_pos_of_ne_zero (primary_ne_zero nd.2.property)) _)
    (Complex.normSq_pos.mpr (metaplecticFrequency_ne_zero nd.1))

lemma metaplectic_dual_weight_split
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein)
    (σ A : ℝ) (nd : MetaplecticDualArgument × PrimaryArgument) :
    metaplecticCoefficientMassTerm a r A nd.1*norm nd.2^(-5/2-3*A) =
      (metaplecticCoefficientMassTerm a r σ nd.1*norm nd.2^(-5/2-3*σ))*
        metaplecticDualNorm nd^(-(A-σ)) := by
  let D := norm nd.2
  let P := Complex.normSq (metaplecticFrequency nd.1)
  let H := ‖a r nd.1*metaplecticLocalCoefficient r nd.1‖
  have hD : 0 < D := norm_pos_of_ne_zero (primary_ne_zero nd.2.property)
  have hP : 0 < P := Complex.normSq_pos.mpr (metaplecticFrequency_ne_zero nd.1)
  change H/P^(1+A)*D^(-5/2-3*A) = (H/P^(1+σ)*D^(-5/2-3*σ))*(D^3*P)^(-(A-σ))
  have hpow : (D^3*P)^(-(A-σ)) = D^(-3*(A-σ))*P^(-(A-σ)) := by
    rw [Real.mul_rpow (pow_nonneg hD.le _) hP.le,←Real.rpow_natCast_mul hD.le]
    congr 2
    norm_num
    ring
  rw [hpow]
  have hPe : P^(-(1+A)) = P^(-(1+σ))*P^(-(A-σ)) := by
    rw [←Real.rpow_add hP]
    congr 1
    ring
  have hDe : D^(-5/2-3*A) = D^(-5/2-3*σ)*D^(-3*(A-σ)) := by
    rw [←Real.rpow_add hD]
    congr 1
    ring
  simp only [div_eq_mul_inv] at hDe
  simp only [div_eq_mul_inv,←Real.rpow_neg hP.le]
  rw [hPe,hDe]
  ring

lemma metaplectic_dual_weight_tail
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein)
    {σ A J : ℝ} (hA : σ ≤ A) (hJ : 0 < J)
    (nd : MetaplecticDualArgument × PrimaryArgument) (hcut : J ≤ metaplecticDualNorm nd) :
    metaplecticCoefficientMassTerm a r A nd.1*norm nd.2^(-5/2-3*A) ≤
      J^(-(A-σ))*(metaplecticCoefficientMassTerm a r σ nd.1*norm nd.2^(-5/2-3*σ)) := by
  rw [metaplectic_dual_weight_split]
  have hpow := Real.rpow_le_rpow_of_nonpos hJ hcut (show -(A-σ) ≤ 0 by linarith)
  have hn : 0 ≤ metaplecticCoefficientMassTerm a r σ nd.1*norm nd.2^(-5/2-3*σ) :=
    mul_nonneg (metaplecticCoefficientMassTerm_nonneg a r σ nd.1)
      (Real.rpow_nonneg (norm_nonneg nd.2) _)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hpow hn

def metaplecticFarTailTerm (a : Eisenstein → MetaplecticDualArgument → ℂ)
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (A X J : ℝ)
    (nd : MetaplecticDualArgument × PrimaryArgument) : ℂ :=
  if J < metaplecticDualNorm nd then metaplecticDualTerm a r ℓ W A X nd else 0

/-- The tail costs the cutoff power while retaining only the already
summable small-line coefficient mass. -/
theorem metaplecticFarTail_norm_bound
    (a : Eisenstein → MetaplecticDualArgument → ℂ) {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) {σ A X J C M : ℝ}
    (hσ : 0 < σ) (hA : σ ≤ A) (hX : 0 < X) (hJ : 0 < J) (hC : 0 ≤ C)
    (hW : ∀ v : ℝ, 0 < v → ‖metaplecticTransform ℓ W A v‖ ≤ C*v^(-A))
    (hm : Summable (metaplecticCoefficientMassTerm a r σ))
    (hM : (∑' n, metaplecticCoefficientMassTerm a r σ n) ≤ M) :
    ‖∑' nd, metaplecticFarTailTerm a r ℓ W A X J nd‖ ≤
      (C*((2*Real.pi)^(-4*A)*X^(-A)*norm r^(2*A)))*J^(-(A-σ))*M*
        (∑' d : PrimaryArgument, norm d^(-5/2-3*σ)) := by
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  let K := C*((2*Real.pi)^(-4*A)*X^(-A)*norm r^(2*A))*J^(-(A-σ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let dweight : PrimaryArgument → ℝ := fun d => norm d^(-5/2-3*σ)
  have hd : Summable dweight := by
    dsimp only [dweight]
    convert primary_norm_rpow_summable (show 1 < 5/2+3*σ by linarith) using 1
    ext d
    congr 1
    ring
  have hd0 (d : PrimaryArgument) : 0 ≤ dweight d :=
    Real.rpow_nonneg (norm_nonneg d) _
  have hprod := hm.mul_of_nonneg hd (metaplecticCoefficientMassTerm_nonneg a r σ) hd0
  have hs := (hm.hasSum.mul hd.hasSum hprod).mul_left K
  have hb : ‖∑' nd, metaplecticFarTailTerm a r ℓ W A X J nd‖ ≤
      K*((∑' n, metaplecticCoefficientMassTerm a r σ n)*(∑' d, dweight d)) := by
    apply tsum_of_norm_bounded hs
    intro nd
    by_cases hcut : J < metaplecticDualNorm nd
    · simp only [metaplecticFarTailTerm,hcut,ite_true]
      have hn := metaplecticDualTerm_norm_le a hr ℓ W hX hC hW nd
      have ht := metaplectic_dual_weight_tail a r hA hJ nd hcut.le
      apply hn.trans
      calc
        _ = (C*((2*Real.pi)^(-4*A)*X^(-A)*norm r^(2*A)))*
            (metaplecticCoefficientMassTerm a r A nd.1*norm nd.2^(-5/2-3*A)) := by ring
        _ ≤ (C*((2*Real.pi)^(-4*A)*X^(-A)*norm r^(2*A)))*
            (J^(-(A-σ))*(metaplecticCoefficientMassTerm a r σ nd.1*norm nd.2^(-5/2-3*σ))) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
        _ = _ := by dsimp [K,dweight]; ring
    · simp only [metaplecticFarTailTerm,hcut,ite_false,norm_zero]
      exact mul_nonneg hK (mul_nonneg (metaplecticCoefficientMassTerm_nonneg a r σ nd.1) (hd0 nd.2))
  apply hb.trans
  calc
    _ ≤ K*(M*(∑' d, dweight d)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hM (tsum_nonneg hd0)) hK
    _ = _ := by dsimp [K,dweight]; ring

end CubicFirstMoment

end

end OAI
