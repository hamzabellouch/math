import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Perturbation
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.ClockWeightedBound

namespace OAI

/-! A block estimate retaining the cancellation in the effective energy.
It is needed when the third-order gadget's coupling exceeds its low block. -/

noncomputable section
namespace ContinuumCoulomb.Perturbation
open scoped InnerProductSpace

variable {L H : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem sharp_lowBlockEnergy_lower (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g d m η μ : ℝ}
    (hd : 0 ≤ d) (hm : 0 ≤ m) (_hη : 0 ≤ η) (hsmall : 2*(d+m) ≤ g)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ)
    (hgap : ∀ q, g*‖q‖^2 ≤ penaltyForm A q)
    (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖)
    (hD : ∀ q, |⟪q,D q⟫_ℝ| ≤ d*‖q‖^2)
    (hμ : μ ≤ m) (hmin : ∀ p, μ*‖p‖^2 ≤ effectiveForm C T B p)
    (p : L) (q : H) :
    -2*(d+m)*η^2*‖p‖^2 ≤ lowBlockEnergy C A D B p q-μ*(‖p‖^2+‖q‖^2) := by
  have hi := penalty_square_identity A T B hAT hAsymm p q (by norm_num : (1:ℝ) ≠ 0)
  simp only [one_mul,inv_one,one_smul] at hi
  have hnorm := norm_add_sq_two (q+T (B p)) (-(T (B p)))
  simp only [add_neg_cancel_right,norm_neg] at hnorm
  have ht := pow_le_pow_left₀ (norm_nonneg _) (hTB p) 2
  rw [mul_pow] at ht
  have hq : ‖q‖^2 ≤ 2*‖q+T (B p)‖^2+2*η^2*‖p‖^2 := by linarith
  have hqp := mul_le_mul_of_nonneg_left hq (add_nonneg hd hm)
  have hg := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖q+T (B p)‖)
  have hmup := mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖q‖)
  have hminp := hmin p
  have hdq := (abs_le.mp (hD q)).1
  have hgapq := hgap (q+T (B p))
  unfold effectiveForm at hminp
  unfold lowBlockEnergy blockEnergy
  nlinarith

theorem sharp_lowBlockRayleigh_lower (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g d m η μ : ℝ}
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hη : 0 ≤ η) (hsmall : 2*(d+m) ≤ g)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ)
    (hgap : ∀ q, g*‖q‖^2 ≤ penaltyForm A q)
    (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖)
    (hD : ∀ q, |⟪q,D q⟫_ℝ| ≤ d*‖q‖^2)
    (hμ : μ ≤ m) (hmin : ∀ p, μ*‖p‖^2 ≤ effectiveForm C T B p)
    (p : L) (q : H) (hpq : 0 < ‖p‖^2+‖q‖^2) :
    μ-2*(d+m)*η^2 ≤ lowBlockRayleigh C A D B p q := by
  have h := sharp_lowBlockEnergy_lower C A T D B hd hm hη hsmall hAT hAsymm hgap hTB hD hμ hmin p q
  unfold lowBlockRayleigh
  apply (le_div_iff₀ hpq).mpr
  have hnonneg : 0 ≤ 2*(d+m)*η^2*‖q‖^2 := by positivity
  nlinarith

theorem sharp_lowBlockRayleigh_trial_upper (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {d m η μ : ℝ} (hd : 0 ≤ d) (hm : 0 ≤ m) (_hη : 0 ≤ η)
    (hAT : ∀ x, A (T x) = x) (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖)
    (hD : ∀ q, |⟪q,D q⟫_ℝ| ≤ d*‖q‖^2)
    (hμ : -m ≤ μ) (p : L) (hp : ‖p‖ = 1) (he : effectiveForm C T B p = μ) :
    lowBlockRayleigh C A D B p (-(T (B p))) ≤ μ+(d+m)*η^2 := by
  have ht := pow_le_pow_left₀ (norm_nonneg _) (hTB p) 2
  rw [hp,mul_one] at ht
  have hi := blockEnergy_trial_identity A T D B hAT p
  have hdq := (abs_le.mp (hD (-(T (B p))))).2
  simp only [norm_neg] at hdq
  have hmup := mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖T (B p)‖)
  have herr := mul_le_mul_of_nonneg_left ht (add_nonneg hd hm)
  have hextra : 0 ≤ (d+m)*η^2*‖T (B p)‖^2 := by positivity
  unfold lowBlockRayleigh lowBlockEnergy
  rw [hp,norm_neg]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 1^2+‖T (B p)‖^2)).mpr
  unfold effectiveForm at he
  nlinarith

theorem sharp_lowBlockBottom (C : L →L[ℝ] L) (A T D : H →L[ℝ] H)
    (B : L →L[ℝ] H) {g d m η μ : ℝ}
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hη : 0 ≤ η) (hsmall : 2*(d+m) ≤ g)
    (hAT : ∀ x, A (T x) = x)
    (hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ)
    (hgap : ∀ q, g*‖q‖^2 ≤ penaltyForm A q)
    (hTB : ∀ p, ‖T (B p)‖ ≤ η*‖p‖)
    (hD : ∀ q, |⟪q,D q⟫_ℝ| ≤ d*‖q‖^2)
    (hμ : |μ| ≤ m) (hmin : ∀ p, μ*‖p‖^2 ≤ effectiveForm C T B p)
    (p₀ : L) (hp₀ : ‖p₀‖ = 1) (he : effectiveForm C T B p₀ = μ) :
    |lowBlockBottom C A D B-μ| ≤ 2*(d+m)*η^2 := by
  have hμb := abs_le.mp hμ
  have hnon : 0 < ‖p₀‖^2+‖-(T (B p₀))‖^2 := by rw [hp₀]; positivity
  have hn : {e | ∃ (p : L) (q : H), 0 < ‖p‖^2+‖q‖^2 ∧
      e = lowBlockRayleigh C A D B p q}.Nonempty :=
    ⟨_,p₀,-(T (B p₀)),hnon,rfl⟩
  have hl (e : ℝ) (he : ∃ (p : L) (q : H), 0 < ‖p‖^2+‖q‖^2 ∧
      e = lowBlockRayleigh C A D B p q) : μ-2*(d+m)*η^2 ≤ e := by
    obtain ⟨p,q,hpq,rfl⟩ := he
    exact sharp_lowBlockRayleigh_lower C A T D B hd hm hη hsmall hAT hAsymm hgap hTB hD hμb.2 hmin p q hpq
  have hb : BddBelow {e | ∃ (p : L) (q : H), 0 < ‖p‖^2+‖q‖^2 ∧
      e = lowBlockRayleigh C A D B p q} := ⟨_,hl⟩
  have hlow : μ-2*(d+m)*η^2 ≤ lowBlockBottom C A D B := le_csInf hn hl
  have hu : lowBlockBottom C A D B ≤ μ+(d+m)*η^2 :=
    (csInf_le hb ⟨p₀,-(T (B p₀)),hnon,rfl⟩).trans
      (sharp_lowBlockRayleigh_trial_upper C A T D B hd hm hη hAT hTB hD hμb.1 p₀ hp₀ he)
  have herr : 0 ≤ (d+m)*η^2 := by positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end ContinuumCoulomb.Perturbation

end

end OAI
