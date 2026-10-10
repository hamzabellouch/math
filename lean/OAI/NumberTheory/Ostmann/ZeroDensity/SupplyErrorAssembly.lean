import OAI.NumberTheory.Ostmann.ZeroDensity.ContourPolynomial
import OAI.NumberTheory.Ostmann.ZeroDensity.LiteralSupplyZeros
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimitiveExplicitComparison
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalSupplyDecay
import OAI.NumberTheory.Ostmann.ZeroDensity.SupplyTailDecay

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open Filter Set
open scoped BigOperators Topology ContDiff
namespace Ostmann.ZeroDensity

theorem eventually_totalPrimitiveError_of_truncated_formula {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1)
    (B : ℕ) {C : ℝ} (hC : 0 < C)
    (hformula : ∀ (Q : ℕ) (χ : NonprincipalPrimitiveFamily Q) (X T : ℝ),
      Real.exp 2 ≤ X → 2 ≤ T →
      ‖smoothError χ.val.2.val φ X‖ ≤ C*
        ((∑ p ∈ (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 (T+1)).toFinset.filter
          (fun p => (1 : ℝ)/2 ≤ p.re),
          (Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 p : ℝ)*X^p.re/(1+|p.im|)^(B+1))+
          contourRemainder B (χ.val.1.val+1 : ℝ) X T))
    (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 0 < Q → Q ≤ supplyConductorCutoff L →
      totalPrimitiveError Q none φ (supplyPrimeSample L : ℝ) ≤
        (supplyPrimeSample L : ℝ)*Real.exp (-D*L) := by
  let E : ℝ := B+|D|+3
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hE' : (B : ℝ)+(D+1)+1 ≤ E := by dsimp [E]; linarith [le_abs_self D]
  have hpr := eventually_principal_supply_decay hφ hcompact hs (D+1)
  have hz := eventually_uniform_supply_zero_decay_succ (B+2) hE (D+1)
  have hl := eventually_supply_left_edge_decay B (B+2) hE (D+1)
  have ht := eventually_supply_tail_decay B (D+1) E hE'
  have hconst := eventually_constant_exp_decay
    (show (0 : ℝ) < 1+3*C by positivity) D
  filter_upwards [hpr,hz,hl,ht,hconst,
    supplyPrimeSample_tendsto.eventually (eventually_ge_atTop (Real.exp (2 : ℝ)))]
    with L hpr hz hl ht hconst hXlarge
  intro Q hQ hQQ
  have hX : (1 : ℝ) ≤ supplyPrimeSample L :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hXlarge
  have hT : (2 : ℝ) ≤ supplyContourHeight (B+2) E L := by
    exact_mod_cast supplyContourHeight_ge_two (B+2) E L
  have hmain := totalPrimitiveError_le_of_truncated_formula Q hQ φ B hX
    (show (0 : ℝ) ≤ supplyContourHeight (B+2) E L by positivity) hC.le
    (fun χ => hformula Q χ _ _ hXlarge hT)
  have hzero : (∑ z ∈ retainedZeros Q none (1/2)
      ((supplyContourHeight (B+2) E L : ℝ)+1), (supplyPrimeSample L : ℝ)^z.point.re) ≤
        (supplyPrimeSample L : ℝ)*Real.exp (-(D+1)*L) := by
    have heq := congrArg (fun t : ℝ =>
      ∑ z ∈ retainedZeros Q none (1/2) t, (supplyPrimeSample L : ℝ)^z.point.re)
      (show (supplyContourHeight (B+2) E L : ℝ)+1 =
        ((supplyContourHeight (B+2) E L+1 : ℕ) : ℝ) by push_cast; rfl)
    exact heq.trans_le (hz Q hQ hQQ none)
  have hleft := hl Q hQ hQQ
  have htail := ht Q hQ hQQ
  have hrem : (Q : ℝ)^2*contourRemainder B Q (supplyPrimeSample L)
      (supplyContourHeight (B+2) E L) ≤
        2*((supplyPrimeSample L : ℝ)*Real.exp (-(D+1)*L)) := by
    calc
      _ = (Q : ℝ)^2*Real.sqrt (supplyPrimeSample L : ℝ)*
          ((Q : ℝ)*((supplyContourHeight (B+2) E L : ℝ)+2))^B+
        (Q : ℝ)^2*(supplyPrimeSample L : ℝ)*
          ((Q : ℝ)*((supplyContourHeight (B+2) E L : ℝ)+2))^B /
          (supplyContourHeight (B+2) E L : ℝ)^(B+1)*
          (1+Real.log (supplyPrimeSample L : ℝ))^B := by
            unfold contourRemainder
            ring
      _ ≤ _ := by linarith only [hleft,htail]
  have hfinal := mul_le_mul_of_nonneg_left hconst
    (Nat.cast_nonneg (supplyPrimeSample L) : (0 : ℝ) ≤ supplyPrimeSample L)
  calc
    _ ≤ ‖smoothError (1 : DirichletCharacter ℂ 1) φ (supplyPrimeSample L : ℝ)‖+
      C*((∑ z ∈ retainedZeros Q none (1/2)
        ((supplyContourHeight (B+2) E L : ℝ)+1), (supplyPrimeSample L : ℝ)^z.point.re)+
        (Q : ℝ)^2*contourRemainder B Q (supplyPrimeSample L) (supplyContourHeight (B+2) E L)) := hmain
    _ ≤ (supplyPrimeSample L : ℝ)*Real.exp (-(D+1)*L)+
        C*((supplyPrimeSample L : ℝ)*Real.exp (-(D+1)*L)+
        2*((supplyPrimeSample L : ℝ)*Real.exp (-(D+1)*L))) := by gcongr
    _ = (supplyPrimeSample L : ℝ)*((1+3*C)*Real.exp (-(D+1)*L)) := by ring
    _ ≤ _ := hfinal

end Ostmann.ZeroDensity

end

end OAI
