import OAI.NumberTheory.TotientAsymptotic.CoordinateExponentialCount
import OAI.NumberTheory.TotientAsymptotic.CoordinateErrorAbsorption
import OAI.NumberTheory.TotientAsymptotic.CountingEnvelopeReal

namespace OAI

/-! A uniform exceptional-value bound for a failed weighted-coordinate row.
All hypotheses beyond the actual row failure are explicit numerical budgets. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem coordinate_deviation_count : ∃ C F : ℝ,0 < C ∧ 0 < F ∧
    ∀ X k : ℕ,256 ≤ X → Real.exp (Real.exp 1) ≤ X → 300000000 ≤ B X →
    ∀ ω : ℝ,0 ≤ ω → ω ≤ 1 →
    Real.log (20*B X)+2 ≤ B X/10000 →
    4 ≤ ω^2*B X/(1000000*((k:ℝ)+2)^6) →
    (Real.log (20*B X)+9+F+Real.log (B X+1))*((k:ℝ)+2)^2 ≤ ω*B X/100 →
    3*B X ≤ Real.exp ((coordinateBottom (B X) ω k:ℝ)-1) →
    9*(Real.log (B X+4))^2+6*Real.log (B X+4) ≤ coordinateDecay ω k*B X →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (1+ω)*B X ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X/Real.log X*Real.exp (-coordinateDecay ω k*B X) := by
  obtain ⟨C,D,A,F,hC,hD,hA,hF,hcount⟩ := coordinate_exponential_count
  obtain ⟨E,hE,henv⟩ := counting_envelope_real_bound
  refine ⟨C+(2+D)+A*E*Real.exp (1/3:ℝ)+F,F,by positivity,hF,?_⟩
  intro X k hX hx hB ω hω hω1 hlog hlarge hbudget hsize habsorb Q hQ
  let b := B X
  let δ := coordinateDecay ω k
  let L := coordinateBottom b ω k
  let J := countingDyadicIndex X
  have hX4 : (4:ℝ) ≤ X := by exact_mod_cast (show 4 ≤ X by omega)
  have hX1 : (1:ℝ) < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX1
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hc := coordinate_cutoff_bounds hB hω hω1 hF.le hlog hlarge hbudget
  have hJ := counting_dyadic_index_bounds hX4
  have htop : Real.exp (bootstrapTop b) ≤ Real.log X/(20*b) := by
    have hh := hc.2.2.2.2.1
    dsimp only [b]
    simpa only [B,Real.exp_log hlogX] using hh
  have hmain := hcount X k (bootstrapTop b) L J hX hx (by dsimp [b] at hb; linarith)
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 htop hJ.1 hJ.2.1 ω hω hω1
    hc.2.2.2.2.2.1 hbudget hc.2.2.2.2.2.2 Q hQ
  have hδ := coordinate_decay_bounds (k:=k) hω hω1
  have hz : (X:ℝ)/Real.log X*Real.exp (-δ*b) = X*Real.exp (-(1+δ)*b) := by
    rw [log_normalized_exponential hX1]
    dsimp [b]
    congr 2
    ring
  have hfirst := coordinate_power_contribution hC.le hX1 hb hδ.2.1
  have hsq := loglog_cutoff_reciprocal hc.1 hsize
  have hsquare := coordinate_square_contribution hD.le hX1 hb (show b=B X from rfl)
    (show δ ≤ 1 by linarith only [hδ.2.1])
    (show (0:ℝ) ≤ (loglogCutoff L+1:ℕ) by positivity) hsq
  have hpoly := counting_normality_polynomial hX4 hb
  have henvX := henv X hX4
  have henvpoly : dyadicTotientEnvelope J*((B (2*X))^5*(1+Real.log J)) ≤
      E*Real.exp (9*(Real.log (b+4))^2)*(b+4)^6 := by
    apply mul_le_mul henvX hpoly
    · have hj1 : (1:ℝ) ≤ J := by exact_mod_cast hJ.1
      have hlogJ : 0 ≤ Real.log J := Real.log_nonneg hj1
      have hb2 : 0 ≤ B (2*X) := by
        have hmono : B X ≤ B (2*X) := Real.log_le_log hlogX
          (Real.log_le_log (by positivity) (by linarith : (X:ℝ) ≤ 2*X))
        exact hb.trans hmono
      positivity
    · positivity
  have hnormal := coordinate_normality_factor hb hω hω1 hlarge
  rw [coordinate_decay_identity] at hnormal
  have hthird : A*dyadicTotientEnvelope J*X/Real.log X*(B (2*X))^5*(1+Real.log J)*
      (Real.log (loglogCutoff L))^(-1/6:ℝ) ≤
      (A*E*Real.exp (1/3:ℝ))*(X/Real.log X*Real.exp (-δ*b)) := by
    have he := coordinate_bootstrap_absorption hb habsorb
    calc
      _ = (A*(X/Real.log X))*(dyadicTotientEnvelope J*((B (2*X))^5*(1+Real.log J)))*
          (Real.log (loglogCutoff L))^(-1/6:ℝ) := by ring
      _ ≤ (A*(X/Real.log X))*(E*Real.exp (9*(Real.log (b+4))^2)*(b+4)^6)*
          (Real.exp (1/3:ℝ)*Real.exp (-2*δ*b)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left henvpoly (by positivity)
        · exact hnormal
        · positivity
        · positivity
      _ = (A*E*Real.exp (1/3:ℝ))*(X/Real.log X)*
          ((b+4)^6*Real.exp (9*(Real.log (b+4))^2)*Real.exp (-2*δ*b)) := by ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he
          (show 0 ≤ (A*E*Real.exp (1/3:ℝ))*(X/Real.log X) by positivity)
  have hfourth : F*X*Real.exp (-(1+ω/2)*b) ≤ F*(X/Real.log X*Real.exp (-δ*b)) := by
    rw [hz]
    have he : -(1+ω/2)*b ≤ -(1+δ)*b := by nlinarith only [mul_le_mul_of_nonneg_right hδ.2.2 hb]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
      (show 0 ≤ F*X by positivity)
  have hh := add_le_add (add_le_add (add_le_add hfirst hsquare) hthird) hfourth
  apply hmain.trans
  convert hh using 1
  dsimp [b,L,J,δ]
  ring

end TotientAsymptotic

end

end OAI
