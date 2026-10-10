import OAI.NumberTheory.TotientAsymptotic.BootstrapGridError

namespace OAI

/-! A power-saving two-coordinate exception, with fixed explicit cutoffs. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

/-- The regular part of Ford Lemma 4.2 at the single parameter needed to
start the global counting bootstrap. -/
theorem bootstrap_regular_violation : ∃ C : ℝ,0 < C ∧ ∀ᶠ X : ℕ in atTop,
    ∀ Q : Finset ℕ,
    (∀ v ∈ Q,v ≤ X ∧ CountingRegular (loglogCutoff (bootstrapBottom (B X))) X v ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (101/100:ℝ)*B X < a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2) →
    (Q.card:ℝ) ≤ C*X*(Real.log X)^(-201/200:ℝ) := by
  obtain ⟨C,D,hC,hD,hcount⟩ := two_coordinate_violation_count
  refine ⟨C,hC,?_⟩
  have ht : Tendsto (fun X : ℕ => B X) atTop atTop := B_tendsto.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_bootstrap_log_budget D),
    ht.eventually (eventually_ge_atTop 300000000),eventually_ge_atTop (4:ℕ)] with X hbudget hb hX
  let b := B X
  let K := bootstrapTop b
  let L := bootstrapBottom b
  change 300000000 ≤ b at hb
  have hb0 : 0 ≤ b := by linarith
  have hlb : 0 ≤ Real.log (b+1) := Real.log_nonneg (by linarith)
  have hl : Real.log (20*b)+2 ≤ b/10000 := by
    change 10000*(Real.log (20*b)+|D|+Real.log (b+1)+10) ≤ b at hbudget
    nlinarith only [hbudget,abs_nonneg D,hlb]
  have hc := bootstrap_cutoff_bounds hb hl
  change 2 ≤ L ∧ L ≤ K ∧ (L:ℝ)+2 ≤ b/2 ∧ (K:ℝ) ≤ b ∧
    b-Real.log (20*b)-2 ≤ K ∧ Real.exp K ≤ Real.exp b/(20*b) at hc
  obtain ⟨hL,hLK,hLB,hKB,hKlow,hcut⟩ := hc
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have he : Real.exp b=Real.log X := Real.exp_log hlogX
  rw [he] at hcut
  have hS := loglogCutoff_bounds (by exact_mod_cast hL : (2:ℝ) ≤ L)
  have hS0 : 0 ≤ B (loglogCutoff L) := by
    have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
    linarith only [hS.2.1,hLR]
  have hSu : B (loglogCutoff L) ≤ b/100000000 :=
    hS.2.2.1.trans (Nat.floor_le (by positivity : 0 ≤ b/100000000))
  have herr := bootstrap_grid_exponential (by linarith : 1 ≤ b) hS0 hSu hKB hKlow hbudget
  intro Q hQ
  have hh := hcount X K L (1/100) hX (by change 12 ≤ b; linarith) (by norm_num)
    hL hLK hLB (by linarith) hcut Q (by
      intro v hv
      obtain ⟨hvX,hreg,n,hn,hφ,hbad⟩ := hQ v hv
      refine ⟨hvX,hreg,n,hn,hφ,?_⟩
      convert hbad using 1
      ring)
  have hconst : (1:ℝ)+1/100=101/100 := by norm_num
  rw [hconst] at hh
  calc
    _ ≤ C*X*(K+1:ℕ)^2*Real.exp (-(101/100:ℝ)*b+(3/2:ℝ)*(b+5-K)+
        4*B (loglogCutoff L)+5*D+8*Real.sqrt (B (loglogCutoff L)*K)) := hh
    _ = C*X*(((K+1:ℕ):ℝ)^2*Real.exp (-(101/100:ℝ)*b+(3/2:ℝ)*(b+5-K)+
        4*B (loglogCutoff L)+5*D+8*Real.sqrt (B (loglogCutoff L)*K))) := by ring
    _ ≤ C*X*Real.exp (-(201/200:ℝ)*b) := mul_le_mul_of_nonneg_left herr (by positivity)
    _ = _ := by rw [Real.rpow_def_of_pos hlogX]; dsimp [b,B]; congr 2; ring

end TotientAsymptotic

end

end OAI
