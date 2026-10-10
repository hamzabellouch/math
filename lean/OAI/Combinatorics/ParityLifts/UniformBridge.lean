import OAI.Combinatorics.ParityLifts.UniformCompose

namespace OAI

namespace ParityWL.Complexity

/-- A single parameter-oblivious finite machine meets every positive rate. Its
input polynomial degree is also fixed before choosing the rate. -/
theorem uniform_reduction (c : Convention) (i : Implementation) (M : Machine) (f g : ℕ → ℝ)
    (hlim : Filter.Tendsto (fun k : ℕ => g k/k) Filter.atTop (nhds 0))
    (hM : UniformWLBound M c i f g) :
    ∃ d : ℕ, ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
      SATTimeBound (raceCode (trialCode c M).decision).decision
        (fun N L => C*(L+1 : ℝ)^d*2^(ε*N)) := by
  obtain ⟨D,P,_,_,hTrial⟩ := trialCode_rate
  obtain ⟨A,hA,d,hd,hRace⟩ := raceDecision_bound (trialCode c M).decision
  refine ⟨(2*trialNormalizeProgram.degree+3)*d,?_⟩
  intro ε hε
  let η : ℝ := ε/(4*(d+1))
  have hη : 0<η := by dsimp only [η]; positivity
  obtain ⟨j,hj,k,hk,hSmall⟩ := uniform_rate_parameters D P g hM.2.1 hlim η hη
  have hkt : k ≤ bagParameter c k := by cases c <;> simp [bagParameter]
  have hbase := hSmall (bagParameter c k) hkt
  let r : ℝ := (D : ℝ)/j+(P : ℝ)*(g k+1)*leafSlope (bagParameter c k) (12*j)+η
  have hr : 0 ≤ r := by
    have hg := hM.2.1 k
    have hs := leafSlope_nonneg (bagParameter c k) (12*j)
    dsimp only [r]
    positivity
  have hrate : r*d ≤ ε := by
    have heq : η*(4*(d+1))=ε := by
      dsimp only [η]
      exact div_mul_cancel₀ _ (by positivity)
    have hb : r ≤ 2*η := by dsimp only [r]; linarith
    have hp := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α:=ℝ) d)
    nlinarith
  obtain ⟨C,hC,hRun⟩ := hTrial c i M f g hM j hj k hk η hη
  let K : ℝ := A*(C+j+k+3)^d
  have hK : 0<K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro N F
  have hall : ∀ j : ℕ, 0<j → ∀ k : ℕ, 4 ≤ k →
      ∃ s b, Emits (trialCode c M).decision (trialInput j k (encodeFormula F)) s b ∧
        (b=true↔F.Satisfiable) := by
    intro j hj k hk
    obtain ⟨C,_,hh⟩ := hTrial c i M f g hM j hj k hk 1 (by norm_num)
    obtain ⟨s,b,hs,hb,_⟩ := hh F
    exact ⟨s,b,hs,hb⟩
  obtain ⟨s,b,hs,hb,ht⟩ := hRun F
  obtain ⟨t,a,ha,hans,htime⟩ := hRace (encodeFormula F) (fun b => b=true↔F.Satisfiable)
    hall j k s hj hk b hs
  refine ⟨t,a,ha,hans,?_⟩
  have hnum := trial_race_numeric A C r d (2*trialNormalizeProgram.degree+2)
    j k (encodeFormula F).length N s t hA.le hC.le hr ht htime
  apply hnum.trans
  change K*_*(2 : ℝ)^((r*d)*N) ≤ K*_*(2 : ℝ)^(ε*N)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg N))

end ParityWL.Complexity

end OAI
