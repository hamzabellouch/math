import OAI.NumberTheory.TotientAsymptotic.GridExponentEnvelope

namespace OAI

/-! Count a weighted-coordinate violation, allowing all short and small-coordinate tails. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem full_coordinate_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ X k K L : ℕ,4 ≤ X → 1 ≤ B X → 3 ≤ L → L ≤ K →
    (K:ℝ) ≤ B X+2 → Real.exp K ≤ Real.log X/(20*B X) →
    ∀ T : ℝ,((L:ℝ)+1)*(k:ℝ)^2 < T → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
      (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧
      SquarefreeAbove v (loglogCutoff L) ∧ SquarefreeAbove n (loglogCutoff L) ∧
      (∀ p ∈ n.primeFactors,IsNormalPrime (loglogCutoff L) p) ∧
      T ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X*k*(K+1:ℕ)^k*Real.exp
      (-T+(B X+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*B (loglogCutoff L)+
        D*((k:ℝ)+2)^2+((k:ℝ)+2)^3*Real.sqrt (B (loglogCutoff L)*K)) := by
  classical
  obtain ⟨C,D,hC,hD,hcount⟩ := positive_grid_count
  refine ⟨C,D,hC,hD,?_⟩
  intro X k K L hX hBX hL hLK hK hbudget T hT Q hQ
  let U := T-((L:ℝ)+1)*(k:ℝ)^2
  let W := -T+(B X+L+6-K)*(k:ℝ)^2+((k:ℝ)+2)^2*B (loglogCutoff L)+
    D*((k:ℝ)+2)^2+((k:ℝ)+2)^3*Real.sqrt (B (loglogCutoff L)*K)
  let F := fun r : ℕ => Q.filter (fun v => ∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
    (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧
    SquarefreeAbove v (loglogCutoff L) ∧ SquarefreeAbove n (loglogCutoff L) ∧
    (∀ p ∈ n.primeFactors,IsNormalPrime (loglogCutoff L) p) ∧
    (∀ j : Fin r,(L:ℝ)+1 ≤ B (fordPrime n (j.val+1))) ∧
    U ≤ ∑ j : Fin r,a (j.val+1)*fordPrimeCoordinate n (j.val+1))
  have hcover : Q ⊆ (Finset.Icc 1 k).biUnion F := by
    intro v hv
    obtain ⟨n,hn,hφ,hvX,hΩ,hsqv,hsqn,hnorm,hscore⟩ := hQ v hv
    obtain ⟨r,hr0,hr,hpositive,hprefix⟩ := coordinate_active_prefix_score hL hT hscore
    exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_Icc.mpr ⟨hr0,hr⟩,
      Finset.mem_filter.mpr ⟨hv,n,hn,hφ,hvX,hΩ,hsqv,hsqn,hnorm,hpositive,hprefix⟩⟩
  have hBS : 0 ≤ B (loglogCutoff L) := by
    have hh := (loglogCutoff_bounds (show (2:ℝ) ≤ L by exact_mod_cast (show 2 ≤ L by omega))).2.1
    have hl : (3:ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hF (r : ℕ) (hr : r ∈ Finset.Icc 1 k) :
      ((F r).card:ℝ) ≤ C*X*(K+1:ℕ)^k*Real.exp W := by
    obtain ⟨hr0,hrk⟩ := Finset.mem_Icc.mp hr
    have hh := hcount X r K L hX hBX hr0 hL hLK hK hbudget U (F r)
      (fun v hv => (Finset.mem_filter.mp hv).2)
    have he := grid_exponent_envelope (T:=T) hrk hD.le hBS hK
    have hexp := Real.exp_le_exp.mpr he
    have hpow : (((K+1:ℕ)^r):ℝ) ≤ ((K+1:ℕ)^k:ℝ) :=
      by exact_mod_cast (Nat.pow_le_pow_right (n:=K+1) (by omega) hrk)
    apply hh.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ C*X)
    · exact hexp
    · positivity
    · positivity
  calc
    _ ≤ (((Finset.Icc 1 k).biUnion F).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ r ∈ Finset.Icc 1 k,((F r).card:ℝ) := by exact_mod_cast (Finset.card_biUnion_le :
      ((Finset.Icc 1 k).biUnion F).card ≤ ∑ r ∈ Finset.Icc 1 k,(F r).card)
    _ ≤ ∑ _r ∈ Finset.Icc 1 k,C*X*(K+1:ℕ)^k*Real.exp W := Finset.sum_le_sum hF
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Icc]; push_cast; ring

end TotientAsymptotic

end

end OAI
