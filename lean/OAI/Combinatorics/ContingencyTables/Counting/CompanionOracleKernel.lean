import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleRational
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleBudget
import OAI.Combinatorics.ContingencyTables.Transport.RationalWalks

namespace OAI

/-! # The actual rational transition and finite walk of the companion evaluator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def oracleProposalRat (d : ℕ) : ℚ := 1/(2:ℚ)^Nat.clog 2 (8*d)

def oracleMove (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v w : Grid (I := Fin (dimension A)) K) : ℚ :=
  if Neighbor v w then oracleProposalRat A.d*min 1
    (rationalGridWeight A C a z w/rationalGridWeight A C a z v) else 0

def oracleTransition (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v w : Grid (I := Fin (dimension A)) K) : ℚ :=
  oracleMove A C a z v w+if v=w then 1-∑ b,oracleMove A C a z v b else 0

lemma oracleMove_cast (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v w : Grid (I := Fin (dimension A)) K) :
    (oracleMove A C a z v w:ℝ)=
      MetropolisChain.move (gridWeight A C a z) Neighbor (binProposal A.d) v w := by
  unfold oracleMove MetropolisChain.move
  split_ifs
  · simp only [Rat.cast_mul,Rat.cast_min,Rat.cast_one,Rat.cast_div,
      rationalGridWeight_cast,oracleProposalRat,binProposal,Rat.cast_pow,Rat.cast_ofNat]
  · exact Rat.cast_zero

theorem oracleTransition_cast (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v w : Grid (I := Fin (dimension A)) K) :
    (oracleTransition A C a z v w:ℝ)=(oracleChain A C a z hK).P v w := by
  unfold oracleTransition
  dsimp only [oracleChain,MetropolisChain.chain,FiniteChain.ofMoves]
  by_cases hvw : v=w <;>
    simp only [hvw,ite_true,ite_false,Rat.cast_add,Rat.cast_sub,Rat.cast_sum,
      Rat.cast_one,Rat.cast_zero,oracleMove_cast]

def oracleTransitionLaw (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    RationalLaw (Grid (I := Fin (dimension A)) K) where
  mass := oracleTransition A C a z v
  nonnegative := fun w => by
    have hh := (oracleChain A C a z hK).nonnegative v w
    rw [←oracleTransition_cast A C a z hK] at hh
    exact_mod_cast hh
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum,oracleTransition_cast A C a z hK,Rat.cast_one]
    exact (oracleChain A C a z hK).stochastic v

def oracleWalkLaw (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    RationalLaw (Grid (I := Fin (dimension A)) K) :=
  walkLaw (oracleTransitionLaw A C a z hK) v n

theorem oracleWalkLaw_cast (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (n : ℕ) (v w : Grid (I := Fin (dimension A)) K) :
    ((oracleWalkLaw A C a z hK v n).mass w:ℝ)=
      ((oracleChain A C a z hK).kernel.power n).P v w := by
  induction n generalizing w with
  | zero =>
    simp only [oracleWalkLaw,walkLaw,pointLaw,FiniteKernel.power,FiniteKernel.identity]
    by_cases hvw : v=w
    · subst w; simp
    · simp [hvw,Ne.symm hvw]
  | succ n ih =>
    change ((∑ b,(oracleWalkLaw A C a z hK v n).mass b*oracleTransition A C a z b w:ℚ):ℝ)=_
    simp only [Rat.cast_sum,Rat.cast_mul,ih,oracleTransition_cast A C a z hK,
      FiniteKernel.power,FiniteKernel.comp,FiniteChain.kernel]

def oracleStationaryLaw (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) : RationalLaw (Grid (I := Fin (dimension A)) K) := by
  let : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  let w := fun v : Grid (I := Fin (dimension A)) K => rationalGridWeight A C a z v
  have hw : ∀ v,0 < w v := rationalGridWeight_positive A C a z
  have hZ : 0 < ∑ v,w v := Finset.sum_pos (fun v _ => hw v) Finset.univ_nonempty
  exact ⟨fun v => w v/∑ b,w b,fun v => (div_pos (hw v) hZ).le,
    by rw [←Finset.sum_div]; exact div_self hZ.ne'⟩

theorem oracleStationaryLaw_cast (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    ((oracleStationaryLaw A C a z hK).mass v:ℝ)=(oracleChain A C a z hK).π v := by
  change ((rationalGridWeight A C a z v/
    ∑ w : Grid (I := Fin (dimension A)) K,rationalGridWeight A C a z w:ℚ):ℝ)=_
  simp only [Rat.cast_div,Rat.cast_sum,rationalGridWeight_cast]
  rfl

/-- The rational finite-walk law inherits the proved source schedule.
No exact real-valued primitive is used to define its transitions. -/
theorem oracleWalkLaw_variation (A : Instance I J) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : (a:ℝ) ≤ height A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    (variation (oracleWalkLaw A C a z hK v (oracleTime A C K Q theta))
      (oracleStationaryLaw A C a z hK):ℝ) ≤ theta/(8*Q) := by
  let P := oracleChain A C a z hK
  let n := oracleTime A C K Q theta
  let delta : ℝ := theta/(8*Q)
  have hpoint (w : Grid (I := Fin (dimension A)) K) :
      |(P.kernel.power n).P v w-P.π w| ≤ P.π w*delta := by
    have hm := oracleChain_scheduled_point_mixing A C a theta
      (by exact_mod_cast hC) (Nat.cast_nonneg _) haH htheta z hz K Q hK hQ hKB hPL hCheeger v w
    change |P.iterate n (P.pointDensity w) v-1| ≤ delta at hm
    rw [←P.kernel_power_density] at hm
    calc
      _ = P.π w*|(P.kernel.power n).P v w/P.π w-1| := by
        calc
          _ = |P.π w*((P.kernel.power n).P v w/P.π w-1)| := by
            congr 1
            field_simp [(P.positive w).ne']
          _ = _ := by rw [abs_mul,abs_of_pos (P.positive w)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (P.positive w).le
  have hsum := Finset.sum_le_sum (fun w (_ : w∈Finset.univ) => hpoint w)
  rw [←Finset.sum_mul,P.normalized,one_mul] at hsum
  unfold variation
  simp only [Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat,
    oracleWalkLaw_cast,oracleStationaryLaw_cast]
  change (∑ w,|(P.kernel.power n).P v w-P.π w|)/2 ≤ delta
  have hd : 0 ≤ delta := by dsimp only [delta]; positivity
  linarith

end

end ContingencyTables.CompanionOracleDensity

end OAI
