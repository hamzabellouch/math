import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleMixing
import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleRational
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleKernel

namespace OAI

/-! # Exact rational grid transitions for the selected-root evaluator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open CompanionOracleDensity (dimension height binWidth height_positive oracleProposalRat oracleTime)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

theorem gridExponent_upper (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    gridExponent A R C a z v ≤ a := by
  have hCR : (0:ℝ) < C := by exact_mod_cast hC
  have hD := D_bounds A R C hCR z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hh : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hh := (v i).property.2; omega)
      exact hh.trans hKB)
  have hH := height_positive A C hCR
  have hbound : (a:ℝ)/height A C*D A R C z (realCorner v) ≤ a := by
    calc
      _ ≤ (a:ℝ)/height A C*height A C :=
        mul_le_mul_of_nonneg_left hD.2 (div_nonneg (Nat.cast_nonneg _) hH.le)
      _ = _ := div_mul_cancel₀ _ hH.ne'
  have he := gridExponent_eq_floor A R C a z v
  have hh := (Int.floor_le ((a:ℝ)/height A C*D A R C z (realCorner v))).trans hbound
  rw [←he] at hh
  exact_mod_cast hh

lemma rationalGridWeight_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : 0 < rationalGridWeight A R C a z v := by
  unfold rationalGridWeight
  positivity
def oracleMove (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v w : Grid (I := Fin (dimension A)) K) : ℚ :=
  if Neighbor v w then oracleProposalRat A.d*min 1
    (rationalGridWeight A R C a z w/rationalGridWeight A R C a z v) else 0

def oracleTransition (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v w : Grid (I := Fin (dimension A)) K) : ℚ :=
  oracleMove A R C a z v w+if v=w then 1-∑ b,oracleMove A R C a z v b else 0

lemma oracleMove_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v w : Grid (I := Fin (dimension A)) K) :
    (oracleMove A R C a z v w:ℝ)=
      MetropolisChain.move (gridWeight A R C a z) Neighbor (binProposal A.d) v w := by
  unfold oracleMove MetropolisChain.move
  split_ifs
  · simp only [Rat.cast_mul,Rat.cast_min,Rat.cast_one,Rat.cast_div,
      rationalGridWeight_cast,oracleProposalRat,binProposal,Rat.cast_pow,Rat.cast_ofNat]
  · exact Rat.cast_zero

theorem oracleTransition_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v w : Grid (I := Fin (dimension A)) K) :
    (oracleTransition A R C a z v w:ℝ)=(oracleChain A R C a z hK).P v w := by
  unfold oracleTransition
  dsimp only [oracleChain,MetropolisChain.chain,FiniteChain.ofMoves]
  by_cases hvw : v=w <;>
    simp only [hvw,ite_true,ite_false,Rat.cast_add,Rat.cast_sub,Rat.cast_sum,
      Rat.cast_one,Rat.cast_zero,oracleMove_cast]

def oracleTransitionLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    RationalLaw (Grid (I := Fin (dimension A)) K) where
  mass := oracleTransition A R C a z v
  nonnegative := fun w => by
    have hh := (oracleChain A R C a z hK).nonnegative v w
    rw [←oracleTransition_cast A R C a z hK] at hh
    exact_mod_cast hh
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum,oracleTransition_cast A R C a z hK,Rat.cast_one]
    exact (oracleChain A R C a z hK).stochastic v

def oracleWalkLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    RationalLaw (Grid (I := Fin (dimension A)) K) :=
  walkLaw (oracleTransitionLaw A R C a z hK) v n

theorem oracleWalkLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (n : ℕ) (v w : Grid (I := Fin (dimension A)) K) :
    ((oracleWalkLaw A R C a z hK v n).mass w:ℝ)=
      ((oracleChain A R C a z hK).kernel.power n).P v w := by
  induction n generalizing w with
  | zero =>
    simp only [oracleWalkLaw,walkLaw,pointLaw,FiniteKernel.power,FiniteKernel.identity]
    by_cases hvw : v=w
    · subst w; simp
    · simp [hvw,Ne.symm hvw]
  | succ n ih =>
    change ((∑ b,(oracleWalkLaw A R C a z hK v n).mass b*oracleTransition A R C a z b w:ℚ):ℝ)=_
    simp only [Rat.cast_sum,Rat.cast_mul,ih,oracleTransition_cast A R C a z hK,
      FiniteKernel.power,FiniteKernel.comp,FiniteChain.kernel]

def oracleStationaryLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) : RationalLaw (Grid (I := Fin (dimension A)) K) := by
  let : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  let w := fun v : Grid (I := Fin (dimension A)) K => rationalGridWeight A R C a z v
  have hw : ∀ v,0 < w v := rationalGridWeight_positive A R C a z
  have hZ : 0 < ∑ v,w v := Finset.sum_pos (fun v _ => hw v) Finset.univ_nonempty
  exact ⟨fun v => w v/∑ b,w b,fun v => (div_pos (hw v) hZ).le,
    by rw [←Finset.sum_div]; exact div_self hZ.ne'⟩

theorem oracleStationaryLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    ((oracleStationaryLaw A R C a z hK).mass v:ℝ)=(oracleChain A R C a z hK).π v := by
  change ((rationalGridWeight A R C a z v/
    ∑ w : Grid (I := Fin (dimension A)) K,rationalGridWeight A R C a z w:ℚ):ℝ)=_
  simp only [Rat.cast_div,Rat.cast_sum,rationalGridWeight_cast]
  rfl

/-- The rational finite-walk law inherits the proved source schedule.
No exact real-valued primitive is used to define its transitions. -/
theorem oracleWalkLaw_variation (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : (a:ℝ) ≤ height A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    (variation (oracleWalkLaw A R C a z hK v (oracleTime A C K Q theta))
      (oracleStationaryLaw A R C a z hK):ℝ) ≤ theta/(8*Q) := by
  let P := oracleChain A R C a z hK
  let n := oracleTime A C K Q theta
  let delta : ℝ := theta/(8*Q)
  have hpoint (w : Grid (I := Fin (dimension A)) K) :
      |(P.kernel.power n).P v w-P.π w| ≤ P.π w*delta := by
    have hm := oracleChain_scheduled_point_mixing A R C a theta
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
end ContingencyTables.RootedOracleDensity

end OAI
