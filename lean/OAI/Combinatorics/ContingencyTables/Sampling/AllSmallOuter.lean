import OAI.Combinatorics.ContingencyTables.Sampling.AllSmallBoolean
import OAI.Combinatorics.ContingencyTables.Sampling.AllSmallInitialization
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperInitialization
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperBinaryParameters

namespace OAI

/-! # Complete finite rejection sampling when the large rectangle is empty -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "s" => smallProposalBits (I := I) (J := J)
local instance : DecidableEq (PaperStates r c) := Classical.decEq _

/-- Each trial reads a disjoint word; failed trials use the feasible fallback. -/
def unitOuterDraw (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n M : ℕ) (z₀ : Table r c)
    (bits : Fin (M*(n*s)) → Bool) : Table r c :=
  wordRetry (fun w => stateTrial r c (unitJointDraw r c fallback x n w)) z₀ M
    (GridBoundary.gridWordEquiv M (n*s) bits)

lemma unitOuterDraw_law (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n M : ℕ) (z₀ : Table r c) :
    mapLaw (uniformLaw (α := Fin (M*(n*s)) → Bool))
      (unitOuterDraw r c fallback x n M z₀)=
      retryLaw (mapLaw (uniformLaw (α := Fin (n*s) → Bool))
        (unitJointDraw r c fallback x n)) (stateTrial r c) z₀ M := by
  unfold unitOuterDraw
  rw [←map_equiv (GridBoundary.gridWordEquiv M (n*s)),uniform_equiv]
  change wordRetryLaw _ _ _=_
  rw [wordRetryLaw_eq,←retryLaw_map]

lemma unitOuterDraw_error [Nonempty I] [Nonempty J] [Nonempty (PaperStates r c)]
    [Nonempty (Table r c)] (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (htotal : (∑ i,r i)=∑ j,c j)
    (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n M : ℕ) (z₀ : Table r c) :
    (variation (mapLaw (uniformLaw (α := Fin (M*(n*s)) → Bool))
      (unitOuterDraw r c fallback x n M z₀)) (uniformLaw (α := Table r c)):ℝ) ≤
      Real.exp (-(M:ℝ)/(2*(1+(d:ℝ)^2)))+
      M*(((stateBound r c+1:ℕ):ℝ)^(2*d)*Real.exp (-(n:ℝ)/(d:ℝ)^160)) := by
  have hd : 14 ≤ d := by
    have hi := Fintype.card_pos (α := I)
    have hj := Fintype.card_pos (α := J)
    unfold dimensionAllowance
    nlinarith
  let p := mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (unitJointDraw r c fallback x n)
  let q := uniformLaw (α := PaperStateJoint r c)
  have hj := unitJointDraw_variation r c hsmall fallback x n
  have hr := retryLaw_variation p q (stateTrial r c) z₀ M
  have hi : (variation (retryLaw q (stateTrial r c) z₀ M)
      (uniformLaw (α := Table r c)):ℝ) ≤ Real.exp (-(M:ℝ)/(2*(1+(d:ℝ)^2))) := by
    apply uniform_partial_retry_exp (StateJointSuccess r c) (originalStateSuccessEquiv r c)
      z₀ M (2*(1+(d:ℝ)^2))
    rw [paperStateJoint_card]
    exact stationary_success_ratio r c htotal hd
  have ht := variation_triangle (retryLaw p (stateTrial r c) z₀ M)
    (retryLaw q (stateTrial r c) z₀ M) (uniformLaw (α := Table r c))
  rw [unitOuterDraw_law]
  have hrR : (variation (retryLaw p (stateTrial r c) z₀ M)
      (retryLaw q (stateTrial r c) z₀ M):ℝ) ≤ M*(variation p q:ℝ) := by
    exact_mod_cast hr
  have htR := (Rat.cast_le (K := ℝ)).mpr ht
  simp only [Rat.cast_add] at htR
  exact htR.trans (by nlinarith)

/-- The all-small branch reaches the same requested error as the branch
with a nonempty large rectangle, using no completion-sampling oracle. -/
theorem unitOuterDraw_accuracy [Nonempty I] [Nonempty J] [Nonempty (PaperStates r c)]
    [Nonempty (Table r c)] (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ) (hk : 1 ≤ k)
    (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (z₀ : Table r c) :
    (variation (mapLaw (uniformLaw (α := Fin (outerTrials d k*(outerSteps d (smallBinaryLength r c) k*s)) → Bool))
      (unitOuterDraw r c fallback x (outerSteps d (smallBinaryLength r c) k) (outerTrials d k) z₀))
      (uniformLaw (α := Table r c)):ℝ) ≤ 1/(2:ℝ)^k := by
  have hd : 14 ≤ d := by
    have hi := Fintype.card_pos (α := I)
    have hj := Fintype.card_pos (α := J)
    unfold dimensionAllowance
    nlinarith
  have he := outer_total_error d (smallBinaryLength r c) k (stateBound r c) hd
    (smallBinaryLength_parameters r c).2.1 hk (smallBinaryLength_parameters r c).2.2
  have hv := unitOuterDraw_error r c hsmall htotal fallback x
    (outerSteps d (smallBinaryLength r c) k) (outerTrials d k) z₀
  apply hv.trans
  have hn : 0 ≤ (outerTrials d k:ℝ)*(outerSteps d (smallBinaryLength r c) k+1)/
      (2:ℝ)^(outerAccuracy d (smallBinaryLength r c) k) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by
      exact add_nonneg (Nat.cast_nonneg _) zero_le_one)) (le_of_lt (pow_pos (by norm_num) _))
  nlinarith

end
end ContingencyTables.SmallGraphProfiles

end OAI
