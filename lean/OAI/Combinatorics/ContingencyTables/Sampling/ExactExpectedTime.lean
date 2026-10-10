import OAI.Combinatorics.ContingencyTables.Sampling.ExactGatePublic
import OAI.Combinatorics.ContingencyTables.Sampling.ExactPublicLaw
import OAI.Combinatorics.ContingencyTables.Machines.QuadraticPrefixRuntime

namespace OAI

/-! # Summability of the actual exact sampler's public runtime -/

namespace ContingencyTables.ExactExpectedTime
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms SmallGraphProfiles PhysicalRetryTail
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "dim" => CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)

attribute [local irreducible] ExactPublicPrefix.program ExactTablePrefix.experiment
  PublishedInputs.FiniteBoxPrekopaLeindler PublishedInputs.FiniteCheeger

/-- Expected runtime is bounded by the explicit costs of the ordinary
prefix and the probability-weighted correction branch. -/
theorem bound
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin q) (4*k^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (B L : ℕ)
    (hB : ∀ X : Table r c,GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B)
    (hL : ∀ X : Table r c,(ExactPublicPrefix.word r c X).length≤L) :
    let S := ExactGatePublic.budget r c B L
    let T := ExactPublicCost.budget r c 1 B L+1
    let tail := PhysicalRetryTail.tail ExactPublicPrefix.program.table
      (ExactPublicPrefix.program.initial (Tape.mk₁ (Algorithms.encodeMargins r c)))
    Summable tail ∧ (∑' t,tail t)≤(S:ℝ)+11*(1/(2:ℝ)^correctionPrecision r c)*T := by
  dsimp only
  let S := ExactGatePublic.budget r c B L
  let T := ExactPublicCost.budget r c 1 B L+1
  let M := ExactPublicPrefix.program.table
  let init := ExactPublicPrefix.program.initial (Tape.mk₁ (Algorithms.encodeMargins r c))
  refine QuadraticPrefixRuntime.expected_time (PhysicalRetryTail.tail M init) S T
    (Nat.zero_lt_succ _) (1/(2:ℝ)^correctionPrecision r c) (by positivity)
    (tail_nonnegative M init) ?_ (tail_antitone M init) ?_ ?_
  · intro t
    have h := PhysicalEventBounds.mean_mono (experiment M t init) live (fun _ => 1) live_le_one
    rw [PhysicalPartialSequence.mean_const] at h
    unfold PhysicalRetryTail.tail
    exact_mod_cast h
  · obtain ⟨p,hp,hm,hc⟩ := ExactGatePublic.prefix_correct_cost r c htotal B L hB hL
    have h := tail_le_failure M (ExactGatePublic.publicOutput r c) init p hp
      (ExactGatePublic.publicOutput_halted r c) S hc
    rw [hm,ExactGatePublic.failure r c htotal] at h
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using h
  · intro N
    obtain ⟨p,hp,hm,hc⟩ := ExactPublicCost.prefix_correct_cost r c htotal N B L hB hL
    have hcost : p.cost≤S+T*(N+1)^2 := by
      have hq := ExactPublicCost.quadratic_budget r c N B L
      have ht := Nat.mul_le_mul_right ((N+1)^2)
        (Nat.le_succ (ExactPublicCost.budget r c 1 B L))
      exact (hc.trans (hq.trans ht)).trans (Nat.le_add_left _ _)
    have h := tail_le_failure M (ExactPublicPrefix.output r c) init p hp
      (ExactPublicPrefix.output_halted r c) _ hcost
    rw [hm] at h
    have hf := ExactTablePrefix.failure_bound r c (hPL _) (hCheeger _ dim) htotal N
    have hfr := (Rat.cast_le (K := ℝ)).mpr hf
    exact h.trans (by
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using hfr)

/-- The physical tail is summable for every equal-total margin pair. -/
theorem summable
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin q) (4*k^8)))
    (htotal : (∑ i,r i)=∑ j,c j) :
    Summable (fun t => 1-Algorithms.haltMass ExactPublicPrefix.machine (Algorithms.encodeMargins r c) t) := by
  obtain ⟨p,hp⟩ := ExactPrintCost.polynomial_print_bound
  let B := p.eval (ExactPrintCost.matrixSize (n := n) r)
  have hB (X : Table r c) : GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B :=
    (Nat.le_add_right _ _).trans (hp m n r c X)
  have hL (X : Table r c) : (ExactPublicPrefix.word r c X).length≤B :=
    (MatchingFPRAS.TreeTyped.list_length_le_weight _).trans
      ((Nat.le_add_left _ _).trans (hp m n r c X))
  have hs := (bound r c hPL hCheeger htotal B B hB hL).1
  have he : (fun t => 1-Algorithms.haltMass ExactPublicPrefix.machine (Algorithms.encodeMargins r c) t)=
      PhysicalRetryTail.tail ExactPublicPrefix.program.table
        (ExactPublicPrefix.program.initial (Tape.mk₁ (Algorithms.encodeMargins r c))) := by
    funext t
    exact PhysicalPublicLaw.tail_eq _ _ _
  rw [he]
  exact hs

end
end ContingencyTables.ExactExpectedTime

end OAI
