import Mathlib
import OAI.Combinatorics.KMedian.Reduction.CompletionEnumeration
import OAI.Combinatorics.KMedian.Reduction.DeletionEndpoint
import OAI.Combinatorics.KMedian.Reduction.RationalDeletion

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def sparseOutcomes (I : Instance) (F T : Finset (Fin I.n)) (δ : ℚ) (c b : ℕ) :
    Finset (Finset (Fin I.n)) :=
  insert T ((deletionEndpoints I T c).biUnion (fun U => insert U (completionBranches I F U δ b)))

theorem sparseOutcomes_card (I : Instance) (F T : Finset (Fin I.n)) (hTF : T ⊆ F)
    (δ : ℚ) (c b : ℕ) :
    (sparseOutcomes I F T δ c b).card ≤
      ((c+1)*(T.card+1)^(c+1)+1)*(1+((b+1)*(F.card+1)^b)^2)+1 := by
  have hUcard : ∀ U ∈ deletionEndpoints I T c, U.card ≤ F.card := by
    intro U hU
    obtain ⟨r,_,rfl⟩ := mem_image.mp hU
    rw [cast_rationalHistory]
    exact card_le_card ((history_bounds I (r:ℝ) T c).1.trans hTF)
  have hcomp : ∀ U ∈ deletionEndpoints I T c,
      (insert U (completionBranches I F U δ b)).card ≤ 1+((b+1)*(F.card+1)^b)^2 := by
    intro U hU
    have hc := completionBranches_card I F U δ b
    have hbU : (b+1)*(U.card+1)^b ≤ (b+1)*(F.card+1)^b :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (hUcard U hU) 1) b)
    have hprod := Nat.mul_le_mul_right ((b+1)*(F.card+1)^b) hbU
    rw [← pow_two] at hprod
    have hi := (card_insert_le U (completionBranches I F U δ b)).trans
      (Nat.add_le_add_right (hc.trans hprod) 1)
    omega
  calc
    _ ≤ ((deletionEndpoints I T c).biUnion (fun U => insert U (completionBranches I F U δ b))).card+1 :=
      card_insert_le _ _
    _ ≤ (∑ U ∈ deletionEndpoints I T c, (insert U (completionBranches I F U δ b)).card)+1 :=
      Nat.add_le_add_right card_biUnion_le 1
    _ ≤ (∑ _U ∈ deletionEndpoints I T c, (1+((b+1)*(F.card+1)^b)^2))+1 :=
      Nat.add_le_add_right (sum_le_sum hcomp) 1
    _ = (deletionEndpoints I T c).card*(1+((b+1)*(F.card+1)^b)^2)+1 := by simp
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_right _ (deletionEndpoints_card I T c)) 1

variable {I : Instance}
local instance sparseReductionPseudoMetric : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

theorem sparse_outcome_exists (F O T : Finset (Fin I.n)) (hOF : O ⊆ F)
    (hO : O.Nonempty) (hk : O.card=I.k) (hTF : T ⊆ F) (hT : T.Nonempty)
    (α η : ℝ) (δ : ℚ) (c b : ℕ) (hc : 0 < c) (hδ : 0 < (δ:ℝ))
    (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η) (hC : 0 < cost I O)
    (hcost : cost I T ≤ α*cost I O) (hcard : T.card ≤ I.k+c)
    (hsp : Sparse (I:=I) F O ((δ:ℝ)*η/(2*c)))
    (hfactor : 1+12*(δ:ℝ) ≤ α+η) (hb : 6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ)) :
    ∃ S ∈ sparseOutcomes I F T δ c b,
      S ⊆ F ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (α+η)*cost I O := by
  classical
  by_cases hTk : T.card ≤ I.k
  · refine ⟨T,mem_insert_self _ _,hTF,hT,hTk,?_⟩
    have hηC := mul_nonneg hη.le hC.le
    nlinarith only [hcost,hηC]
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  let B := η*cost I O/c
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hη.le hC.le) hcR.le
  let U := deletionHistory I B T c
  have hUc : I.k ≤ U.card := history_budget_lower I B T (by omega) c
  have hUne : U.Nonempty := card_pos.mp (I.k_pos.trans hUc)
  have hUF : U ⊆ F := (history_bounds I B T c).1.trans hTF
  have hUcst : cost I U ≤ (α+η)*cost I O := by
    have hhistory := history_cost I hB T c
    have hcancel : (c:ℝ)*B=η*cost I O := by dsimp only [B]; field_simp
    rw [hcancel] at hhistory
    nlinarith only [hhistory,hcost]
  have hUm : U ∈ deletionEndpoints I T c := ideal_endpoint_mem I T c hB
  obtain hUk | hstuck := history_endpoint I B T c hcard
  · refine ⟨U,mem_insert_of_mem (mem_biUnion.mpr ⟨U,hUm,mem_insert_self _ _⟩),hUF,hUne,hUk,hUcst⟩
  · by_cases hUk : U.card ≤ I.k
    · exact ⟨U,mem_insert_of_mem (mem_biUnion.mpr ⟨U,hUm,mem_insert_self _ _⟩),hUF,hUne,hUk,hUcst⟩
    obtain ⟨S,hS,hSF,hSne,hSk,hSc⟩ := completion_branch_exists F O U hOF hO hk hUF
      (by omega) (α+η) η δ c b hc hδ hsmall hη hC hUcst hsp (fun i hi => (hstuck i hi).le) hb
    refine ⟨S,mem_insert_of_mem (mem_biUnion.mpr ⟨U,hUm,mem_insert_of_mem hS⟩),hSF,hSne,hSk,?_⟩
    exact hSc.trans (mul_le_mul_of_nonneg_right hfactor hC.le)

end MetricKMedian.Reduction
end
end

end OAI
