import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseReduction
import OAI.Combinatorics.KMedian.Reduction.SparsifyEnumeration

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

def restrictFacilities (I : Instance) (F : Finset (Fin I.n)) (hF : I.k ≤ F.card) : Instance :=
  { I with facilities := F, k_le := hF }

@[simp] theorem restrict_cost (I : Instance) (F : Finset (Fin I.n)) (hF : I.k ≤ F.card)
    (S : Finset (Fin I.n)) : cost (I.restrictFacilities F hF) S=cost I S := rfl

theorem padded_optimum (I : Instance) :
    ∃ O, O ⊆ I.facilities ∧ O.Nonempty ∧ O.card=I.k ∧ cost I O=optimum I := by
  obtain ⟨S,hSF,hS,hSk,hSc⟩ := I.optimum_attained
  obtain ⟨O,hSO,hOF,hOk⟩ := exists_subsuperset_card_eq hSF hSk I.k_le
  have hO := hS.mono hSO
  refine ⟨O,hOF,hO,hOk,le_antisymm ?_ (I.optimum_le hOF hO hOk.le)⟩
  exact (I.cost_antitone hS hSO).trans_eq hSc

theorem restrict_optimum (I : Instance) (F O : Finset (Fin I.n))
    (hF : I.k ≤ F.card) (hFF : F ⊆ I.facilities) (hOF : O ⊆ F) (hO : O.Nonempty)
    (hOk : O.card ≤ I.k) (hcost : cost I O=optimum I) :
    optimum (I.restrictFacilities F hF)=optimum I := by
  apply le_antisymm
  · exact ((I.restrictFacilities F hF).optimum_le hOF hO hOk).trans_eq hcost
  · obtain ⟨S,hS,hSne,hSk,hSc⟩ := (I.restrictFacilities F hF).optimum_attained
    exact (I.optimum_le (hS.trans hFF) hSne hSk).trans_eq hSc

end Instance

namespace Reduction

def reductionOutputs (pseudo : (I : Instance) → Finset (Fin I.n)) (I : Instance)
    (δ : ℚ) (c a b : ℕ) : Finset (Finset (Fin I.n)) :=
  (sparseBranches I I.facilities a).biUnion (fun F =>
    if hF : I.k ≤ F.card then sparseOutcomes I F (pseudo (I.restrictFacilities F hF)) δ c b
    else ∅)

theorem reductionOutputs_success
    (pseudo : (I : Instance) → Finset (Fin I.n)) (α η : ℝ) (δ : ℚ) (c a b : ℕ)
    (hc : 0 < c) (hδ : 0 < (δ:ℝ)) (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η)
    (hfactor : 1+12*(δ:ℝ) ≤ α+η)
    (ha : (3/2:ℝ) ≤ a*((δ:ℝ)*η/(2*c)))
    (hb : 6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ))
    (hpseudo : ∀ I, pseudo I ⊆ I.facilities ∧ (pseudo I).Nonempty ∧
      (pseudo I).card ≤ I.k+c ∧ cost I (pseudo I) ≤ α*optimum I)
    (I : Instance) (hopt : 0 < optimum I) :
    ∃ S ∈ reductionOutputs pseudo I δ c a b,
      S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (α+η)*optimum I := by
  let : PseudoMetricSpace (Fin I.n) := I.pseudoMetric
  obtain ⟨O,hOF,hO,hOk,hOc⟩ := I.padded_optimum
  have hC : 0 < cost I O := by rwa [hOc]
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hρ : 0 < (δ:ℝ)*η/(2*c) := div_pos (mul_pos hδ hη) (by positivity)
  obtain ⟨F,hF,hOF',hsp⟩ := sparse_branch_exists I.facilities O hOF hO hC
    ((δ:ℝ)*η/(2*c)) hρ a ha
  have hFk : I.k ≤ F.card := hOk.symm.le.trans (card_le_card hOF')
  have hFF := sparseBranches_sub I I.facilities a hF
  have hop : optimum (I.restrictFacilities F hFk)=optimum I :=
    I.restrict_optimum F O hFk hFF hOF' hO hOk.le hOc
  obtain ⟨hTF,hT,hTc,hTv⟩ := hpseudo (I.restrictFacilities F hFk)
  change cost I (pseudo (I.restrictFacilities F hFk)) ≤ α*optimum (I.restrictFacilities F hFk) at hTv
  rw [hop,← hOc] at hTv
  obtain ⟨S,hSm,hSF,hS,hSk,hSc⟩ := sparse_outcome_exists F O
    (pseudo (I.restrictFacilities F hFk)) hOF' hO hOk hTF hT α η δ c b hc hδ hsmall hη
    hC hTv hTc hsp hfactor hb
  refine ⟨S,mem_biUnion.mpr ⟨F,hF,?_⟩,hSF.trans hFF,hS,hSk,?_⟩
  · simp only [dite_eq_left hFk]
    exact hSm
  · rwa [hOc] at hSc

theorem reductionOutputs_card
    (pseudo : (I : Instance) → Finset (Fin I.n)) (I : Instance) (δ : ℚ) (c a b : ℕ)
    (hsub : ∀ J, pseudo J ⊆ J.facilities) :
    (reductionOutputs pseudo I δ c a b).card ≤
      ((a+1)*(I.facilities.card*I.facilities.card+1)^a)*
      (((c+1)*(I.facilities.card+1)^(c+1)+1)*(1+((b+1)*(I.facilities.card+1)^b)^2)+1) := by
  have hbound : ∀ F ∈ sparseBranches I I.facilities a,
      (if hF : I.k ≤ F.card then sparseOutcomes I F (pseudo (I.restrictFacilities F hF)) δ c b
        else ∅).card ≤
      ((c+1)*(I.facilities.card+1)^(c+1)+1)*(1+((b+1)*(I.facilities.card+1)^b)^2)+1 := by
    intro F hF
    split_ifs with hFk
    · have hh := sparseOutcomes_card I F (pseudo (I.restrictFacilities F hFk))
        (hsub (I.restrictFacilities F hFk)) δ c b
      have hFc := card_le_card (sparseBranches_sub I I.facilities a hF)
      have hTc := (card_le_card (hsub (I.restrictFacilities F hFk))).trans hFc
      apply hh.trans
      gcongr; assumption
    · simp only [card_empty]; omega
  calc
    _ ≤ ∑ F ∈ sparseBranches I I.facilities a,
        (if hF : I.k ≤ F.card then sparseOutcomes I F (pseudo (I.restrictFacilities F hF)) δ c b
          else ∅).card := card_biUnion_le
    _ ≤ ∑ _F ∈ sparseBranches I I.facilities a,
        (((c+1)*(I.facilities.card+1)^(c+1)+1)*(1+((b+1)*(I.facilities.card+1)^b)^2)+1) :=
      sum_le_sum hbound
    _ = (sparseBranches I I.facilities a).card*
      (((c+1)*(I.facilities.card+1)^(c+1)+1)*(1+((b+1)*(I.facilities.card+1)^b)^2)+1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (sparseBranches_card I I.facilities a)

end Reduction
end MetricKMedian
end
end

end OAI
