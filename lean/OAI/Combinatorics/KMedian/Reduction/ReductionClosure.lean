import Mathlib
import OAI.Combinatorics.KMedian.Reduction.BudgetReduction

namespace OAI


                                        
section
section
namespace MetricKMedian.Reduction
open Finset

def selectFeasible (I : Instance) (C : Finset (Finset (Fin I.n))) : Finset (Fin I.n) :=
  let K := C.filter (fun S => S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k)
  (pickSingleton (K.image toColex) (fun S => rationalCost I (ofColex S))).biUnion ofColex

theorem selectFeasible_spec (I : Instance) (C : Finset (Finset (Fin I.n)))
    (T : Finset (Fin I.n)) (hT : T ∈ C) (hTF : T ⊆ I.facilities) (hTne : T.Nonempty)
    (hTk : T.card ≤ I.k) :
    selectFeasible I C ∈ C ∧ selectFeasible I C ⊆ I.facilities ∧
      (selectFeasible I C).Nonempty ∧ (selectFeasible I C).card ≤ I.k ∧
      cost I (selectFeasible I C) ≤ cost I T := by
  let K := C.filter (fun S => S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k)
  have hKT : T ∈ K := mem_filter.mpr ⟨hT,hTF,hTne,hTk⟩
  have hK : K.Nonempty := ⟨T,hKT⟩
  obtain ⟨a,ha,hpick,hmin⟩ := pickSingleton_spec (K.image toColex)
    (fun S => rationalCost I (ofColex S)) (hK.image _)
  obtain ⟨S,hS,rfl⟩ := mem_image.mp ha
  have hselect : selectFeasible I C=S := by
    change (pickSingleton (K.image toColex) (fun S => rationalCost I (ofColex S))).biUnion ofColex=S
    rw [hpick]
    simp only [singleton_biUnion,ofColex_toColex]
  obtain ⟨hSC,hSF,hSne,hSk⟩ := mem_filter.mp hS
  rw [hselect]
  refine ⟨hSC,hSF,hSne,hSk,?_⟩
  have hm := hmin (toColex T) (mem_image_of_mem _ hKT)
  simp only [ofColex_toColex] at hm
  have hc : (rationalCost I S:ℝ) ≤ (rationalCost I T:ℝ) := by exact_mod_cast hm
  simpa only [I.cast_rationalCost] using hc

def zeroSet (I : Instance) : Finset (Fin I.n) :=
  if I.clients.Nonempty then I.clients else {I.facilities.min' I.facilities_nonempty}

theorem zeroSet_spec (I : Instance) (hzero : optimum I=0) :
    zeroSet I ⊆ I.facilities ∧ (zeroSet I).Nonempty ∧ (zeroSet I).card ≤ I.k ∧
      cost I (zeroSet I)=0 := by
  obtain ⟨hJF,hJk⟩ := I.optimum_eq_zero_iff.mp hzero
  unfold zeroSet
  split_ifs with hJ
  · exact ⟨hJF,hJ,hJk,(I.cost_eq_zero_iff I.clients hJ).mpr Subset.rfl⟩
  · have hJe := not_nonempty_iff_eq_empty.mp hJ
    refine ⟨singleton_subset_iff.mpr (min'_mem _ _),singleton_nonempty _,?_,?_⟩
    · simpa only [card_singleton] using I.k_pos
    · simp only [cost,hJe,sum_empty]

end MetricKMedian.Reduction
end
section
namespace MetricKMedian.Reduction

theorem reduction_parameters (α η : ℝ) (hα : 1 < α) (hη : 0 < η) (c : ℕ) (hc : 0 < c) :
    ∃ (δ : ℚ) (a b : ℕ), 0 < (δ:ℝ) ∧ (δ:ℝ) ≤ 1/6 ∧
      1+12*(δ:ℝ) ≤ α+η ∧
      (3/2:ℝ) ≤ a*((δ:ℝ)*η/(2*c)) ∧
      6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ) := by
  have hsmall : (0:ℝ) < min (1/6) ((α-1)/12) := by
    apply lt_min
    · norm_num
    · exact div_pos (sub_pos.mpr hα) (by norm_num)
  obtain ⟨δ,hδ,hδsmall⟩ := exists_rat_btwn hsmall
  have hd1 : (δ:ℝ) < 1/6 := hδsmall.trans_le (min_le_left _ _)
  have hd2 : (δ:ℝ) < (α-1)/12 := hδsmall.trans_le (min_le_right _ _)
  let ρ := (δ:ℝ)*η/(2*c)
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hρ : 0 < ρ := div_pos (mul_pos hδ hη) (by positivity)
  refine ⟨δ,⌈(3/2:ℝ)/ρ⌉₊,⌈6*(α+η)*c/((δ:ℝ)*η)⌉₊,hδ,hd1.le,?_,?_,Nat.le_ceil _⟩
  · linarith
  · exact (div_le_iff₀ hρ).mp (Nat.le_ceil _)

end MetricKMedian.Reduction
end
section
namespace MetricKMedian.Reduction
open Finset

def ordinaryReduction (pseudo : (I : Instance) → Finset (Fin I.n)) (δ : ℚ) (c a b : ℕ)
    (I : Instance) : Finset (Fin I.n) :=
  if I.clients ⊆ I.facilities ∧ I.clients.card ≤ I.k then zeroSet I
  else selectFeasible I (reductionOutputs pseudo I δ c a b)

theorem ordinaryReduction_spec
    (pseudo : (I : Instance) → Finset (Fin I.n)) (α η : ℝ) (δ : ℚ) (c a b : ℕ)
    (hc : 0 < c) (hδ : 0 < (δ:ℝ)) (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η)
    (hfactor : 1+12*(δ:ℝ) ≤ α+η)
    (ha : (3/2:ℝ) ≤ a*((δ:ℝ)*η/(2*c)))
    (hb : 6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ))
    (hpseudo : ∀ I, pseudo I ⊆ I.facilities ∧ (pseudo I).Nonempty ∧
      (pseudo I).card ≤ I.k+c ∧ cost I (pseudo I) ≤ α*optimum I)
    (I : Instance) :
    ordinaryReduction pseudo δ c a b I ⊆ I.facilities ∧
      (ordinaryReduction pseudo δ c a b I).Nonempty ∧
      (ordinaryReduction pseudo δ c a b I).card ≤ I.k ∧
      cost I (ordinaryReduction pseudo δ c a b I) ≤ (α+η)*optimum I := by
  unfold ordinaryReduction
  split_ifs with hzero
  · have hz := I.optimum_eq_zero_iff.mpr hzero
    obtain ⟨hsub,hne,hk,hcost⟩ := zeroSet_spec I hz
    refine ⟨hsub,hne,hk,?_⟩
    rw [hcost,hz,mul_zero]
  · have hz : optimum I ≠ 0 := fun he => hzero (I.optimum_eq_zero_iff.mp he)
    obtain ⟨S,hS,hSF,hSne,hSk,hSc⟩ := reductionOutputs_success pseudo α η δ c a b hc
      hδ hsmall hη hfactor ha hb hpseudo I (lt_of_le_of_ne I.optimum_nonneg (Ne.symm hz))
    obtain ⟨_,hsub,hne,hk,hcost⟩ := selectFeasible_spec I _ S hS hSF hSne hSk
    exact ⟨hsub,hne,hk,hcost.trans hSc⟩

theorem ordinaryReduction_parameters (pseudo : (I : Instance) → Finset (Fin I.n))
    (α η : ℝ) (hα : 1 < α) (hη : 0 < η) (c : ℕ) (hc : 0 < c)
    (hpseudo : ∀ I, pseudo I ⊆ I.facilities ∧ (pseudo I).Nonempty ∧
      (pseudo I).card ≤ I.k+c ∧ cost I (pseudo I) ≤ α*optimum I) :
    ∃ (δ : ℚ) (a b : ℕ), ∀ I,
      ordinaryReduction pseudo δ c a b I ⊆ I.facilities ∧
      (ordinaryReduction pseudo δ c a b I).Nonempty ∧
      (ordinaryReduction pseudo δ c a b I).card ≤ I.k ∧
      cost I (ordinaryReduction pseudo δ c a b I) ≤ (α+η)*optimum I := by
  obtain ⟨δ,a,b,hδ,hs,hf,ha,hb⟩ := reduction_parameters α η hα hη c hc
  exact ⟨δ,a,b,ordinaryReduction_spec pseudo α η δ c a b hc hδ hs hη hf ha hb hpseudo⟩

end MetricKMedian.Reduction
end
end

end OAI
