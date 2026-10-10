import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ClassSlotsMem

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [DecidableEq V]

def smallSubsets (S : Finset V) (w : ℕ) : Finset (Finset V) :=
  (Finset.range (w+1)).biUnion (fun r => S.powersetCard r)
lemma mem_smallSubsets (S R : Finset V) (w : ℕ) :
    R ∈ smallSubsets S w ↔ R ⊆ S ∧ R.card ≤ w := by
  simp only [smallSubsets,Finset.mem_biUnion,Finset.mem_range,Finset.mem_powersetCard]
  constructor
  · rintro ⟨r,hr,hRS,hR⟩
    exact ⟨hRS,by omega⟩
  · rintro ⟨hRS,hR⟩
    exact ⟨R.card,by omega,hRS,rfl⟩

lemma smallSubsets_card (S : Finset V) (w : ℕ) :
    (smallSubsets S w).card ≤ (w+1)*(S.card+1)^w := by
  unfold smallSubsets
  calc
    _ ≤ ∑ r ∈ Finset.range (w+1), (S.powersetCard r).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ Finset.range (w+1), (S.card+1)^w := by
      apply Finset.sum_le_sum
      intro r hr
      rw [Finset.card_powersetCard]
      exact (Nat.choose_le_pow S.card r).trans
        ((Nat.pow_le_pow_left (by omega : S.card ≤ S.card+1) r).trans
          (Nat.pow_le_pow_right (by omega : 0 < S.card+1) (by have hh := Finset.mem_range.mp hr; omega)))
    _ = _ := by simp

def exchangeCandidates (F S : Finset V) (w : ℕ) : Finset (Finset V) :=
  (((smallSubsets S w).product (smallSubsets F w)).image (fun RA => (S \ RA.1) ∪ RA.2)).filter
    (fun T => T.card = S.card)

lemma candidate_mem_self (F S : Finset V) (w : ℕ) : S ∈ exchangeCandidates F S w := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(∅,∅),?_,by simp⟩,rfl⟩
  apply Finset.mem_product.mpr
  constructor <;> apply (mem_smallSubsets _ _ w).mpr <;> simp

lemma candidate_properties (F S T : Finset V) (w : ℕ) (hSF : S ⊆ F)
    (hT : T ∈ exchangeCandidates F S w) :
    T ⊆ F ∧ T.card = S.card ∧ (S \ T).card ≤ w ∧ (T \ S).card ≤ w := by
  rcases Finset.mem_filter.mp hT with ⟨hm,hcard⟩
  rcases Finset.mem_image.mp hm with ⟨⟨R,A⟩,hra,rfl⟩
  rcases Finset.mem_product.mp hra with ⟨hr,ha⟩
  rcases (mem_smallSubsets _ _ _).mp hr with ⟨hRS,hrc⟩
  rcases (mem_smallSubsets _ _ _).mp ha with ⟨hAF,hac⟩
  have hdiff := exchange_diff_bounds S R A
  exact ⟨Finset.union_subset (Finset.sdiff_subset.trans hSF) hAF,hcard,
    (Finset.card_le_card hdiff.1).trans hrc,(Finset.card_le_card hdiff.2).trans hac⟩

lemma candidate_of_exchange (F S T : Finset V) (w : ℕ) (hTF : T ⊆ F)
    (hcard : T.card = S.card) (hR : (S \ T).card ≤ w) (hA : (T \ S).card ≤ w) :
    T ∈ exchangeCandidates F S w := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(S \ T,T \ S),?_,?_⟩,hcard⟩
  · exact Finset.mem_product.mpr ⟨(mem_smallSubsets _ _ _).mpr ⟨Finset.sdiff_subset,hR⟩,
      (mem_smallSubsets _ _ _).mpr ⟨Finset.sdiff_subset.trans hTF,hA⟩⟩
  · ext x
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto

lemma exchangeCandidates_card (F S : Finset V) (w : ℕ) (hSF : S ⊆ F) :
    (exchangeCandidates F S w).card ≤ ((w+1)*(F.card+1)^w)^2 := by
  have hS := smallSubsets_card S w
  have hF := smallSubsets_card F w
  have hn : (S.card+1)^w ≤ (F.card+1)^w :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (Finset.card_le_card hSF) 1) w
  have hbound := hS.trans (Nat.mul_le_mul_left (w+1) hn)
  calc
    _ ≤ (((smallSubsets S w).product (smallSubsets F w)).image
        (fun RA => (S \ RA.1) ∪ RA.2)).card := Finset.card_filter_le _ _
    _ ≤ ((smallSubsets S w).product (smallSubsets F w)).card := Finset.card_image_le
    _ = (smallSubsets S w).card*(smallSubsets F w).card := Finset.card_product _ _
    _ ≤ ((w+1)*(F.card+1)^w)*((w+1)*(F.card+1)^w) := Nat.mul_le_mul hbound hF
    _ = _ := (pow_two _).symm

noncomputable def descentStep (F : Finset V) (rank : Finset V → ℕ) (w : ℕ) (S : Finset V) : Finset V :=
  Classical.choose (Finset.exists_min_image (exchangeCandidates F S w) rank
    ⟨S,candidate_mem_self F S w⟩)
lemma descentStep_mem (F : Finset V) (rank : Finset V → ℕ) (w : ℕ) (S : Finset V) :
    descentStep F rank w S ∈ exchangeCandidates F S w :=
  (Classical.choose_spec (Finset.exists_min_image (exchangeCandidates F S w) rank
    ⟨S,candidate_mem_self F S w⟩)).1
lemma descentStep_min (F : Finset V) (rank : Finset V → ℕ) (w : ℕ) (S T : Finset V)
    (hT : T ∈ exchangeCandidates F S w) : rank (descentStep F rank w S) ≤ rank T :=
  (Classical.choose_spec (Finset.exists_min_image (exchangeCandidates F S w) rank
    ⟨S,candidate_mem_self F S w⟩)).2 T hT

theorem bounded_descent (F S : Finset V) (rank : Finset V → ℕ) (w : ℕ) (hSF : S ⊆ F) :
    ∃ n ≤ rank S, ∃ path : ℕ → Finset V,
      path 0 = S ∧ (∀ j < n, path (j+1) ∈ exchangeCandidates F (path j) w) ∧
      path n ⊆ F ∧ (path n).card = S.card ∧ rank (path n) ≤ rank S ∧
      (∀ T ∈ exchangeCandidates F (path n) w, rank (path n) ≤ rank T) := by
  generalize heq : rank S = fuel
  induction fuel using Nat.strong_induction_on generalizing S with
  | h fuel ih =>
    by_cases hlocal : ∀ T ∈ exchangeCandidates F S w, rank S ≤ rank T
    · refine ⟨0,by omega,fun _ => S,rfl,?_,hSF,rfl,(by change rank S ≤ fuel; omega),hlocal⟩
      intro j hj
      omega
    · let S' := descentStep F rank w S
      have hm : S' ∈ exchangeCandidates F S w := descentStep_mem F rank w S
      have hp := candidate_properties F S S' w hSF hm
      have hlt : rank S' < rank S := by
        push Not at hlocal
        obtain ⟨T,hT,ht⟩ := hlocal
        exact (descentStep_min F rank w S T hT).trans_lt ht
      obtain ⟨n,hn,path,hzero,hsteps,hend,hcard,hcost,hmin⟩ :=
        ih (rank S') (by omega) S' hp.1 rfl
      let path' : ℕ → Finset V := fun j => if j = 0 then S else path (j-1)
      refine ⟨n+1,by omega,path',by simp [path'],?_,?_,?_,?_,?_⟩
      · intro j hj
        cases j with
        | zero => simpa only [path',ite_eq_left rfl,Nat.reduceAdd,ite_false,Nat.add_sub_cancel,one_ne_zero] using hzero ▸ hm
        | succ j =>
          simpa only [path',Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,Nat.succ_sub_one]
            using hsteps j (by omega)
      · simpa only [path',Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel] using hend
      · simpa only [path',Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel] using hcard.trans hp.2.1
      · simpa only [path',Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel] using hcost.trans (by omega : rank S' ≤ fuel)
      · simpa only [path',Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel] using hmin

end MetricKMedianRecovery.LocalSearch

end OAI
