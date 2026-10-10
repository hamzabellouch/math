import OAI.Probability.MatroidProphet.LayerRank
import OAI.Probability.MatroidProphet.ProductRestriction

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma conditionalRank_union_chain (M : Matroid α) (A B P : Set α) :
    conditionalRank M (A ∪ B) P =
      conditionalRank M A P + conditionalRank M B (P ∪ A) := by
  have hA := conditionalRank_add_base M A P
  have hB := conditionalRank_add_base M B (P ∪ A)
  have hAB := conditionalRank_add_base M (A ∪ B) P
  have heq : B ∪ (P ∪ A) = (A ∪ B) ∪ P := by ext x; simp only [Set.mem_union]; tauto
  rw [heq] at hB
  rw [union_comm A P] at hA
  omega

lemma conditionalRank_subset_witness (M : Matroid α) (K P A : Set α)
    (hK : conditionalRank M K P = K.ncard) (hAK : A ⊆ K) :
    conditionalRank M A P = A.ncard := by
  have hu : A ∪ (K \ A) = K := by
    ext e
    constructor
    · rintro (he | he)
      · exact hAK he
      · exact he.1
    · intro he
      by_cases ha : e ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨he, ha⟩
  have hc := conditionalRank_union_chain M A (K \ A) P
  rw [hu, hK] at hc
  have hd := (conditionalRank_le_rank M (K \ A) (P ∪ A)).trans (natRank_le_ncard M (K \ A))
  have ha := (conditionalRank_le_rank M A P).trans (natRank_le_ncard M A)
  have hn := Set.ncard_sdiff_add_ncard_of_subset hAK
  omega

lemma exists_conditionalRank_witness (M : Matroid α) (hE : M.E = Set.univ) (S P : Set α) :
    ∃ K : Set α, K ⊆ S ∧ conditionalRank M K P = K.ncard ∧
      K.ncard = conditionalRank M S P := by
  obtain ⟨K, hK, hgen, hcard⟩ := exists_extension_generators M hE (M.closure P) S
    (M.closure (M.closure P ∪ S)) (Matroid.isFlat_closure (M := M) P) rfl
  have hrS : K.ncard + natRank M P = natRank M (S ∪ P) := by
    simpa only [natRank, M.eRk_closure_eq, M.eRk_union_closure_left_eq, union_comm P S] using hcard
  have hrK : natRank M (K ∪ P) = natRank M (S ∪ P) := by
    have hh := congrArg (natRank M) hgen
    simpa only [natRank, M.eRk_closure_eq, M.eRk_union_closure_left_eq, union_comm P K,
      union_comm P S] using hh
  refine ⟨K, fun _ he => (hK he).1, ?_, ?_⟩ <;> unfold conditionalRank <;> omega

theorem independent_thinning_rank [DecidableEq α] (M : Matroid α) (hE : M.E = Set.univ)
    (V S : Finset α) (hSV : S ⊆ V) (P : Set α) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (conditionalRank M (S : Set α) P : ℝ) ≤
      bitsExpectation (fun _ => t) V (fun T => (conditionalRank M ((S ∩ T : Finset α) : Set α) P : ℝ)) := by
  classical
  obtain ⟨K, hKS, hKrank, hKcard⟩ := exists_conditionalRank_witness M hE (S : Set α) P
  let KF := K.toFinset
  have hKF : KF ⊆ V := fun e he => hSV (hKS (by simpa [KF] using he))
  have hpoint (T : Finset α) : ((KF ∩ T).card : ℝ) ≤
      (conditionalRank M ((S ∩ T : Finset α) : Set α) P : ℝ) := by
    have hw := conditionalRank_subset_witness M K P ((KF ∩ T : Finset α) : Set α) hKrank
      (by intro e he; exact (by simpa [KF] using (mem_inter.mp he).1))
    have hm := conditionalRank_mono_left M P
      (show ((KF ∩ T : Finset α) : Set α) ⊆ ((S ∩ T : Finset α) : Set α) from by
        intro e he
        rcases mem_inter.mp he with ⟨heK, heT⟩
        exact mem_inter.mpr ⟨hKS (by simpa [KF] using heK), heT⟩)
    rw [hw, Set.ncard_coe_finset] at hm
    exact_mod_cast hm
  have hm := bitsExpectation_mono (fun _ : α => t) (fun _ => ht0) (fun _ => ht1)
    V (fun T _ => hpoint T)
  rw [bitsExpectation_card_inter _ V KF hKF] at hm
  have hcardKF : KF.card = conditionalRank M (S : Set α) P := by
    change K.toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card', hKcard]
  simpa only [sum_const, nsmul_eq_mul, hcardKF, mul_comm] using hm

end MatroidProphet

end OAI
