import OAI.NumberTheory.JointDickman.Amplification.AdditionScaleDichotomy
import OAI.NumberTheory.JointDickman.Amplification.LowCardinalityPartition
import OAI.NumberTheory.JointDickman.Amplification.SmallCandidateMultiplicity
import OAI.NumberTheory.JointDickman.Arithmetic.CandidateExceptionalPrimes

namespace OAI

/-! # Covering the actual candidate representations by addition classes -/

namespace JointDickman
open Finset Classical

private theorem endpoint_box_exp_bound {B T c b : ℕ} (hB : 5 ≤ B)
    (hT : (T : ℝ) ≤ Real.exp B) (hc : (c : ℝ) ≤ Real.exp (2*B))
    (hb : b ≤ 2*T*c) : (b : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) := by
  have hB' : (5 : ℝ) ≤ B := by exact_mod_cast hB
  have htwo : (2 : ℝ) ≤ Real.exp ((B : ℝ)/5) := by
    linarith [Real.add_one_le_exp ((B : ℝ)/5)]
  calc
    (b : ℝ) ≤ 2*T*c := by exact_mod_cast hb
    _ ≤ 2*Real.exp (B : ℝ)*Real.exp (2*B) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hT (by norm_num)) hc
        (Nat.cast_nonneg _) (by positivity)
    _ = 2*Real.exp (3*(B : ℝ)) := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp ((B : ℝ)/5)*Real.exp (3*B) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Each actual representation is either small at both endpoints, or is
in a later grid class with a large addition at one of its endpoints. -/
theorem candidatePairRepresentations_addition_cover
    {B L T H M : ℕ} {τ C : ℝ} (hB : 5 ≤ B) (hL : 3 ≤ L)
    (hT : (T : ℝ) ≤ Real.exp B) (i t : Fin M) (A D U V : Finset ℕ)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (hU : U ⊆ auxiliaryPrimes B) (hV : V ⊆ auxiliaryPrimes B)
    {ab : Finset ℕ × Finset ℕ}
    (hab : ab ∈ candidatePairRepresentations B L T H τ C i t (A ∪ U) (D ∪ V)) :
    ab ∈ smallCandidateAlternatives B L T H τ C i t A D U V ∨
      ∃ k ∈ Icc 4 L,
        ab ∈ allLargeLowAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) A U D V ∨
        ab.swap ∈ allLargeHighAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) D V A U := by
  obtain ⟨hm,he⟩ := mem_filter.mp hab
  obtain ⟨ha,hd⟩ := mem_product.mp hm
  have ha' := mem_endpointSplits.mp ha
  have hd' := mem_endpointSplits.mp hd
  have hZ : ab.1 \ A ⊆ auxiliaryPrimes B :=
    sdiff_subset.trans (ha'.1.trans (union_subset hA hU))
  have hY : ab.2 \ D ⊆ auxiliaryPrimes B :=
    sdiff_subset.trans (hd'.1.trans (union_subset hD hV))
  rcases addition_scale_dichotomy hL hZ hY with hs | ⟨k,hk,hz,hy,hl⟩
  · exact Or.inl (mem_filter.mpr ⟨hab,hs⟩)
  · right
    let e : BlockCandidateIndex M := ((i,t),ab)
    have he' : BlockCandidateAdmissible B L T H τ C e := he
    have hcsize := (candidate_quotient_exp_bounds he').2
    obtain ⟨_,_,_,hc,hrel,_,_,_,_,hcr,_,_,hlo,hhi,hdlo,hdhi⟩ := he'
    have hsizea := endpoint_box_exp_bound hB hT hcsize hhi
    have hsized := endpoint_box_exp_bound hB hT hcsize hdhi
    have hratiod : candidateHigh e ≤ 2*candidateLow e :=
      hdhi.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left 2 hlo)
    have hgeq : ((k : ℝ)-1)/L = (k : ℝ)/L-1/(L : ℝ) := by ring
    rw [hgeq] at hl
    have haReg : ab.1 ∈ regularSmallAlternatives B L k τ C A U :=
      mem_filter.mpr ⟨mem_powerset.mpr ha'.1,ha'.2.1,hz⟩
    have hdReg : ab.2 ∈ regularSmallAlternatives B L k τ C D V :=
      mem_filter.mpr ⟨mem_powerset.mpr hd'.1,hd'.2.1,hy⟩
    dsimp only [e,candidateLow,candidateHigh,candidateLag] at hrel hsizea hsized hratiod
    refine ⟨k,hk,?_⟩
    rcases hl with hl | hl
    · left
      exact mem_filter.mpr ⟨mem_product.mpr ⟨haReg,hdReg⟩,
        hl,hratiod,hsizea,hsized,candidateQuotient e,hc,hrel.symm,hcr⟩
    · right
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hdReg,haReg⟩,
        hl,hratiod,hsized,hsizea,candidateQuotient e,hc,hrel,hcr⟩

/-- A finite cardinal bound retaining every representation and both endpoint
orientations. No uniqueness of a coefficient pair is assumed. -/
theorem candidatePairRepresentations_card_le_addition_classes
    {B L T H M : ℕ} {τ C : ℝ} (hB : 5 ≤ B) (hL : 3 ≤ L)
    (hT : (T : ℝ) ≤ Real.exp B) (i t : Fin M) (A D U V : Finset ℕ)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (hU : U ⊆ auxiliaryPrimes B) (hV : V ⊆ auxiliaryPrimes B) :
    (candidatePairRepresentations B L T H τ C i t (A ∪ U) (D ∪ V)).card ≤
      (smallCandidateAlternatives B L T H τ C i t A D U V).card +
      ∑ k ∈ Icc 4 L,
        ((allLargeLowAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) A U D V).card +
         (allLargeHighAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) D V A U).card) := by
  let lo := fun k => allLargeLowAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) A U D V
  let hi := fun k => allLargeHighAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) D V A U
  have hsub : candidatePairRepresentations B L T H τ C i t (A ∪ U) (D ∪ V) ⊆
      smallCandidateAlternatives B L T H τ C i t A D U V ∪
        (Icc 4 L).biUnion (fun k => lo k ∪ (hi k).image Prod.swap) := by
    intro ab hab
    rcases candidatePairRepresentations_addition_cover hB hL hT i t A D U V hA hD hU hV hab with hs | ⟨k,hk,hh⟩
    · exact mem_union_left _ hs
    · apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨k,hk,?_⟩
      rcases hh with hl | hh
      · exact mem_union_left _ hl
      · exact mem_union_right _ (mem_image.mpr ⟨ab.swap,hh,Prod.swap_swap ab⟩)
  calc
    _ ≤ (smallCandidateAlternatives B L T H τ C i t A D U V ∪
        (Icc 4 L).biUnion (fun k => lo k ∪ (hi k).image Prod.swap)).card := card_le_card hsub
    _ ≤ (smallCandidateAlternatives B L T H τ C i t A D U V).card +
        ((Icc 4 L).biUnion (fun k => lo k ∪ (hi k).image Prod.swap)).card := card_union_le _ _
    _ ≤ (smallCandidateAlternatives B L T H τ C i t A D U V).card +
        ∑ k ∈ Icc 4 L, ((lo k).card+(hi k).card) := by
      apply Nat.add_le_add_left
      exact card_biUnion_le.trans (sum_le_sum (fun k _ => (card_union_le _ _).trans
        (Nat.add_le_add_left card_image_le _)))

end JointDickman

end OAI
