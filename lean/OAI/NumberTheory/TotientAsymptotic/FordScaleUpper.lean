import OAI.NumberTheory.TotientAsymptotic.FordStructureCount
import OAI.NumberTheory.TotientAsymptotic.FordSimplexGoodCount

namespace OAI

/-! The upper half of Ford's counting scale, assembled on actual totient values. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem ford_scale_upper : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop, V x ≤ C*(x/Real.log x)*G x (m x) := by
  classical
  obtain ⟨A,hA,hsmall⟩ := small_head_real_gaussian
  obtain ⟨D,hD,hbad⟩ := ford_structure_value_count
  obtain ⟨E,hE,hgood⟩ := ford_simplex_good_value_count
  refine ⟨A+D+E,by positivity,?_⟩
  filter_upwards [hsmall,hbad,hgood,eventually_ge_atTop (0:ℝ),
    m_tendsto.eventually (eventually_gt_atTop 0)] with x hs hb hg hx hm
  let Q := (Finset.Icc 1 ⌊x⌋₊).filter IsTotient
  let U := Q.filter (fun v => (fordPrime (ell v) 0:ℝ) < x^(1/4:ℝ))
  let W := Q.filter (fun v => ¬fordSimplexCondition x 0 (ell v))
  let T := Q.filter (fun v => x^(1/4:ℝ) ≤ fordPrime (ell v) 0 ∧
    fordSimplexCondition x 0 (ell v))
  have hmem (v) (hv : v ∈ Q) : IsTotient v ∧ (v:ℝ) ≤ x := by
    obtain ⟨hv,ht⟩ := Finset.mem_filter.mp hv
    exact ⟨ht,(Nat.cast_le.mpr (Finset.mem_Icc.mp hv).2).trans (Nat.floor_le hx)⟩
  have hU := hs 0 (by omega) U (by
    intro v hv
    obtain ⟨hv,hhead⟩ := Finset.mem_filter.mp hv
    obtain ⟨ht,hvx⟩ := hmem v hv
    exact ⟨ht,hvx,ell v,(ell_spec ht).1,(ell_spec ht).2,hhead⟩)
  have hW := hb 0 hm W ell (by
    intro v hv
    obtain ⟨hv,hfail⟩ := Finset.mem_filter.mp hv
    obtain ⟨ht,hvx⟩ := hmem v hv
    exact ⟨(ell_spec ht).1,(ell_spec ht).2,hvx,hfail⟩)
  have hT := hg T ell (by
    intro v hv
    obtain ⟨hv,hhead,hsimplex⟩ := Finset.mem_filter.mp hv
    obtain ⟨ht,hvx⟩ := hmem v hv
    exact ⟨(ell_spec ht).1,(ell_spec ht).2,hhead,hvx,hsimplex⟩)
  have hcover : Q ⊆ U ∪ W ∪ T := by
    intro v hv
    by_cases hu : (fordPrime (ell v) 0:ℝ) < x^(1/4:ℝ)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hv,hu⟩))
    by_cases hw : fordSimplexCondition x 0 (ell v)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,le_of_not_gt hu,hw⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hv,hw⟩))
  have hc : (Q.card:ℝ) ≤ (U.card:ℝ)+W.card+T.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  norm_num only [Nat.cast_zero,zero_pow (by norm_num : 2≠0),neg_zero,
    zero_div,Real.exp_zero,mul_one] at hU hW
  change (Q.card:ℝ) ≤ _
  calc
    _ ≤ (U.card:ℝ)+W.card+T.card := hc
    _ ≤ A*(x/Real.log x)*G x (m x)+D*(x/Real.log x)*G x (m x)+
        E*(x/Real.log x)*G x (m x) := add_le_add (add_le_add hU hW) hT
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
