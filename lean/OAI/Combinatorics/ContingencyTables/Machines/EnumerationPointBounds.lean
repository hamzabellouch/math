import OAI.Combinatorics.ContingencyTables.Sampling.ExactPrintCost
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileBoxEnumeration

namespace OAI

/-! # Individual enumeration points have polynomial binary size -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma gridCoordinates_weight (z : GridEnumerationData) (hz : 0 < z.2) (i : ℕ) :
    weight (gridCoordinates (z,i)) ≤ z.1.length*(4*weight z.2+2)+1 := by
  rw [gridCoordinates_eq]
  apply ExactPrintCost.weight_ofFn
  intro j
  exact weight_nat_small (Nat.le_of_lt (Nat.mod_lt _ hz))

lemma gridWords_point_weight (z : GridEnumerationData) (hz : 0 < z.2)
    (w : List ℕ) (hw : w∈gridWords z) :
    weight w ≤ z.1.length*(4*weight z.2+2)+1 := by
  rw [gridWords] at hw
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
  exact gridCoordinates_weight z hz i

lemma splitViews_weight (n : ℕ) (w : List ℕ) : weight (splitViews (n,w))=weight w+2 := by
  have h := weight_append (w.take n) (w.drop n)
  rw [List.take_append_drop] at h
  simp only [splitViews,weight_prod]
  omega

lemma profileBoxViews_length (z : ProfileCheckData) :
    (profileBoxViews z).length=gridStateCount (profileEnumerationData z) := by
  simp only [profileBoxViews,List.length_map,gridWords,List.length_range]

lemma profileBoxViews_point_weight (z : ProfileCheckData) (v : List ℕ×List ℕ)
    (hv : v∈profileBoxViews z) :
    weight v ≤ (2*z.1.1.1.length)*(4*weight (z.2+1)+2)+3 := by
  rw [profileBoxViews] at hv
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  have hb := gridWords_point_weight (profileEnumerationData z) (by
    change 0 < z.2+1
    omega) w hw
  simp only [profileEnumerationData,List.length_map,List.length_append] at hb
  rw [←two_mul] at hb
  rw [splitViews_weight]
  omega

/-- Exponentially many enumerated points do not make any one point's
binary representation exponentially large. -/
theorem profileBoxViews_point_polynomial : ∃ p : Polynomial ℕ,
    ∀ z v,v∈profileBoxViews z → weight v ≤ p.eval (weight z) := by
  obtain ⟨p,hp⟩ := polynomial_successor
  refine ⟨2*X*(4*p+2)+3,?_⟩
  intro z v hv
  have hw : weight z.2 ≤ weight z := weight_snd z
  have hu : weight (z.2+1) ≤ p.eval (weight z) :=
    (Nat.le_add_left _ _).trans ((hp z.2).trans (polynomial_eval_monotone p hw))
  have hc : z.1.1.1.length ≤ weight z :=
    (list_length_le_weight _).trans ((weight_fst _).trans ((weight_fst _).trans (weight_fst z)))
  have h := profileBoxViews_point_weight z v hv
  simp only [eval_add,eval_mul,eval_ofNat,eval_X]
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul
    (Nat.mul_le_mul_left 2 hc) (by omega)) 3)

end ContingencyTables.ProfilePrograms

end OAI
