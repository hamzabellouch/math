import Mathlib
import OAI.Combinatorics.HoneycombCorridor.CollisionWeights
import OAI.Combinatorics.HoneycombCorridor.ConvexDomains

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem rayLeaves_balance (D : Finset Vertex) (v : Vertex) :
    (∑ e ∈ rayLeaves D v, wordWeight e.2) = 3 := by
  rw [rayLeaves,sum_record_fibers]
  simp only [leaf_balance,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num

theorem rayExits_filter (D : Finset Vertex) (v : Vertex) :
    rayExits D v = (rayLeaves D v).filter (fun e => (stemEnd v e).1 ∉ D) := rfl

theorem rayLeaves_split (D : Finset Vertex) (v : Vertex) (hv : v ∈ D) :
    (∑ e ∈ rayLeaves D v, wordWeight e.2) =
      (∑ e ∈ rayExits D v, wordWeight e.2) +
      (∑ e ∈ rayReturns D v, wordWeight e.2) +
      (∑ e ∈ rayCollisions D v, wordWeight e.2) := by
  classical
  rw [rayExits_filter,rayReturns,rayCollisions]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  change wordWeight e.2 = (if (stemEnd v e).1 ∉ D then _ else _) +
    (if (stemEnd v e).1 = v then _ else _) + _
  by_cases hD : (stemEnd v e).1 ∈ D
  · by_cases hEq : (stemEnd v e).1 = v <;> simp [hD,hEq,hv]
  · have hEq : (stemEnd v e).1 ≠ v := fun h => hD (h.symm ▸ hv)
    simp [hD,hEq]

theorem complex_visit_balance (D : Finset Vertex) (v : Vertex) (hD : Filled D) (hv : v ∈ D) :
    (3 : ℂ) = visitSum D v +
      (∑ P ∈ polygons D, if v ∈ P.vertices then
        (2 : ℂ) * (criticalActivity : ℂ) ^ (P.length - 1) *
          (Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)) : ℂ) else 0) +
      (∑ P ∈ polygons D, if v ∈ P.interior then
        -2 * (criticalActivity : ℂ) ^ P.length * visitSum P.interior v else 0) := by
  have h := rayLeaves_split D v hv
  rw [rayLeaves_balance,rayExits_eq_visitSum D v hD hv,
    return_sum_polygons D v hv,collision_sum_polygons D v hD] at h
  exact h

theorem finite_visit_recursion : FiniteVisitRecursion := by
  classical
  intro D v hD hv
  have h := congrArg Complex.reAddGroupHom (complex_visit_balance D v hD hv)
  simp only [map_add,map_sum,Complex.coe_reAddGroupHom,← Complex.ofReal_pow] at h
  have hr : (∑ P ∈ polygons D, (if v ∈ P.vertices then
      (2 : ℂ) * (criticalActivity ^ (P.length - 1) : ℝ) *
        (Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)) : ℂ) else 0).re) =
    -(∑ P ∈ polygons D, if v ∈ P.vertices then
      2 * criticalActivity ^ (P.length - 1) *
        (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro P hP
    split_ifs <;> simp only [Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,
      Complex.mul_re,Complex.mul_im,show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,mul_zero,zero_mul,sub_zero,add_zero]
    all_goals ring
  have hc : (∑ P ∈ polygons D, (if v ∈ P.interior then
      -(2 : ℂ) * (criticalActivity ^ P.length : ℝ) * visitSum P.interior v else 0).re) =
    -(∑ P ∈ polygons D, if v ∈ P.interior then
      2 * criticalActivity ^ P.length * visitMass P.interior v else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro P hP
    split_ifs <;> simp only [visitMass,Complex.mul_re,Complex.mul_im,Complex.neg_re,
      Complex.neg_im,show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
      Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,mul_zero,zero_mul,
      neg_zero,sub_zero,add_zero]
    all_goals ring
  rw [hr,hc] at h
  change _ = visitMass D v + _ + _ at h
  norm_num only [show (3 : ℂ).re = 3 from rfl] at h
  linarith


theorem criticalActivity_pos : 0 < criticalActivity := by
  unfold criticalActivity
  exact inv_pos.mpr (mul_pos (by norm_num) critical_cos_pos)

theorem Polygon.ccwTurn_cases (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    P.ccwTurn v = Real.pi / 3 ∨ P.ccwTurn v = -(Real.pi / 3) := by
  obtain ⟨k,w,hw⟩ := P.exists_rooted v hv
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hw.1
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator (v,k) (b :: u)
    (by simp) hw.2.1 hw.2.2.1
  have he := P.ccwTurn_traversal (v,k) b u hw p ε hp hε hvals
  rcases hε with rfl | rfl <;> cases b <;> simp [turnUnit] at he <;> simp [he]

theorem through_cos_pos (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    0 < -Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)) := by
  have hpi := Real.pi_pos
  rcases P.ccwTurn_cases v hv with h | h
  · rw [h,show (3 / 8 : ℝ) * (2 * Real.pi - Real.pi / 3) = Real.pi - 3 * Real.pi / 8 by ring,
      Real.cos_pi_sub,neg_neg]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  · rw [h,show (3 / 8 : ℝ) * (2 * Real.pi - -(Real.pi / 3)) = Real.pi - Real.pi / 8 by ring,
      Real.cos_pi_sub,neg_neg]
    exact critical_cos_pos

theorem recursion_coefficients_positive (P : Polygon) :
    0 < 2 * criticalActivity ^ P.length ∧ ∀ v ∈ P.vertices,
      0 < 2 * criticalActivity ^ (P.length - 1) *
        (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) := by
  constructor
  · exact mul_pos (by norm_num) (pow_pos criticalActivity_pos _)
  · intro v hv
    exact mul_pos (mul_pos (by norm_num) (pow_pos criticalActivity_pos _)) (through_cos_pos P v hv)

theorem visitMass_ge_three (D : Finset Vertex) (v : Vertex) (hD : Filled D) (hv : v ∈ D) :
    3 ≤ visitMass D v := by
  classical
  induction hn : D.card using Nat.strong_induction_on generalizing D with
  | h n ih =>
      rw [finite_visit_recursion D v hD hv]
      have hp : 0 ≤ ∑ P ∈ polygons D, if v ∈ P.vertices then
          2 * criticalActivity ^ (P.length - 1) *
            (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) else 0 := by
        apply Finset.sum_nonneg
        intro P hP
        split_ifs with hvP
        · exact (recursion_coefficients_positive P).2 v hvP |>.le
        · exact le_rfl
      have hi : 0 ≤ ∑ P ∈ polygons D, if v ∈ P.interior then
          2 * criticalActivity ^ P.length * visitMass P.interior v else 0 := by
        apply Finset.sum_nonneg
        intro P hP
        split_ifs with hvP
        · have hl : P.interior.card < n := hn ▸ P.interior_card_lt D hD hP
          have hmass := ih P.interior.card hl P.interior P.interior_filled hvP rfl
          exact mul_nonneg (recursion_coefficients_positive P).1.le (by linarith)
        · exact le_rfl
      linarith

theorem polygons_mono {D E : Finset Vertex} (hDE : D ⊆ E) : polygons D ⊆ polygons E := by
  intro P hP
  exact (mem_polygons E P).mpr ((mem_polygons D P).mp hP |>.trans hDE)

theorem visitMass_mono (D E : Finset Vertex) (v : Vertex)
    (hD : Filled D) (hE : Filled E) (hDE : D ⊆ E) (hv : v ∈ D) :
    visitMass D v ≤ visitMass E v := by
  classical
  rw [finite_visit_recursion D v hD hv,finite_visit_recursion E v hE (hDE hv)]
  apply add_le_add
  · apply add_le_add le_rfl
    apply Finset.sum_le_sum_of_subset_of_nonneg (polygons_mono hDE)
    intro P hP hn
    split_ifs with hvP
    · exact (recursion_coefficients_positive P).2 v hvP |>.le
    · exact le_rfl
  · apply Finset.sum_le_sum_of_subset_of_nonneg (polygons_mono hDE)
    intro P hP hn
    split_ifs with hvP
    · have hmass := visitMass_ge_three P.interior v P.interior_filled hvP
      exact mul_nonneg (recursion_coefficients_positive P).1.le (by linarith)
    · exact le_rfl



theorem wordWeight_re (w : List Bool) : (wordWeight w).re =
    criticalActivity ^ w.length * Real.cos (Real.pi / 8 * (turnUnits w : ℝ)) := by
  rw [wordWeight_turnUnits]
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.exp_ofReal_mul_I_re]

theorem wordWeight_re_le (w : List Bool) :
    (wordWeight w).re ≤ criticalActivity ^ w.length := by
  rw [wordWeight_re]
  exact mul_le_of_le_one_right (pow_nonneg criticalActivity_pos.le _) (Real.cos_le_one _)

theorem bounded_turn_cos (m : ℤ) (hm : -3 ≤ m ∧ m ≤ 3) :
    Real.cos (3 * Real.pi / 8) ≤ Real.cos (Real.pi / 8 * (m : ℝ)) := by
  have hlow : -(3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
  have hhigh : (m : ℝ) ≤ 3 := by exact_mod_cast hm.2
  have habs : |Real.pi / 8 * (m : ℝ)| ≤ 3 * Real.pi / 8 := by
    apply abs_le.mpr
    constructor <;> nlinarith [Real.pi_pos]
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (Real.pi / 8 * (m : ℝ)))
    (show 3 * Real.pi / 8 ≤ Real.pi by linarith [Real.pi_pos]) habs
  simpa only [Real.cos_abs] using h

theorem convex_wordWeight_re_lower (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (e : Germ × List Bool) (he : IsExcursion D e) :
    Real.cos (3 * Real.pi / 8) * criticalActivity ^ e.2.length ≤ (wordWeight e.2).re := by
  rw [wordWeight_re,mul_comm (Real.cos _)]
  exact mul_le_mul_of_nonneg_left
    (bounded_turn_cos (turnUnits e.2) (convex_excursion_turn_bound D hD e he))
    (pow_nonneg criticalActivity_pos.le _)

theorem visitMass_excursion_upper (D : Finset Vertex) (v : Vertex) :
    visitMass D v ≤ excursionMass D v := by
  classical
  simp only [visitMass,visitSum,excursionMass,Complex.re_sum]
  apply Finset.sum_le_sum
  intro e he
  split_ifs <;> try simp only [Complex.zero_re,le_refl]
  exact wordWeight_re_le _

theorem visitMass_excursion_lower (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (v : Vertex) :
    Real.cos (3 * Real.pi / 8) * excursionMass D v ≤ visitMass D v := by
  classical
  simp only [visitMass,visitSum,excursionMass,Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  split_ifs <;> try simp only [mul_zero,Complex.zero_re,le_refl]
  exact convex_wordWeight_re_lower D hD e ((mem_excursions D e).mp he)

end PolynomialVacuumBridge.Corridor

end

end OAI
