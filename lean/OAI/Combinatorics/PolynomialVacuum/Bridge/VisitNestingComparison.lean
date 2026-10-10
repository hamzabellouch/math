import OAI.Combinatorics.HoneycombCorridor.VisitRecursion
import OAI.Combinatorics.PolynomialVacuum.Geometry.IncidentNesting

namespace OAI

namespace PolynomialVacuumBridge.Corridor

theorem Polygon.faceCount_cases (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    faceCount P.interiorFaces v = 1 ∨ faceCount P.interiorFaces v = 2 := by
  obtain ⟨k,w,hw⟩ := P.exists_rooted v hv
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hw.1
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator (v,k) (b :: u)
    (by simp) hw.2.1 hw.2.2.1
  have hs : p.support = P.interiorFaces := (P.interiorFaces_of_traversal (v,k) (b :: u) hw.2.1 hw.2.2.1 hw.2.2.2 p hp).symm
  have ht := contour_faceCount_turn p ε hε hvals _ hp (v,k) b
    ((simple_closed_word_contour _ _ hw.2.1 hw.2.2.1).1)
  rw [hs] at ht
  rcases hε with rfl | rfl <;> cases b <;> simp [turnUnit] at ht <;> omega

theorem through_power_ratio (x c m : ℝ) (n : ℕ) (hx : x ≠ 0) (hm : m ≠ 0) (hn : 0 < n) :
    2 * x ^ (n - 1) * c = (c / (x * m)) * (2 * m * x ^ n) := by
  have he : x ^ n = x ^ (n - 1) * x := by
    rw [← pow_succ]
    congr 1
    omega
  rw [he]
  field_simp

noncomputable def lowThroughRatio : ℝ := Real.cos (3 * Real.pi / 8) / criticalActivity
noncomputable def highThroughRatio : ℝ := Real.cos (Real.pi / 8) / (2 * criticalActivity)

theorem lowThroughRatio_pos : 0 < lowThroughRatio := by
  apply div_pos _ criticalActivity_pos
  apply Real.cos_pos_of_mem_Ioo
  have hpi := Real.pi_pos
  constructor <;> linarith

theorem highThroughRatio_pos : 0 < highThroughRatio :=
  div_pos critical_cos_pos (mul_pos (by norm_num) criticalActivity_pos)

theorem through_coefficient_two_ratios (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    ∃ r : ℝ, (r = lowThroughRatio ∨ r = highThroughRatio) ∧
      2 * criticalActivity ^ (P.length - 1) *
        (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) =
        r * (2 * (faceCount P.interiorFaces v : ℝ) * criticalActivity ^ P.length) := by
  have hx := ne_of_gt criticalActivity_pos
  rcases P.faceCount_cases v hv with hm | hm
  · refine ⟨lowThroughRatio,Or.inl rfl,?_⟩
    have ht : P.ccwTurn v = Real.pi / 3 := by simp only [Polygon.ccwTurn,hm,Int.cast_one]; ring
    rw [ht,hm]
    norm_num only [Int.cast_one,mul_one]
    rw [show (3 / 8 : ℝ) * (2 * Real.pi - Real.pi / 3) = Real.pi - 3 * Real.pi / 8 by ring,
      Real.cos_pi_sub,neg_neg]
    simpa only [mul_one,lowThroughRatio] using
      through_power_ratio criticalActivity (Real.cos (3 * Real.pi / 8)) 1 P.length hx one_ne_zero P.length_pos
  · refine ⟨highThroughRatio,Or.inr rfl,?_⟩
    have ht : P.ccwTurn v = -(Real.pi / 3) := by simp only [Polygon.ccwTurn,hm,Int.cast_ofNat]; ring
    rw [ht,hm]
    norm_num only [Int.cast_ofNat]
    rw [show (3 / 8 : ℝ) * (2 * Real.pi - -(Real.pi / 3)) = Real.pi - Real.pi / 8 by ring,
      Real.cos_pi_sub,neg_neg]
    simpa only [highThroughRatio,mul_comm criticalActivity (2 : ℝ), show (2 : ℝ) * 2 = 4 by norm_num] using
      through_power_ratio criticalActivity (Real.cos (Real.pi / 8)) 2 P.length hx (by norm_num) P.length_pos

noncomputable def visitLowerConstant : ℝ := min 1 (min lowThroughRatio highThroughRatio)
noncomputable def visitUpperConstant : ℝ := max 1 (max lowThroughRatio highThroughRatio)

theorem visit_constants_positive : 0 < visitLowerConstant ∧ 0 < visitUpperConstant := by
  constructor
  · exact lt_min (by norm_num) (lt_min lowThroughRatio_pos highThroughRatio_pos)
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)

theorem through_coefficient_bounds (P : Polygon) (v : Vertex) (hv : v ∈ P.vertices) :
    visitLowerConstant * (2 * (faceCount P.interiorFaces v : ℝ) * criticalActivity ^ P.length) ≤
      2 * criticalActivity ^ (P.length - 1) *
        (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) ∧
    2 * criticalActivity ^ (P.length - 1) *
        (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) ≤
      visitUpperConstant * (2 * (faceCount P.interiorFaces v : ℝ) * criticalActivity ^ P.length) := by
  obtain ⟨r,hr,he⟩ := through_coefficient_two_ratios P v hv
  have hnon : 0 ≤ 2 * (faceCount P.interiorFaces v : ℝ) * criticalActivity ^ P.length := by
    have hm : 0 < (faceCount P.interiorFaces v : ℝ) := by
      rcases P.faceCount_cases v hv with h | h <;> norm_num [h]
    exact (mul_pos (mul_pos (by norm_num) hm) (pow_pos criticalActivity_pos _)).le
  have hc : visitLowerConstant ≤ r ∧ r ≤ visitUpperConstant := by
    rcases hr with rfl | rfl
    · exact ⟨(min_le_right _ _).trans (min_le_left _ _),(le_max_left _ _).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (min_le_right _ _),(le_max_right _ _).trans (le_max_right _ _)⟩
  rw [he]
  exact ⟨mul_le_mul_of_nonneg_right hc.1 hnon,mul_le_mul_of_nonneg_right hc.2 hnon⟩

 

theorem visitMass_incident_comparison (D : Finset Vertex) (v : Vertex)
    (hD : Filled D) (hv : v ∈ D) :
    visitLowerConstant * incidentNestingMass D v ≤ visitMass D v ∧
    visitMass D v ≤ visitUpperConstant * incidentNestingMass D v := by
  classical
  induction hn : D.card using Nat.strong_induction_on generalizing D with
  | h n ih =>
    rw [finite_visit_recursion D v hD hv,incidentNestingMass_recursion D v hD]
    simp only [mul_add,Finset.mul_sum]
    have hbase : visitLowerConstant * 3 ≤ 3 ∧ 3 ≤ visitUpperConstant * 3 := by
      have hl : visitLowerConstant ≤ 1 := min_le_left _ _
      have hu : 1 ≤ visitUpperConstant := le_max_left _ _
      constructor <;> linarith
    have hb :
        (∑ P ∈ polygons D, visitLowerConstant * (if v ∈ P.vertices then
          2 * (faceCount P.interiorFaces v : ℝ) * criticalActivity ^ P.length else 0)) ≤
        (∑ P ∈ polygons D, if v ∈ P.vertices then
          2 * criticalActivity ^ (P.length - 1) *
            (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) else 0) ∧
        (∑ P ∈ polygons D, if v ∈ P.vertices then
          2 * criticalActivity ^ (P.length - 1) *
            (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) else 0) ≤
        (∑ P ∈ polygons D, visitUpperConstant * (if v ∈ P.vertices then
          2 * (faceCount P.interiorFaces v : ℝ) * criticalActivity ^ P.length else 0)) := by
      constructor <;> apply Finset.sum_le_sum <;> intro P hP
      · split_ifs with hvP
        · exact (through_coefficient_bounds P v hvP).1
        · simp
      · split_ifs with hvP
        · exact (through_coefficient_bounds P v hvP).2
        · simp
    have hint (P : Polygon) (hP : P ∈ polygons D) (hvP : v ∈ P.interior) :
        visitLowerConstant * incidentNestingMass P.interior v ≤ visitMass P.interior v ∧
        visitMass P.interior v ≤ visitUpperConstant * incidentNestingMass P.interior v :=
      ih P.interior.card (hn ▸ P.interior_card_lt D hD hP) P.interior P.interior_filled hvP rfl
    have hi :
        (∑ P ∈ polygons D, visitLowerConstant * (if v ∈ P.interior then
          2 * criticalActivity ^ P.length * incidentNestingMass P.interior v else 0)) ≤
        (∑ P ∈ polygons D, if v ∈ P.interior then
          2 * criticalActivity ^ P.length * visitMass P.interior v else 0) ∧
        (∑ P ∈ polygons D, if v ∈ P.interior then
          2 * criticalActivity ^ P.length * visitMass P.interior v else 0) ≤
        (∑ P ∈ polygons D, visitUpperConstant * (if v ∈ P.interior then
          2 * criticalActivity ^ P.length * incidentNestingMass P.interior v else 0)) := by
      constructor <;> apply Finset.sum_le_sum <;> intro P hP
      · split_ifs with hvP
        · have h := mul_le_mul_of_nonneg_left (hint P hP hvP).1 (recursion_coefficients_positive P).1.le
          nlinarith only [h]
        · simp
      · split_ifs with hvP
        · have h := mul_le_mul_of_nonneg_left (hint P hP hvP).2 (recursion_coefficients_positive P).1.le
          nlinarith only [h]
        · simp
    exact ⟨add_le_add (add_le_add hbase.1 hb.1) hi.1,
      add_le_add (add_le_add hbase.2 hb.2) hi.2⟩

end PolynomialVacuumBridge.Corridor

end OAI
