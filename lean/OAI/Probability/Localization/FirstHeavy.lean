import OAI.Probability.Localization.Cells

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma Descendant.refl {n : ℕ} (Q : Cell n) : Descendant Q Q := ⟨le_rfl,Subset.rfl⟩

lemma Descendant.trans {n : ℕ} {Q R S : Cell n} (hQR : Descendant Q R) (hRS : Descendant R S) :
    Descendant Q S := ⟨hQR.1.trans hRS.1,hRS.2.trans hQR.2⟩

lemma nested_of_point {n : ℕ} (hn : 0 < n) {Q R : Cell n} (h : Q.1 ≤ R.1)
    {z : Coordinate n} (hzQ : z ∈ cellSet Q) (hzR : z ∈ cellSet R) : Descendant Q R := by
  have ha := cellSet_subset_ancestor hn R Q.1 h
  have h₁ := cellAt_eq_of_mem hn Q hzQ
  have h₂ := cellAt_eq_of_mem hn (ancestorCell R Q.1 h) (ha hzR)
  have he : ancestorCell R Q.1 h = Q := h₂.symm.trans h₁
  exact ⟨h,by simpa only [he] using ha⟩

lemma cell_eq_of_level_point {n : ℕ} (hn : 0 < n) {Q R : Cell n} (h : Q.1 = R.1)
    {z : Coordinate n} (hzQ : z ∈ cellSet Q) (hzR : z ∈ cellSet R) : Q = R := by
  have h₁ := cellAt_eq_of_mem hn Q hzQ
  have h₂ := cellAt_eq_of_mem hn R hzR
  rw [h] at h₁
  exact h₁.symm.trans h₂

lemma Descendant.eq_of_level {n : ℕ} (hn : 0 < n) {Q R : Cell n}
    (h : Descendant Q R) (hlev : Q.1 = R.1) : Q = R :=
  cell_eq_of_level_point hn hlev (h.2 (cellCenter_mem hn R)) (cellCenter_mem hn R)

lemma firstHeavy_disjoint {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {R S : Cell n} (hR : FirstHeavy P Q R) (hS : FirstHeavy P Q S) (hne : R ≠ S) :
    Disjoint (cellSet R) (cellSet S) := by
  apply Set.disjoint_left.mpr
  intro z hzR hzS
  rcases le_total R.1 S.1 with h | h
  · exact hne (hS.2 R hR.1 (nested_of_point hn h hzR hzS))
  · exact hne (hR.2 S hS.1 (nested_of_point hn h hzS hzR)).symm

lemma exists_firstHeavy_ancestor {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    {Q R : Cell n} (hR : Heavy P Q R) :
    ∃ E : Cell n,FirstHeavy P Q E ∧ Descendant E R := by
  classical
  have hex : ∃ J : ℕ,∃ E : Cell n,Heavy P Q E ∧ Descendant E R ∧ E.1 = J :=
    ⟨R.1,R,hR,Descendant.refl R,rfl⟩
  obtain ⟨E,hE,hER,hlev⟩ := Nat.find_spec hex
  refine ⟨E,⟨hE,?_⟩,hER⟩
  intro F hF hFE
  have hmin := Nat.find_min' hex (show ∃ E : Cell n,Heavy P Q E ∧ Descendant E R ∧ E.1 = F.1 from
    ⟨F,hF,hFE.trans hER,rfl⟩)
  rw [← hlev] at hmin
  exact hFE.eq_of_level hn (le_antisymm hFE.1 hmin)

lemma measurableSet_residual {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) :
    MeasurableSet (residual P Q) :=
  (measurableSet_cellSet Q).diff (MeasurableSet.iUnion (fun R => measurableSet_cellSet R.val))

lemma measurableSet_branch {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (a : Letter n) :
    MeasurableSet (branch P Q a) := by
  classical
  cases a with
  | none => exact measurableSet_residual P Q
  | some R => by_cases h : FirstHeavy P Q R <;> simp [branch,h,measurableSet_cellSet]

lemma branch_subset {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (a : Letter n) :
    branch P Q a ⊆ cellSet Q := by
  classical
  cases a with
  | none => exact Set.sdiff_subset
  | some R => by_cases h : FirstHeavy P Q R <;> simp only [branch,h,ite_true,ite_false]
              · exact h.1.1.2
              · exact Set.empty_subset _

lemma branch_disjoint {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {a b : Letter n} (hab : a ≠ b) : Disjoint (branch P Q a) (branch P Q b) := by
  classical
  cases a with
  | none =>
    cases b with
    | none => exact False.elim (hab rfl)
    | some R =>
      by_cases h : FirstHeavy P Q R
      · simp only [branch,ite_eq_left h]
        apply Set.disjoint_left.mpr
        intro z hz hzR
        exact hz.2 (Set.mem_iUnion.mpr ⟨⟨R,h⟩,hzR⟩)
      · simp [branch,h]
  | some R =>
    cases b with
    | none =>
      by_cases h : FirstHeavy P Q R
      · simp only [branch,ite_eq_left h]
        apply Set.disjoint_right.mpr
        intro z hz hzR
        exact hz.2 (Set.mem_iUnion.mpr ⟨⟨R,h⟩,hzR⟩)
      · simp [branch,h]
    | some S =>
      by_cases hR : FirstHeavy P Q R
      · by_cases hS : FirstHeavy P Q S
        · simpa only [branch,ite_eq_left hR,ite_eq_left hS] using
            firstHeavy_disjoint hn P Q hR hS (fun h => hab (congrArg some h))
        · simp [branch,hS]
      · simp [branch,hR]

lemma attemptLetter_mem_branch {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : z ∈ branch P Q (attemptLetter P Q z) := by
  classical
  by_cases h : ∃ R : Cell n,FirstHeavy P Q R ∧ z ∈ cellSet R
  · simp only [attemptLetter,dite_eq_left h,branch,ite_eq_left h.choose_spec.1]
    exact h.choose_spec.2
  · simp only [attemptLetter,dite_eq_right h,branch,residual]
    refine ⟨hz,?_⟩
    intro hm
    obtain ⟨R,hR⟩ := Set.mem_iUnion.mp hm
    exact h ⟨R.val,R.property,hR⟩

lemma attemptLetter_eq_iff {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) (a : Letter n) :
    attemptLetter P Q z = a ↔ z ∈ branch P Q a := by
  constructor
  · intro he; rw [← he]; exact attemptLetter_mem_branch P Q hz
  · intro hm
    by_contra he
    exact Set.disjoint_left.mp (branch_disjoint hn P Q he) (attemptLetter_mem_branch P Q hz) hm

lemma heavy_disjoint_residual {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    {Q R : Cell n} (hR : Heavy P Q R) : Disjoint (residual P Q) (cellSet R) := by
  obtain ⟨E,hE,hER⟩ := exists_firstHeavy_ancestor hn P hR
  apply Set.disjoint_left.mpr
  intro z hz hzR
  exact hz.2 (Set.mem_iUnion.mpr ⟨⟨E,hE⟩,hER.2 hzR⟩)

lemma stopped_regular {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hq : (1/2:ℝ) ≤ (P (residual P Q)).toReal) :
    Regular (ProbabilityTheory.cond P (residual P Q)) Q := by
  have hq0 : P (residual P Q) ≠ 0 := by
    intro hzero
    rw [hzero, ENNReal.toReal_zero] at hq
    norm_num at hq
  have hp := ProbabilityTheory.cond_isProbabilityMeasure (μ := P) hq0
  let := hp
  refine ⟨?_,?_⟩
  · apply le_antisymm prob_le_one
    have hself := ProbabilityTheory.cond_apply_self (μ := P) hq0 (measure_ne_top _ _)
    rw [← hself]
    exact measure_mono Set.sdiff_subset
  · intro R hQR hlev
    by_cases hR : Heavy P Q R
    · have hd := heavy_disjoint_residual hn P hR
      rw [ProbabilityTheory.cond_apply' (measurableSet_cellSet R),Set.disjoint_iff_inter_eq_empty.mp hd]
      simp only [measure_empty,mul_zero,ENNReal.toReal_zero]
      exact mul_nonneg (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _).le
    · have hm : (P (cellSet R)).toReal ≤ threshold n (R.1-Q.1) := by
        exact le_of_not_gt (fun h => hR ⟨hQR,hlev,h⟩)
      rw [ProbabilityTheory.cond_apply' (measurableSet_cellSet R),ENNReal.toReal_mul,ENNReal.toReal_inv]
      have hinter : (P (residual P Q ∩ cellSet R)).toReal ≤ (P (cellSet R)).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_right)
      have hpos : 0 < (P (residual P Q)).toReal := by linarith
      have hinv : ((P (residual P Q)).toReal)⁻¹ ≤ 2 := by
        apply (inv_le_comm₀ hpos (by norm_num)).mpr
        simpa only [one_div] using hq
      exact (mul_le_mul_of_nonneg_left (hinter.trans hm) (inv_nonneg.mpr hpos.le)).trans
        (mul_le_mul_of_nonneg_right hinv (Real.rpow_pos_of_pos (by norm_num) _).le)

end FiniteEntropy

end RepeatedLocalization

end OAI
