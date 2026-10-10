import OAI.Probability.SwitchChain.SliceMoments
import OAI.Probability.SwitchChain.SliceEquality

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized

variable {V : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V]

abbrev State (V : Type*) [Fintype V] (q : ℕ) :=
  ↥((Finset.univ : Finset V).powersetCard q)

abbrev Space (V : Type*) [Fintype V] (q : ℕ) := EuclideanSpace ℝ (State V q)

def raw (q : ℕ) (i j : V) : Space V q :=
  WithLp.toLp 2 (fun S => if i = j then 0 else
    SliceMoments.centeredEqual Finset.univ q i j S.val)

def denominator (V : Type*) [Fintype V] (q : ℕ) : ℝ :=
  Real.sqrt (2 * (Nat.choose (Fintype.card V) q : ℝ) *
    SliceMoments.equalMean (Finset.univ : Finset V) q *
      (1 - SliceMoments.equalMean (Finset.univ : Finset V) q))

def column (q : ℕ) (i j : V) : Space V q :=
  (denominator V q)⁻¹ • raw q i j

@[simp] theorem raw_diag (q : ℕ) (i : V) : raw q i i = 0 := by
  ext S
  simp [raw]

@[simp] theorem column_diag (q : ℕ) (i : V) : column q i i = 0 := by
  simp [column]

theorem raw_symmetric (q : ℕ) (i j : V) : raw q i j = raw q j i := by
  ext S
  simp [raw, SliceMoments.centeredEqual, SliceMoments.equalIndicator, eq_comm, iff_comm]

theorem column_symmetric (q : ℕ) (i j : V) : column q i j = column q j i := by
  rw [column, column, raw_symmetric q i j]

theorem coord_sum (q : ℕ) (S : State V q) :
    ∑ i, SliceMoments.coord i S.val = (q : ℝ) := by
  have hcard := (Finset.mem_powersetCard.mp S.property).2
  simp [SliceMoments.coord, ← hcard]

theorem centered_eq_binary (q : ℕ) (S : State V q) (i j : V) :
    SliceEquality.centeredEquality (fun k => SliceMoments.coord k S.val)
      (SliceMoments.equalMean (Finset.univ : Finset V) q) i j =
    SliceMoments.centeredEqual Finset.univ q i j S.val := by
  unfold SliceEquality.centeredEquality SliceEquality.equalityIndicator
    SliceMoments.centeredEqual SliceMoments.equalIndicator SliceMoments.coord
  by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val <;> simp [hi, hj]

theorem raw_total (q : ℕ) (hN : 2 ≤ Fintype.card V) :
    (∑ i, ∑ j, raw q i j : Space V q) = 0 := by
  ext S
  have hb (i : V) : SliceMoments.coord i S.val = 0 ∨
      SliceMoments.coord i S.val = 1 := by
    by_cases hi : i ∈ S.val <;> simp [SliceMoments.coord, hi]
  have ht := SliceEquality.centeredEquality_total_zero hN
    (fun i => SliceMoments.coord i S.val) hb (q : ℝ) (coord_sum q S)
  have hp : SliceMoments.equalMean (Finset.univ : Finset V) q =
      ((q : ℝ) * (q - 1) + ((Fintype.card V : ℝ) - q) *
        ((Fintype.card V : ℝ) - q - 1)) /
        ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by
    simp [SliceMoments.equalMean]
  rw [← hp] at ht
  simp_rw [SliceEquality.offDiagonal, centered_eq_binary q S] at ht
  simpa [raw, SliceEquality.offDiagonal] using ht

theorem column_total (q : ℕ) (hN : 2 ≤ Fintype.card V) :
    (∑ i, ∑ j, column q i j : Space V q) = 0 := by
  simp only [column, ← Finset.smul_sum, raw_total q hN, smul_zero]

theorem raw_inner (q : ℕ) (hq : q ≤ Fintype.card V)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l) :
    ⟪raw q i j, raw q k l⟫ = (Nat.choose (Fintype.card V) q : ℝ) *
      SliceMoments.average Finset.univ q (fun S =>
        SliceMoments.centeredEqual Finset.univ q i j S *
        SliceMoments.centeredEqual Finset.univ q k l S) := by
  have hc : (Nat.choose (Fintype.card V) q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  simp only [raw, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    star_trivial, hij, hkl, ite_false]
  change (∑ S : ↥((Finset.univ : Finset V).powersetCard q),
    SliceMoments.centeredEqual Finset.univ q k l S.val *
    SliceMoments.centeredEqual Finset.univ q i j S.val) = _
  rw [Finset.sum_coe_sort ((Finset.univ : Finset V).powersetCard q)
    (fun S => SliceMoments.centeredEqual Finset.univ q k l S *
      SliceMoments.centeredEqual Finset.univ q i j S)]
  simp only [SliceMoments.average, Finset.card_univ]
  field_simp
  simp only [mul_comm]

theorem raw_norm_sq (q : ℕ) (hq : q ≤ Fintype.card V)
    (i j : V) (hij : i ≠ j) :
    ‖raw q i j‖ ^ 2 = (Nat.choose (Fintype.card V) q : ℝ) *
      (SliceMoments.equalMean (Finset.univ : Finset V) q *
        (1 - SliceMoments.equalMean (Finset.univ : Finset V) q)) := by
  rw [← real_inner_self_eq_norm_sq, raw_inner q hq i j i j hij hij]
  simp_rw [← pow_two]
  rw [SliceMoments.average_centeredEqual_sq Finset.univ q
    (by simpa using hq) i j (Finset.mem_univ i) (Finset.mem_univ j) hij]

include sectionDecidableEqV in
theorem denominator_sq (q : ℕ)
    (hp : 0 ≤ SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q ≤ 1) :
    denominator V q ^ 2 = 2 * (Nat.choose (Fintype.card V) q : ℝ) *
      SliceMoments.equalMean (Finset.univ : Finset V) q *
        (1 - SliceMoments.equalMean (Finset.univ : Finset V) q) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  apply Real.sq_sqrt
  exact mul_nonneg (mul_nonneg (by positivity) hp) (sub_nonneg.mpr hp1)

theorem column_inner_unsimplified (q : ℕ) (hq : q ≤ Fintype.card V)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l) :
    ⟪column q i j, column q k l⟫ =
      ((Nat.choose (Fintype.card V) q : ℝ) / denominator V q ^ 2) *
      SliceMoments.average Finset.univ q (fun S =>
        SliceMoments.centeredEqual Finset.univ q i j S *
        SliceMoments.centeredEqual Finset.univ q k l S) := by
  rw [column, column, inner_smul_left, inner_smul_right,
    raw_inner q hq i j k l hij hkl]
  simp only [RCLike.conj_to_real]
  ring

theorem column_inner (q : ℕ) (hq : q ≤ Fintype.card V)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q < 1)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l) :
    ⟪column q i j, column q k l⟫ =
      SliceMoments.average Finset.univ q (fun S =>
        SliceMoments.centeredEqual Finset.univ q i j S *
        SliceMoments.centeredEqual Finset.univ q k l S) /
      (2 * SliceMoments.equalMean (Finset.univ : Finset V) q *
        (1 - SliceMoments.equalMean (Finset.univ : Finset V) q)) := by
  rw [column_inner_unsimplified q hq i j k l hij hkl,
    denominator_sq q hp.le hp1.le]
  have hc : (Nat.choose (Fintype.card V) q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  have hpc : 1 - SliceMoments.equalMean (Finset.univ : Finset V) q ≠ 0 := by
    linarith
  field_simp

theorem column_norm_sq (q : ℕ) (hq : q ≤ Fintype.card V)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q < 1)
    (i j : V) (hij : i ≠ j) : ‖column q i j‖ ^ 2 = (1 / 2 : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, column_inner q hq hp hp1 i j i j hij hij]
  simp_rw [← pow_two]
  rw [SliceMoments.average_centeredEqual_sq Finset.univ q
    (by simpa using hq) i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
  have hpc : 1 - SliceMoments.equalMean (Finset.univ : Finset V) q ≠ 0 := by
    linarith
  field_simp

end Problem315.SliceNormalized

end

end OAI
