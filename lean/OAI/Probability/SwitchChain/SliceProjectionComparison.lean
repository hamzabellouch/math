import OAI.Probability.SwitchChain.SliceOperatorComparison
import OAI.Probability.SwitchChain.SliceFrameProjection

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized
open SliceSynthesis

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem raw_eq_zero_of_boundary (q : ℕ) (hq : q ≤ Fintype.card V)
    (hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2) (i j : V) :
    raw q i j = 0 := by
  by_cases hij : i = j
  · subst j; exact raw_diag q i
  · ext S
    change (if i = j then 0 else SliceMoments.centeredEqual Finset.univ q i j S.val) = 0
    rw [ite_eq_right hij]
    exact SliceMoments.centeredEqual_eq_zero_of_boundary Finset.univ q
      (by simpa using hq) i j (Finset.mem_univ i) (Finset.mem_univ j) hij
      (by simpa using hb) S.val S.property

 theorem denominator_pos (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V) : 0 < denominator V q := by
  apply Real.sqrt_pos.2
  have hc : (0 : ℝ) < Nat.choose (Fintype.card V) q := by
    exact_mod_cast Nat.choose_pos hqN.le
  have hp := SliceImageNorm.equalMean_pos hN q
  have hp1 := SliceImageNorm.equalMean_lt_one (by omega : 2 ≤ Fintype.card V) q hq0 hqN
  exact mul_pos (mul_pos (mul_pos (by norm_num) hc) hp) (sub_pos.mpr hp1)

 theorem column_span_eq_raw_span (q : ℕ) (hq : q ≤ Fintype.card V) (i j : V) :
    (ℝ ∙ column q i j) = (ℝ ∙ raw q i j) := by
  by_cases hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2
  · rw [column_eq_zero_of_boundary q hq hb, raw_eq_zero_of_boundary q hq hb]
  · unfold column
    apply Submodule.span_singleton_smul_eq
    exact isUnit_iff_ne_zero.mpr (inv_ne_zero (denominator_pos q (by omega)
      (by omega) (by omega)).ne')

 theorem column_zero_or_norm_sq (q : ℕ) (hq : q ≤ Fintype.card V) (i j : V) :
    column q i j = 0 ∨ ‖column q i j‖ ^ 2 = (1/2 : ℝ) := by
  by_cases hij : i = j
  · subst j; exact Or.inl (column_diag q i)
  by_cases hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2
  · exact Or.inl (column_eq_zero_of_boundary q hq hb i j)
  · right
    exact column_norm_sq q hq (SliceImageNorm.equalMean_pos (by omega) q)
      (SliceImageNorm.equalMean_lt_one (by omega) q (by omega) (by omega)) i j hij

 theorem raw_projection_frame_energy (q : ℕ) (hq : q ≤ Fintype.card V)
    (f : Space V q) :
    ⟪f, synthesis (column q) (LinearMap.adjoint (synthesis (column q)) f)⟫ =
      (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ raw q i j).starProjection f‖ ^ 2 := by
  rw [synthesis_eq_frame]
  have h := FrameSynthesis.frame_energy_of_common_norm_sq
    (fun p : V × V => column q p.1 p.2) (1/2)
    (fun p => column_zero_or_norm_sq q hq p.1 p.2) f
  simpa only [Fintype.sum_prod_type, column_span_eq_raw_span q hq] using h

 theorem projection_comparison (q : ℕ) (hq : q ≤ Fintype.card V) (f : Space V q) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ raw q i j).starProjection f‖ ^ 2 ≤
      ⟪f, SliceEuclideanGenerator.generator q f⟫ := by
  rw [← raw_projection_frame_energy q hq f]
  exact operator_comparison q hq f

 theorem projection_energy_le_swap_energy (q : ℕ) (hq : q ≤ Fintype.card V)
    (f : Space V q) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ raw q i j).starProjection f‖ ^ 2 ≤
      (1/8 : ℝ) * ∑ i, ∑ j,
        ‖f - SliceEuclideanGenerator.moveOperator q i j f‖ ^ 2 := by
  rw [← SliceEuclideanGenerator.generator_energy]
  exact projection_comparison q hq f

end Problem315.SliceNormalized

end

end OAI
