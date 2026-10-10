import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceBondLists

namespace OAI

/-! Literal source rounding and zero deletion feed the complete three-stage
spin comparison. Only the source's upper coefficient and gap bounds are
needed; a nonzero lower coefficient bound is proved by rounding. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum
open Matrix MediatorIteration MediatorListProgram SourceBondLists
open scoped BigOperators

def rounded (d : SquareLatticeHeisenberg) (M : ℕ) : List Bond :=
  List.ofFn (fun e => ((d.left e).val, (d.right e).val,
    SourceCoefficientRounding.coefficient M (d.coefficient e)))

def retained (d : SquareLatticeHeisenberg) (M : ℕ) : List Bond :=
  (rounded d M).filter SourceZeroFilter.keep

theorem rounded_bounded (d : SquareLatticeHeisenberg) (M : ℕ) : bounded d.vertices (rounded d M) := by
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact ⟨(d.left i).isLt, (d.right i).isLt⟩

theorem retained_bounded (d : SquareLatticeHeisenberg) (M : ℕ) : bounded d.vertices (retained d M) :=
  filter_bounded d.vertices (rounded d M) (rounded_bounded d M)

def family (d : SquareLatticeHeisenberg) (M : ℕ) : Bonds d.vertices (retained d M).length :=
  bonds d.vertices (retained d M) (retained_bounded d M)

theorem family_noLoops (d : SquareLatticeHeisenberg) (M : ℕ) : (family d M).NoLoops := by
  apply bonds_noLoops
  intro e he hloop
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_filter.mp he).1
  exact d.edge_ne i (Fin.ext hloop)

theorem rounded_matrix (d : SquareLatticeHeisenberg) (M : ℕ) :
    matrix d.vertices (rounded d M) =
      (d.withCoefficients (fun e => SourceCoefficientRounding.coefficient M (d.coefficient e))).bonds.matrix := by
  unfold matrix rounded
  rw [List.map_ofFn, List.sum_ofFn]
  unfold Bonds.matrix SquareLatticeHeisenberg.bonds sourceGraphMatrix
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  rw [bondMatrix, dite_eq_left ⟨(d.left i).isLt, (d.right i).isLt⟩]
  simp only [SquareLatticeHeisenberg.withCoefficients, Complex.ofReal_ratCast]
  rfl

theorem family_matrix (d : SquareLatticeHeisenberg) (M : ℕ) :
    (family d M).matrix =
      (d.withCoefficients (fun e => SourceCoefficientRounding.coefficient M (d.coefficient e))).bonds.matrix := by
  exact (matrix_bonds d.vertices (retained d M) (retained_bounded d M)).symm.trans
    ((filter_matrix d.vertices (rounded d M)).trans (rounded_matrix d M))

theorem family_bottom_error (d : SquareLatticeHeisenberg) {M : ℕ} (hM : 0 < M) :
    |sourceMatrixBottom d.vertices (family d M).matrix - realSourceGroundEnergy d| ≤
      3 * d.edges / (2 * (M : ℝ)) := by
  rw [family_matrix]
  change |sourceMatrixBottom
      (d.withCoefficients (fun e => SourceCoefficientRounding.coefficient M (d.coefficient e))).vertices
      (d.withCoefficients (fun e => SourceCoefficientRounding.coefficient M (d.coefficient e))).bonds.matrix -
      realSourceGroundEnergy d| ≤ _
  rw [sourceMatrixBottom_eq_realSource]
  have h := realSourceGroundEnergy_rounding d
    (fun e => SourceCoefficientRounding.coefficient M (d.coefficient e))
  have hp : ∀ e, |(d.coefficient e : ℝ) -
      (SourceCoefficientRounding.coefficient M (d.coefficient e) : ℝ)| ≤ 1 / (2 * (M : ℝ)) := by
    intro e
    have hq := Rat.cast_le (K := ℝ).mpr
      (SourceCoefficientRounding.coefficient_error hM (d.coefficient e))
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one,
      Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using hq
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ (Finset.univ : Finset (Fin d.edges))) => hp e)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  exact h.trans ((mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring))

theorem family_bounds (d : SquareLatticeHeisenberg) {M W : ℕ} (hM : 0 < M)
    (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) :
    ∀ e, 1 / ((M + W + 1 : ℕ) : ℝ) ≤ |((family d M).weight e : ℝ)| ∧
      |((family d M).weight e : ℝ)| ≤ (M + W + 1 : ℕ) := by
  intro e
  have he := List.get_mem (retained d M) e
  have hz := SourceZeroFilter.nonzero_mem (rounded d M) _ he
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp (List.mem_filter.mp he).1
  have hw : (family d M).weight e = SourceCoefficientRounding.coefficient M (d.coefficient i) := by
    exact congrArg (fun a : Bond => a.2.2) hi.symm
  have hz' : SourceCoefficientRounding.coefficient M (d.coefficient i) ≠ 0 := by simpa only [← hi] using hz
  have hl : 1 / (M : ℝ) ≤ |(SourceCoefficientRounding.coefficient M (d.coefficient i) : ℝ)| := by
    have hq := Rat.cast_le (K := ℝ).mpr
      (SourceCoefficientRounding.coefficient_nonzero_lower hM (d.coefficient i) hz')
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_abs] using hq
  have hq : |d.coefficient i| ≤ (W : ℚ) := by exact_mod_cast hW i
  have hu : |(SourceCoefficientRounding.coefficient M (d.coefficient i) : ℝ)| ≤ W + 1 := by
    exact_mod_cast SourceCoefficientRounding.coefficient_upper hM (d.coefficient i) hq
  rw [hw]
  constructor
  · exact (one_div_le_one_div_of_le (by exact_mod_cast hM)
      (by norm_cast; omega : (M : ℝ) ≤ (M + W + 1 : ℕ))).trans hl
  · have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    push_cast
    linarith

/-- Full three-stage error after genuine source normalization, with no
lower-weight hypothesis on the original published source. -/
theorem normalized_three_stage_bottom (d : SquareLatticeHeisenberg) {M W G : ℕ}
    (hM : 0 < M) (hG : 0 < G) (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) :
    |sourceMatrixBottom
      (d.vertices + (retained d M).length * 2 + (retained d M).length * 2 * 2 +
        ((retained d M).length * 2 + (retained d M).length * 2 * 2) * 2)
      (finalGraph (family d M) (M + W + 1) G).matrix +
      (MediatorIteration.offset (family d M) (M + W + 1) G : ℝ) - realSourceGroundEnergy d| ≤
        3 / (512 * (G : ℝ)) + 3 * d.edges / (2 * (M : ℝ)) := by
  have hB := family_bounds d hM hW
  have h := three_stage_bottom (family d M) (family_noLoops d M)
    (by omega : 0 < M + W + 1) hG (fun e => (hB e).2) (fun e => (hB e).1)
  have he := family_bottom_error d hM
  have ht := (abs_add_le
    (sourceMatrixBottom _ (finalGraph (family d M) (M + W + 1) G).matrix +
      (MediatorIteration.offset (family d M) (M + W + 1) G : ℝ) -
      sourceMatrixBottom d.vertices (family d M).matrix)
    (sourceMatrixBottom d.vertices (family d M).matrix - realSourceGroundEnergy d)).trans (add_le_add h he)
  convert ht using 1
  congr 1
  ring

end ContinuumCoulomb.SourceNormalizedSpectrum

end

end OAI
