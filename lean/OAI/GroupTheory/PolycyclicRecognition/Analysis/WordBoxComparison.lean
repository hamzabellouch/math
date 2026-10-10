import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledGeneratorBounds
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceSectionTileVolume

namespace OAI

/-! # Comparing boxes with varying maximizing word bases

Only the target basis needs to maximize its costs. A small change in the
costs of the finite word list introduces exactly its exponential error.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
/-- A uniform basis-change bound for all cost functions. -/
theorem exists_word_box_comparison_constant
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (cost newCost : S → ℝ)
      (β γ : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val →
      ∀ {r ε : ℝ}, 0 ≤ r → (∀ w, newCost w ≤ cost w + ε) → ∀ v : L,
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => cost (β.val j)) r).equivFun v‖ ≤
        D * Real.exp (ε * r) *
          ‖(exponentialRescaleBasis (WordBasisSelections.basis X S γ)
            (fun j => newCost (γ.val j)) r).equivFun v‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_normalized_coordinate_bound (wordListCoordinates X S b₀)
  refine ⟨(finrank ℝ L : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro cost newCost β γ hβ r ε hr hcost v
  let b := exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => cost (β.val j)) r
  let b' := exponentialRescaleBasis (WordBasisSelections.basis X S γ)
    (fun j => newCost (γ.val j)) r
  have hword (w : S) : ‖b.equivFun (Real.exp (r * cost w) • evalBracketWord X w)‖ ≤ C := by
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro j
    change |b.repr (Real.exp (r * cost w) • evalBracketWord X w) j| ≤ C
    rw [repr_exponentialRescaleBasis_smul]
    have hh := hb cost β.val hβ w j r hr
    rw [columnCoordinates_eq_wordBasis_repr X S b₀ β w] at hh
    exact hh
  have hnew (w : S) :
      ‖b.equivFun (Real.exp (r * newCost w) • evalBracketWord X w)‖ ≤
        Real.exp (ε * r) * C := by
    have he : Real.exp (r * newCost w) • evalBracketWord X w =
        Real.exp (r * (newCost w - cost w)) •
          (Real.exp (r * cost w) • evalBracketWord X w) := by
      rw [smul_smul, ← Real.exp_add]
      congr 2
      ring
    rw [he, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul _ (hword w) (norm_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hcost w) hr]
  have hbase (j : Fin (finrank ℝ L)) : ‖b.equivFun (b' j)‖ ≤ Real.exp (ε * r) * C := by
    have he : b' j = Real.exp (r * newCost (γ.val j)) • evalBracketWord X (γ.val j) := by
      have hj := WordBasisSelections.eval_words X S γ j
      change evalBracketWord X (γ.val j) = _ at hj
      rw [hj]
      simp only [b', exponentialRescaleBasis, Basis.unitsSMul_apply,
        Units.smul_def, Units.val_mk0]
    rw [he]
    exact hnew (γ.val j)
  change ‖b.equivFun v‖ ≤ _ * ‖b'.equivFun v‖
  conv_lhs => rw [← b'.sum_repr v]
  rw [map_sum]
  calc
    _ ≤ ∑ j, ‖b.equivFun (b'.repr v j • b' j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (finrank ℝ L), ‖b'.equivFun v‖ * (Real.exp (ε * r) * C) := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (norm_le_pi_norm (b'.equivFun v) j) (hbase j)
        (norm_nonneg _) (norm_nonneg _)
    _ = ((finrank ℝ L : ℝ) * C) * Real.exp (ε * r) * ‖b'.equivFun v‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

omit [FiniteDimensional ℝ L] in
/-- Vanishing errors in the costs and subexponential box radii admit one
subexponential envelope in a single fixed maximizing basis. -/
theorem exists_sequence_word_box_envelope
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (cost : S → ℝ) (β : WordBasisSelections X S)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val)
    (scale ε R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hε : Tendsto ε atTop (𝓝 0))
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ V : ℕ → ℝ, (∀ n, 0 ≤ V n) ∧ HasSubexponentialUpperBoundSeq scale V ∧
      ∀ n (newCost : S → ℝ) (γ : WordBasisSelections X S),
        (∀ w, newCost w ≤ cost w + ε n) → ∀ v : L,
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X S γ)
          (fun j => newCost (γ.val j)) (scale n)).equivFun v‖ ≤ R n →
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => cost (β.val j)) (scale n)).equivFun v‖ ≤ V n := by
  obtain ⟨D, hD, hcompare⟩ := exists_word_box_comparison_constant X S b₀
  let V := fun n => D * Real.exp (ε n * scale n) * R n
  have hV : HasSubexponentialUpperBoundSeq scale V :=
    ((sequence_subexponential_upper_const hscale D).mul
      (sequence_subexponential_exp_error hscale hε) (Eventually.of_forall (fun _ => hD))).mul
      hR (Eventually.of_forall (fun n => mul_nonneg hD (Real.exp_pos _).le))
  refine ⟨V, fun n => mul_nonneg (mul_nonneg hD (Real.exp_pos _).le) (hR0 n), hV, ?_⟩
  intro n newCost γ hc v hv
  exact (hcompare cost newCost β γ hβ (hscale0 n) hc v).trans
    (mul_le_mul_of_nonneg_left hv (mul_nonneg hD (Real.exp_pos _).le))

end PolycyclicRecognition

end

end OAI
