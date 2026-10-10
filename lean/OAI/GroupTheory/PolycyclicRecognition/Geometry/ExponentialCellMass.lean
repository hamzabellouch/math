import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialGoodCells

namespace OAI

/-! # Positive finite mass of the actual translated exponential cells -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

/-- Every positive finite coordinate cell gives a positive finite Haar cell,
with no restriction on the scale or the deterministic right suffix. -/
theorem translated_exponential_cell_mass
    {L E N I : Type*} [LieRing L] [LieAlgebra ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace N] [ChartedSpace E N] [Group N]
    [LieGroup (𝓘(ℝ, E)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
    [MeasurableSpace N] [BorelSpace N]
    (haar : NilpotentExponentialHaarInput E N)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N) (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) N ≃ₜ N) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (r : ℝ) (k : N)
    (C : Set (Fin (finrank ℝ L) → ℝ)) (hC0 : volume C ≠ 0) (hCfin : volume C ≠ ∞) :
    let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
    let sample := fun y => ((Exp ∘ e) ∘ (exponentialRescaleBasis
      (WordBasisSelections.basis X words β) (fun j => cost (β.val j)) r).equivFun.symm) y * k
    0 < (μ (sample '' C)).toReal ∧ μ (sample '' C) ≠ ∞ := by
  let : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haar e hnil Exp hExp b₀
  let g := (Exp ∘ e) ∘ (exponentialRescaleBasis
    (WordBasisSelections.basis X words β) (fun j => cost (β.val j)) r).equivFun.symm
  have hm : μ ((fun y => g y * k) '' C) =
      ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| *
        ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) * volume C := by
    rw [show (fun y => g y * k) '' C = (fun y : N => y * k) '' (g '' C) from
      image_comp (fun y : N => y * k) g C, measure_image_mul_right μ]
    exact exponential_rescaled_subset_measure e Exp chart hchart X words b₀ β cost r C
  have hd := ENNReal.ofReal_pos.mpr
    (abs_pos.mpr (wordBasis_det_ne_zero X words b₀ β))
  have he := ENNReal.ofReal_pos.mpr (Real.exp_pos (r * columnBasisWeight cost β.val))
  have hzero : μ ((fun y => g y * k) '' C) ≠ 0 := by
    rw [hm]
    exact mul_ne_zero (mul_ne_zero hd.ne' he.ne') hC0
  have hfinite : μ ((fun y => g y * k) '' C) ≠ ∞ := by
    rw [hm]
    exact (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ENNReal.ofReal_lt_top) hCfin.lt_top).ne
  exact ⟨ENNReal.toReal_pos hzero hfinite, hfinite⟩

/-- The finite-dimensional closed coordinate cube has positive finite mass. -/
theorem coordinate_cube_mass {n : ℕ} {R : ℝ} (hR : 0 < R) :
    volume (Icc (fun _ : Fin n => -R) (fun _ => R)) ≠ 0 ∧
      volume (Icc (fun _ : Fin n => -R) (fun _ => R)) ≠ ∞ := by
  rw [Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith : 0 ≤ 2 * R)]
  exact ⟨(ENNReal.ofReal_pos.mpr (pow_pos (by linarith) n)).ne', ENNReal.ofReal_ne_top⟩

end PolycyclicRecognition

end

end OAI
