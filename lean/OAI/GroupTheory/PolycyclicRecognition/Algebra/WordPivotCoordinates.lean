import OAI.GroupTheory.PolycyclicRecognition.Geometry.GradedHeight
import Mathlib.Topology.Compactness.LocallyCompact

namespace OAI

/-! # Compact coordinates for the actual rescaled contact pivot -/

noncomputable section
namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology

/-- The pivot coordinate moves with the weighted chart. It stays in one
compact part of the height domain and has exactly the original height. -/
theorem exists_compact_word_pivot_coordinates
    {L W I : Type*} [LieRing L] [LieAlgebra ℝ L]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [Fintype I] [DecidableEq I]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hs0 : ∀ n, 0 < scale n)
    (pivot : L) (V : Set W) (hV : IsOpen V) (hp : h pivot ∈ V) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    ∃ Q : Set (Fin (finrank ℝ L) → ℝ), IsCompact Q ∧
      Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧
      (∀ᶠ n in atTop, (br n).equivFun (scale n • pivot) ∈ Q) ∧
      ∀ n, h (b.equivFun.symm ((br n).equivFun (scale n • pivot))) = h pivot := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
  let q : (Fin (finrank ℝ L) → ℝ) →ₗ[ℝ] W := h.comp b.equivFun.symm.toLinearMap
  let U := {z | q z ∈ V}
  have hU : IsOpen U := hV.preimage q.continuous_of_finiteDimensional
  have hcost (j) (_ : b.repr pivot j ≠ 0) : (1 : ℝ) ≤ cost j := by
    have hlen (w : FreeMagma I) : 1 ≤ bracketWordLength w := by
      induction w using FreeMagma.rec with
      | of i => simp [bracketWordLength]
      | mul u w hu hw => simp only [bracketWordLength]; omega
    dsimp only [cost]
    rw [bracketWordExponent_one]
    exact_mod_cast hlen (β.val j)
  have hlim : Tendsto (fun n => (br n).equivFun (scale n • pivot)) atTop
      (𝓝 (gradedGenerator b cost 1 pivot)) := by
    have hraw := (rescaled_generator_tendsto b cost 1 pivot hcost).comp
      (Real.tendsto_log_atTop.comp hscale)
    simpa only [Function.comp_def, mul_one, Real.exp_log (hs0 _)] using hraw
  have hinside : gradedGenerator b cost 1 pivot ∈ U := by
    change h (b.equivFun.symm (gradedGenerator b cost 1 pivot)) ∈ V
    rw [gradedGenerator_word_height X S β h hh]
    exact hp
  obtain ⟨Q, hQ, hQi, hQU⟩ := exists_compact_subset hU hinside
  refine ⟨Q, hQ, hQU, hlim.eventually (mem_interior_iff_mem_nhds.mp hQi), ?_⟩
  intro n
  exact word_length_chart_pivot_height X S β h hh (hs0 n) pivot

end PolycyclicRecognition

end

end OAI
