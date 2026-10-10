import OAI.GroupTheory.PolycyclicRecognition.Geometry.MovingBaseFlow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.GradedHeight

namespace OAI

/-! # Compact coordinates for the actual pivot-to-support legs -/

noncomputable section
namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology

/-- In a unit-cost word chart, the actual exponential leg from the pivot
 to each of finitely many support heights stays in one compact part of the
 open convex height domain. The coordinate identity is retained. -/
theorem exists_compact_rescaled_pivot_legs
    {L G W I J : Type*} [LieRing L] [LieAlgebra ℝ L] [Group G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [Fintype I] [DecidableEq I] [Fintype J]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (Exp : L → G) (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = h x)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (hweight : ∀ i j k,
      (WordBasisSelections.basis X S β).repr
        ⁅(WordBasisSelections.basis X S β) i, (WordBasisSelections.basis X S β) j⁆ k ≠ 0 →
      bracketWordExponent (fun _ : I => 1) (β.val i) +
        bracketWordExponent (fun _ : I => 1) (β.val j) ≤
          bracketWordExponent (fun _ : I => 1) (β.val k))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (pivot : L) (support : J → L) (V : Set W)
    (hV : IsOpen V) (hconv : Convex ℝ V)
    (hpivot : h pivot ∈ V) (hsupport : ∀ j, h (support j) ∈ V) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    ∃ Q : Set (Fin (finrank ℝ L) → ℝ), IsCompact Q ∧
      Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧
      ∀ᶠ n in atTop, ∀ j t, t ∈ Icc (0 : ℝ) 1 →
        ∃ z ∈ Q, Exp ((exponentialRescaleBasis b cost (scale n)).equivFun.symm z) =
          Exp (Real.exp (scale n) • pivot) *
            Exp ((Real.exp (scale n) * t) • (support j - pivot)) := by
  classical
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let p := h.comp b.equivFun.symm.toLinearMap
  let U := {z | p z ∈ V}
  have hU : IsOpen U := hV.preimage p.continuous_of_finiteDimensional
  have hlower (v : L) (j) (_ : b.repr v j ≠ 0) : (1 : ℝ) ≤ cost j := by
    have hlen (w : FreeMagma I) : 1 ≤ bracketWordLength w := by
      induction w using FreeMagma.rec with
      | of i => simp [bracketWordLength]
      | mul u w hu hw => simp only [bracketWordLength]; omega
    dsimp [cost]
    rw [bracketWordExponent_one]
    exact_mod_cast hlen (β.val j)
  have hbase := (rescaled_generator_tendsto b cost 1 pivot (hlower pivot)).comp hscale
  have hbase' : Tendsto (fun n => (exponentialRescaleBasis b cost (scale n)).equivFun
      (Real.exp (scale n) • pivot)) atTop (𝓝 (gradedGenerator b cost 1 pivot)) := by
    simpa only [Function.comp_def, mul_one] using hbase
  have hleg (j : J) : ∃ Q : Set (Fin (finrank ℝ L) → ℝ), IsCompact Q ∧ Q ⊆ U ∧
      ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
        dynkinProduct a (basisBracket (exponentialRescaleBasis b cost (scale n)))
          ((exponentialRescaleBasis b cost (scale n)).equivFun (Real.exp (scale n) • pivot))
          (t • (exponentialRescaleBasis b cost (scale n)).equivFun
            (Real.exp (scale n) • (support j - pivot))) ∈ Q := by
    have hv := (rescaled_generator_tendsto b cost 1 (support j - pivot)
      (hlower (support j - pivot))).comp hscale
    apply exists_compact_eventual_based_dynkin_leg a _ _ _ _ _ _
      ((basisBracket_rescale_tendsto b cost hweight).comp hscale) hbase'
      (by simpa only [Function.comp_def, mul_one] using hv) U hU
    intro t ht
    change p _ ∈ V
    have he : p (dynkinProduct a (gradedCoordinateBracket b cost)
        (gradedGenerator b cost 1 pivot) (t • gradedGenerator b cost 1 (support j - pivot))) =
        (1 - t) • h pivot + t • h (support j) := by
      rw [show p _ = p (gradedGenerator b cost 1 pivot) +
          p (t • gradedGenerator b cost 1 (support j - pivot)) from
        gradedWordChartProduct_height X S β h hh Exp π hπ a hm hweight _ _]
      rw [map_smul]
      change h (b.equivFun.symm (gradedGenerator b cost 1 pivot)) +
        t • h (b.equivFun.symm (gradedGenerator b cost 1 (support j - pivot))) = _
      rw [gradedGenerator_word_height X S β h hh,
        gradedGenerator_word_height X S β h hh, map_sub, smul_sub, sub_smul, one_smul]
      abel
    rw [he]
    exact hconv hpivot (hsupport j) (sub_nonneg.mpr ht.2) ht.1 (by ring)
  choose Q hQ hQU hevent using hleg
  refine ⟨⋃ j, Q j, isCompact_iUnion hQ, iUnion_subset hQU, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hevent] with n hn
  intro j t ht
  let br := exponentialRescaleBasis b cost (scale n)
  let z := dynkinProduct a (basisBracket br)
    (br.equivFun (Real.exp (scale n) • pivot))
    (t • br.equivFun (Real.exp (scale n) • (support j - pivot)))
  refine ⟨z, mem_iUnion.mpr ⟨j, hn j t ht⟩, ?_⟩
  dsimp only [z]
  rw [exp_basis_dynkinProduct br Exp a hm, LinearEquiv.symm_apply_apply,
    ← map_smul, LinearEquiv.symm_apply_apply, smul_smul, mul_comm t]

end PolycyclicRecognition

end

end OAI
