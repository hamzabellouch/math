import OAI.Combinatorics.CliqueFree.SplittingLoss

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

noncomputable def splittingConstant (C : ℝ) : ℝ :=
  6 * (smoothingConstant C + entropyConstant C + 1)

lemma splitting_error_le {C x : ℝ} (hC : 1 ≤ C) (hx : 32 ≤ x) :
    6 * (smoothingConstant C * Real.sqrt (Real.log x / x)) +
    6 * ((entropyConstant C + 1) * Real.log x / (Real.sqrt x + Real.log x)) ≤
    splittingConstant C * (Real.log x / Real.sqrt x) := by
  have hx0 : 0 < x := by linarith
  have hl := (Numerical.log_bounds hx).1
  have hl0 : 0 ≤ Real.log x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hA : 0 ≤ entropyConstant C + 1 := by
    unfold entropyConstant exceptionalConstant
    positivity
  have hB : 0 ≤ smoothingConstant C := by unfold smoothingConstant; positivity
  have hslog : Real.sqrt (Real.log x) ≤ Real.log x := by
    have hh := Real.sq_sqrt hl0
    have hn := Real.sqrt_nonneg (Real.log x)
    nlinarith
  have h1 : Real.sqrt (Real.log x / x) ≤ Real.log x / Real.sqrt x := by
    rw [Real.sqrt_div hl0]
    exact div_le_div_of_nonneg_right hslog hs.le
  have h2 : (entropyConstant C + 1) * Real.log x / (Real.sqrt x + Real.log x) ≤
      (entropyConstant C + 1) * (Real.log x / Real.sqrt x) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_left (mul_nonneg hA hl0) hs (by linarith)
  unfold splittingConstant
  nlinarith [mul_le_mul_of_nonneg_left h1 hB]

/-- Weighted vertex splitting with explicit constants. -/
lemma weighted_splitting {G : SimpleGraph V} [Nonempty (EdgeState G)] {w : V → ℝ}
    (hw : ∀ u, 0 < w u) {C x : ℝ} (hC : 1 ≤ C) (hCross : CrossBound G w C)
    (hx : 32 ≤ x) (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) :
    ∃ H : SimpleGraph (EdgeState G), EdgeProjection H G EdgeState.src ∧
      (∀ z, neighborMass H (w ∘ EdgeState.src) z ≤ Real.exp (Real.sqrt x)) ∧
      (1 - splittingConstant C * (Real.log x / Real.sqrt x)) * triangleMass G w ≤
        triangleMass H (w ∘ EdgeState.src) := by
  open FiniteEntropy FiniteKernel LocalWalk in
  have hx0 : 0 < x := by linarith
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx0).trans_le (hc u v huv)
  obtain ⟨j,_,hH,hD⟩ := LocalWalk.exists_smooth_index hw hC hCross hx hc hL
  let K := FiniteKernel.smoothed (LocalWalk.transition G w) j
  have hP := LocalWalk.transition_stochastic hw hc0
  have hK := FiniteKernel.stochastic_smoothed hP j
  have hrev := FiniteKernel.reversible_smoothed (LocalWalk.transition_reversible hw hc0) j
  have htail := FiniteKernel.reversed_entropy_tail (LocalWalk.law_isProb hw hc0)
    (fun e : EdgeState G ↦ hw e.dst) hK hrev hx0 (LocalWalk.smoothed_density hw hx0 hc j)
    (a := Real.sqrt x)
  have hden : 0 < Real.sqrt x + Real.log x := by
    have hs := Real.sqrt_pos.2 hx0
    linarith [(Numerical.log_bounds hx).1]
  have hδ : (∑ e, LocalWalk.law G w e * ∑ y,
      if K y e < w e.dst * Real.exp (-Real.sqrt x) then K e y else 0) ≤
        (entropyConstant C + 1) * Real.log x / (Real.sqrt x + Real.log x) := by
    apply (le_div_iff₀ hden).2
    dsimp [K]
    change FiniteKernel.avgEntropy (LocalWalk.law G w) (fun e ↦ w e.dst)
      (FiniteKernel.smoothed (LocalWalk.transition G w) j) ≤ entropyConstant C * Real.log x at hH
    nlinarith only [htail,hH]
  obtain ⟨H,hproj,hneigh,htri⟩ := Splitting.exists_graph hw hc0 K hK
    (LocalWalk.smoothed_fixed_src j) hD hδ
  refine ⟨H,hproj,hneigh,?_⟩
  have hn := triangleMass_nonneg G (fun u ↦ (hw u).le)
  have he := splitting_error_le hC hx
  nlinarith [mul_le_mul_of_nonneg_right he hn]

end CliqueFreeIndependence.WeightedGraph

end

end OAI
