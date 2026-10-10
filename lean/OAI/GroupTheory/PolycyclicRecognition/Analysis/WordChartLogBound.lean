import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartLeftShift

namespace OAI

/-! # A polynomial Cartan logarithm from the actual chart displacement -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

variable {L E G I : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]

/-- The shift of zero is the negative logarithm of the translating element,
expressed in the target basis. -/
theorem wordChartLeftShift_zero_log
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    {n : ℕ} (source target : Basis (Fin n) ℝ L) (k : G) :
    ∃ h : L, Exp (e h) = k ∧
      ‖target.equivFun h‖ = ‖wordChartLeftShift e chart source target k 0‖ := by
  let z := wordChartLeftShift e chart source target k 0
  have he : Exp (e (target.equivFun.symm z)) = k⁻¹ := by
    have hp := wordChartLeftShift_point e chart source target k 0
    simpa only [exponentialCoordinates_apply, hchart, map_zero, hExp.map_zero, mul_one] using hp
  refine ⟨-(target.equivFun.symm z), ?_, ?_⟩
  · rw [map_neg, hExp.map_neg, he, inv_inv]
  · simp only [map_neg, LinearEquiv.apply_symm_apply, norm_neg, z]

/-- A bounded point in the word-length rescaled chart has a polynomially
bounded logarithm in any fixed reference basis. -/
theorem exists_wordChartLeftShift_log_bound
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    [Fintype I] [DecidableEq I] (X : I → L) (d : ℕ)
    (β : WordBasisSelections X (boundedBracketWords d))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      let br := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) β)
        (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
      ∀ source : Basis (Fin (finrank ℝ L)) ℝ L,
      ∀ k : G, ∀ R : ℝ, ‖wordChartLeftShift e chart source br k 0‖ ≤ R →
        ∃ h : L, Exp (e h) = k ∧ ‖b₀.equivFun h‖ ≤ C * R * (1 + r) ^ p := by
  classical
  let b := WordBasisSelections.basis X (boundedBracketWords d) β
  let cost := fun j => bracketWordLength (β.val j : FreeMagma I)
  let p := Finset.univ.sup cost
  let C := ∑ j, ‖b₀.equivFun (b j)‖
  have hp j : cost j ≤ p := Finset.le_sup (f := cost) (Finset.mem_univ j)
  refine ⟨C, p, Finset.sum_nonneg (fun j _ => norm_nonneg _), ?_⟩
  intro r hr
  dsimp only
  let br := exponentialRescaleBasis b
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
  intro source k R hR
  obtain ⟨h, he, hh⟩ := wordChartLeftShift_zero_log e Exp hExp chart hchart source br k
  refine ⟨h, he, ?_⟩
  have hb : br = exponentialRescaleBasis b (fun j => (cost j : ℝ)) (Real.log r) := by
    simp only [br, cost, bracketWordExponent_one]
  have hpoly := norm_polynomial_chart_log_le b b₀ cost p hp hr (br.equivFun h)
  rw [← hb, br.equivFun.symm_apply_apply] at hpoly
  exact hpoly.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hh.trans_le hR) (Finset.sum_nonneg (fun j _ => norm_nonneg _)))
    (pow_nonneg (by linarith) _))

end PolycyclicRecognition

end

end OAI
