import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartLeftShift

namespace OAI

/-! # Compact-ball restriction of the actual changed-center chart -/

noncomputable section
namespace PolycyclicRecognition

open Module Metric
open scoped Manifold

variable {L E G W I : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]

/-- The genuine group-defined shift, with its range restricted by the
proved chart bound. -/
def wordBallLeftShift {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (source target : Basis (Fin n) ℝ L) (k : G) (R S : ℝ)
    (hbound : ∀ z : Fin n → ℝ, ‖z‖ ≤ R →
      ‖wordChartLeftShift e chart source target k z‖ ≤ S) :
    C(closedBall (0 : Fin n → ℝ) R, closedBall (0 : Fin n → ℝ) S) := by
  let f : closedBall (0 : Fin n → ℝ) R → closedBall (0 : Fin n → ℝ) S :=
    fun z => ⟨wordChartLeftShift e chart source target k z, by
      rw [mem_closedBall, dist_zero_right]
      exact hbound z (by simpa only [mem_closedBall, dist_zero_right] using z.property)⟩
  exact ⟨f, ((wordChartLeftShift e chart source target k).continuous.comp
    continuous_subtype_val).subtype_mk _⟩

variable [Fintype I] [DecidableEq I] [AddCommGroup W] [Module ℝ W]

/-- Normalizing the exact two-scale height identity produces the affine
translation required by the finite-label comparison. -/
theorem wordChartLeftShift_normalized_height
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (π : G →* Multiplicative W) (height : L →ₗ[ℝ] W)
    (hheight : ∀ v, (π (chart (e v))).toAdd = height v)
    (hkill : ∀ x y : L, height ⁅x, y⁆ = 0)
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (k : G)
    (z : Fin (finrank ℝ L) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let br := exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
    let bs := exponentialRescaleBasis b
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log s)
    (s / r) • height (b.equivFun.symm (wordChartLeftShift e chart br bs k z)) =
      height (b.equivFun.symm z) - r⁻¹ • (π k).toAdd := by
  have hh := wordChartLeftShift_height e chart π height hheight hkill X S β hr hs k z
  simp only [← bracketWordExponent_one] at hh
  have he := congrArg (fun w : W => r⁻¹ • w) hh
  simp only [smul_sub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at he
  simpa only [div_eq_mul_inv, mul_comm] using he

end PolycyclicRecognition

end

end OAI
