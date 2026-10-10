import OAI.Analysis.KadisonSimilarity.Derivation.CyclicDecomposition
import Mathlib.Topology.Bases

namespace OAI

/-! An orthogonal cyclic decomposition is countable on a separable Hilbert
space, as required for the normal standard-representation reduction. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  {N : StarSubalgebra ℂ (H →L[ℂ] H)}

namespace CyclicDecompositionData

/-- Normalized nonzero cyclic generators have disjoint open half-balls,
so separability makes the family countable. -/
theorem generators_countable (D : CyclicDecompositionData N) : Countable D.generators := by
  let v : D.generators → H := fun i => (‖(i : H)‖⁻¹ : ℂ) • (i : H)
  have hn (i : D.generators) : ‖v i‖ = 1 := by
    have hi := norm_ne_zero_iff.mpr (D.nonzero i i.property)
    simp only [v, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hi]
  have ho (i j : D.generators) (hij : i ≠ j) : inner ℂ (v i) (v j) = 0 := by
    have h := D.orthogonal i.property j.property (fun he => hij (Subtype.ext he))
      i (self_mem_orbitClosure N i) j (self_mem_orbitClosure N j)
    simp only [v, inner_smul_left, inner_smul_right, h, mul_zero]
  have hd (i j : D.generators) (hij : i ≠ j) : 1 ≤ dist (v i) (v j) := by
    have h := norm_sub_sq (𝕜 := ℂ) (v i) (v j)
    rw [hn i, hn j, ho i j hij] at h
    norm_num at h
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v j)]
  exact Pairwise.countable_of_isOpen_disjoint
    (s := fun i => Metric.ball (v i) (1 / 2))
    (fun i j hij => Metric.ball_disjoint_ball (by linarith [hd i j hij]))
    (fun _ => Metric.isOpen_ball) (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

end CyclicDecompositionData
end KadisonSimilarity

end

end OAI
