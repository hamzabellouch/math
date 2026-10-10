import OAI.Probability.SwitchChain.SliceSynthesis
import OAI.Probability.SwitchChain.FrameSynthesis

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis

variable {V E : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

include sectionDecidableEqV in
theorem synthesis_eq_frame (z : V → V → E) :
    synthesis z = FrameSynthesis.synthesis (fun p : V × V => z p.1 p.2) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  apply LinearMap.ext
  intro c
  simp [synthesis, FrameSynthesis.synthesis, Fintype.sum_prod_type]

variable [FiniteDimensional ℝ E]

theorem half_projection_frame_apply (z : V → V → E)
    (hzdiag : ∀ i, z i i = 0)
    (hznorm : ∀ i j, i ≠ j → ‖z i j‖ ^ 2 = (1 / 2 : ℝ)) (x : E) :
    synthesis z ((synthesis z).adjoint x) =
      (1 / 2 : ℝ) • ∑ i, ∑ j, (ℝ ∙ z i j).starProjection x := by
  rw [synthesis_eq_frame]
  have hz (p : V × V) : z p.1 p.2 = 0 ∨ ‖z p.1 p.2‖ ^ 2 = (1 / 2 : ℝ) := by
    by_cases h : p.1 = p.2
    · exact Or.inl (by rw [h, hzdiag])
    · exact Or.inr (hznorm p.1 p.2 h)
  simpa only [Fintype.sum_prod_type] using
    FrameSynthesis.frame_apply_of_common_norm_sq
      (fun p : V × V => z p.1 p.2) (1 / 2) hz x

theorem half_projection_frame_energy (z : V → V → E)
    (hzdiag : ∀ i, z i i = 0)
    (hznorm : ∀ i j, i ≠ j → ‖z i j‖ ^ 2 = (1 / 2 : ℝ)) (x : E) :
    ⟪x, synthesis z ((synthesis z).adjoint x)⟫ =
      (1 / 2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ z i j).starProjection x‖ ^ 2 := by
  rw [synthesis_eq_frame]
  have hz (p : V × V) : z p.1 p.2 = 0 ∨ ‖z p.1 p.2‖ ^ 2 = (1 / 2 : ℝ) := by
    by_cases h : p.1 = p.2
    · exact Or.inl (by rw [h, hzdiag])
    · exact Or.inr (hznorm p.1 p.2 h)
  simpa only [Fintype.sum_prod_type] using
    FrameSynthesis.frame_energy_of_common_norm_sq
      (fun p : V × V => z p.1 p.2) (1 / 2) hz x

end Problem315.SliceSynthesis

end

end OAI
