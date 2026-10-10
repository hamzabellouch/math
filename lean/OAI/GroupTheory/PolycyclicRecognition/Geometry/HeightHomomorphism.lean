import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineAction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AmenableCorrection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeanSubgroup

namespace OAI

/-! # The corrected height homomorphism

An amenable group acting with bounded height error and finitely many linear
height parts has a normal finite-index subgroup with a genuine homomorphism
to the height space at bounded distance from the height shifts. In particular
the shifts are uniformly bounded on the kernel. The construction combines
the exact linear action with an invariant-mean correction.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability

variable {H X W : Type*} [Group H] [NormedAddCommGroup W] [NormedSpace ℝ W]

namespace HeightQuasiAction

/-- The affine shifts restricted to the linear kernel are at bounded distance
from an actual height homomorphism. Amenability is expressed by an invariant
mean on all bounded functions on the original group. -/
theorem exists_correctedHeight [FiniteDimensional ℝ W] (Q : HeightQuasiAction H X W) (M : InvariantMean H) :
    ∃ (τ : Q.linearHom.ker →* Multiplicative W) (B : ℝ),
      0 ≤ B ∧ ∀ h, ‖(τ h).toAdd - Q.shift h‖ ≤ B := by
  exact exists_finiteDimensional_correctedHom
    (subgroupInvariantMean M Q.linearHom.ker) (fun h => Q.shift h)
    Q.translationDefect Q.translation_defect_le

/-- On the kernel of any such correction, the original height shifts are bounded.
The kernel is not assumed to be finitely generated. -/
theorem shift_bounded_on_kernel (Q : HeightQuasiAction H X W)
    (τ : Q.linearHom.ker →* Multiplicative W) (B : ℝ)
    (hτ : ∀ h, ‖(τ h).toAdd - Q.shift h‖ ≤ B)
    (h : τ.ker) : ‖Q.shift (h : Q.linearHom.ker)‖ ≤ B := by
  have hh : τ (h : Q.linearHom.ker) = 1 := h.property
  have hb := hτ (h : Q.linearHom.ker)
  rw [hh] at hb
  change ‖(0 : W) - Q.shift (h : Q.linearHom.ker)‖ ≤ B at hb
  simpa only [zero_sub, norm_neg] using hb

/-- The finite-index, normal-subgroup and bounded-kernel conclusions of the
algebraic part of the recognition argument. -/
theorem exists_normal_finiteIndex_height [FiniteDimensional ℝ W] (Q : HeightQuasiAction H X W)
    (M : InvariantMean H) (hfinite : Set.Finite (Set.range Q.linear)) :
    ∃ (H₀ : Subgroup H), H₀.Normal ∧ H₀.FiniteIndex ∧
      ∃ (τ : H₀ →* Multiplicative W) (B : ℝ), 0 ≤ B ∧
        (∀ h : H₀, ‖(τ h).toAdd - Q.shift h‖ ≤ B) ∧
        (∀ h : τ.ker, ‖Q.shift (h : H₀)‖ ≤ B) := by
  obtain ⟨τ, B, hB, hτ⟩ := Q.exists_correctedHeight M
  refine ⟨Q.linearHom.ker, inferInstance, Q.finiteIndex_linear_kernel hfinite,
    τ, B, hB, hτ, ?_⟩
  exact Q.shift_bounded_on_kernel τ B hτ

end HeightQuasiAction

end PolycyclicRecognition

end

end OAI
