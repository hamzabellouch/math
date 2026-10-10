import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ChosenIntegralResolution
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteAugmentationKernel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralKernelRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteKernelsFromFillings
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InfiniteCyclicFiniteness

namespace OAI

/-! # Finiteness from uniformly controlled fillings

Finite group generation supplies the first augmentation kernel. Each further
kernel is finite by the controlled-filling comparison, so the chosen projective
cover remains finite through the required degree.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] [Group.FG G]

theorem typeFP_of_controlledCycleFillings (m : ℕ)
    (hfill : ∀ n, n + 2 ≤ m → HasControlledCycleFillings ℤ G n) : TypeFP G m := by
  have hfin : ∀ i, i ≤ m →
      IntegralRepresentationFinite G ((chosenIntegralResolution G).complex.X i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro him
      rcases i with _ | (_ | n)
      · exact integralRepresentationFinite_leftRegular G
      · exact chosenIntegralPresentation_finite _
          (integralKernel_finite (integralFreeAugmentation (G := G)) integralAugmentationKernel_fg)
      · apply chosenIntegralResolution_step_finite
        apply integralKernel_finite
        exact finite_resolution_kernel_of_controlledFillings (chosenIntegralResolution G)
          (ih (n + 1) (by omega) (by omega)) (hfill n (by omega))
  exact ⟨chosenIntegralResolution G, hfin⟩

omit [Group.FG G] in
theorem TypeFP.mono {m n : ℕ} (h : TypeFP G n) (hmn : m ≤ n) : TypeFP G m := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun i hi => hP i (hi.trans hmn)⟩

end PolycyclicRecognition

end

end OAI
