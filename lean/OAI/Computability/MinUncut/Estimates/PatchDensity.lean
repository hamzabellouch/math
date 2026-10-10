import Mathlib
import OAI.Computability.MinUncut.Estimates.Density

namespace OAI

section
noncomputable section
namespace MinUncut.OuterSmoothness.Density
lemma tv_ofMap_instances {A B : Type*} (a₁ a₂ : Fintype A) (b₁ b₂ : Fintype B)
    (h₁ h₂ : Nonempty B) (d₁ d₂ : DecidableEq A) (f : B → A) :
    @tvUniform A a₁ (@ofMap A a₁ B b₁ h₁ d₁ f) =
      @tvUniform A a₂ (@ofMap A a₂ B b₂ h₂ d₂ f) := by
  cases Subsingleton.elim a₁ a₂
  cases Subsingleton.elim b₁ b₂
  cases Subsingleton.elim d₁ d₂
  rfl
end MinUncut.OuterSmoothness.Density

end
end

end OAI
