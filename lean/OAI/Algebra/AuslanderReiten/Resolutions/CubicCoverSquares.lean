import OAI.Algebra.AuslanderReiten.Cones.TwoConeExtensionDiagrams

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
universe u
variable {R : Type u} [Ring R] (D : Data R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))

theorem firstCokernelMap_cover (n : ℕ) :
    (D.first n).comp (baseStepInclusion D hex (n+3)) =
      (baseStepInclusion D hex n).comp (firstCokernelMap D (n+1)) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := (LinearMap.range (D.d (n+4))).mkQ_surjective z
  exact (DFunLike.congr_fun (D.first_comm n) z).symm

theorem secondCokernelMap_cover (n : ℕ) :
    (D.second n).comp (baseStepInclusion D hex (n+3)) =
      (baseStepInclusion D hex n).comp (secondCokernelMap D (n+1)) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := (LinearMap.range (D.d (n+4))).mkQ_surjective z
  exact (DFunLike.congr_fun (D.second_comm n) z).symm

theorem firstCokernelMap_quotient (n : ℕ) :
    ((LinearMap.range (D.d n)).mkQ).comp (D.first n) =
      (firstCokernelMap D n).comp (LinearMap.range (D.d (n+3))).mkQ := rfl

theorem secondCokernelMap_quotient (n : ℕ) :
    ((LinearMap.range (D.d n)).mkQ).comp (D.second n) =
      (secondCokernelMap D n).comp (LinearMap.range (D.d (n+3))).mkQ := rfl

end ArExplicit.TwoCone

end

end OAI
