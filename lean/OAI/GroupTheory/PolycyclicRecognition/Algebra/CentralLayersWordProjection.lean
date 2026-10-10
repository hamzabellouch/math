import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalNilpotentQuotient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntertwinedActionWords

namespace OAI

/-! # Projecting a uniform action bound to the central factors -/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

theorem centralLayers_word_projection (c : ℕ) (K : Subgroup G) (d : ℕ)
    (hd : ∀ w : List K, w.length = d → actionOperatorWord
      (fun g : K => (centralLayersAction F c g).toLinearMap - 1) w = 0)
    (i : Fin c) :
    linearActionFiltration (fun g : K => (rationalUpperCentralAction F i g).toLinearMap - 1) d = ⊥ := by
  apply linearActionFiltration_eq_bot_of_word_zero
  intro w hw
  apply LinearMap.ext
  intro v
  let D := fun g : K => (centralLayersAction F c g).toLinearMap - 1
  let E := fun g : K => (rationalUpperCentralAction F i g).toLinearMap - 1
  let q : CentralLayersSpace F c →ₗ[ℚ] RationalAbelianSpace (CentralLayer F i) := LinearMap.proj i
  let x : CentralLayersSpace F c := Pi.single i v
  have hx : q x = v := by simp [q, x]
  have he := actionOperatorWord_intertwines D E q (fun _ _ => rfl) w x
  rw [hd w hw] at he
  simpa only [map_zero, hx, LinearMap.zero_apply] using he.symm

end PolycyclicRecognition

end

end OAI
