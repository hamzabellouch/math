import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.HeightShift
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RationalLoader
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ObservationByInstruction

namespace OAI

/-! A rational loader on an arbitrary horizontal coding sheet. -/

open Set
namespace ForcedComputation
open ShearFlows

def shiftedLoader (p q : Fin 2 → ℚ) (z : ℚ) : Input :=
  (loaderInput p q (1 / 2)).shiftHeight (z - 1 / 2)

theorem shiftedLoader_valid (p q : Fin 2 → ℚ) (z : ℚ)
    (hp : ∀ j, 1 / 8 ≤ p j ∧ p j ≤ 7 / 8)
    (hq : ∀ j, 1 / 8 ≤ q j ∧ q j ≤ 7 / 8) : ValidInput (shiftedLoader p q z) :=
  (loaderInput_valid p q (1 / 2) hp hq (by norm_num)).shiftHeight _

@[simp] theorem shiftedLoader_height (p q : Fin 2 → ℚ) (z : ℚ) :
    ((shiftedLoader p q z).codingHeight : ℝ) = z := by
  simp only [shiftedLoader, Input.shiftHeight_codingHeight, loaderInput,
    Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  ring

@[simp] theorem shiftedLoader_period (p q : Fin 2 → ℚ) (z : ℚ) :
    ((shiftedLoader p q z).period : ℝ) = 1 := by
  norm_num [shiftedLoader, loaderInput, Input.shiftHeight]

theorem shiftedLoader_endpoint {p q : Fin 2 → ℚ} {z : ℚ}
    (hd : ValidInput (shiftedLoader p q z)) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (shiftedLoader p q z).realizingVelocity Φ) :
    Φ 1 (atHeight (fun j => (p j : ℝ)) z) = atHeight (fun j => (q j : ℝ)) z := by
  have hΦ' : IsMaterialFlow (shiftedLoader p q z).period
      (shiftedLoader p q z).realizingVelocity Φ := by
    simpa only [shiftedLoader_period] using hΦ
  have hδ : (0 : ℝ) < (shiftedLoader p q z).tubeRadius := by
    exact_mod_cast tubeRadius_pos hd
  have hx : atHeight (fun j => (p j : ℝ)) z ∈
      sourceTube (loaderInstruction p q) z (shiftedLoader p q z).tubeRadius := by
    refine ⟨_, loaderInstruction_contains_center p q, ?_, ?_⟩
    · simpa only [atHeight_horizontal, sub_self, norm_zero] using hδ
    · simpa [atHeight] using hδ
  have he := realizingVelocity_periodMap hd hΦ' (b := loaderInstruction p q)
    (by simp [shiftedLoader, loaderInput, Input.shiftHeight]) (by
      simpa only [shiftedLoader_height] using hx)
  rw [atHeight_horizontal, loaderInstruction_center] at he
  change Φ 1 (atHeight (fun j => (p j : ℝ)) z) =
    atHeight (fun j => (q j : ℝ)) z at he
  exact he

theorem shiftedLoader_first_le {p q : Fin 2 → ℚ} {z : ℚ}
    (hd : ValidInput (shiftedLoader p q z)) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (shiftedLoader p q z).realizingVelocity Φ)
    {a t : ℝ} (hp : (p 0 : ℝ) ≤ a) (hq : (q 0 : ℝ) ≤ a) (ht : t ∈ Icc (0 : ℝ) 1) :
    Φ t (atHeight (fun j => (p j : ℝ)) z) 0 ≤ a + 1 / 256 := by
  have hΦ' : IsMaterialFlow (shiftedLoader p q z).period
      (shiftedLoader p q z).realizingVelocity Φ := by
    simpa only [shiftedLoader_period] using hΦ
  have he := materialFlow_first_le_of_mem hd hΦ' (b := loaderInstruction p q)
    (by simp [shiftedLoader, loaderInput, Input.shiftHeight])
    (loaderInstruction_contains_center p q)
    (by simpa [loaderInstruction, centeredBox_center] using hp)
    (by simpa [loaderInstruction, centeredBox_center] using hq) ht
  simp only [shiftedLoader_height] at he
  norm_num only [shiftedLoader, Input.shiftHeight, loaderInput,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at he
  exact he

end ForcedComputation

end OAI
