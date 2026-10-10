import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedTrajectories
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RationalLoader

namespace OAI

/-! A safe rational loader transfers the periodic body's continuous-time event
criterion to the fixed starting point of the initialized fluid. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set

def fixedStart : Fin 2 → ℚ := ![1 / 8, 3 / 8]

theorem initialized_observation_iff {q : Fin 2 → ℚ} {body : Input}
    (hl : ValidInput (loaderInput fixedStart q (1 / 2))) (hb : ValidInput body)
    {Φ Ψ Λ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow body.period
      (initializedProgram (loaderInput fixedStart q (1 / 2)) body) Φ)
    (hΨ : IsMaterialFlow body.period body.realizingVelocity Ψ)
    (hΛ : IsMaterialFlow 1 (loaderInput fixedStart q (1 / 2)).realizingVelocity Λ)
    {H : Prop} {upper : ℝ}
    (hbody : (∃ t : ℝ, 0 ≤ t ∧
      1 / 2 < Ψ t (atHeight (fun j => (q j : ℝ)) (1 / 2)) 0 ∧
      Ψ t (atHeight (fun j => (q j : ℝ)) (1 / 2)) 0 < upper) ↔ H)
    (hq : ¬H → (q 0 : ℝ) ≤ 1 / 3) :
    (∃ t : ℝ, 0 ≤ t ∧
      1 / 2 < Φ t (atHeight (fun j => (fixedStart j : ℝ)) (1 / 2)) 0 ∧
      Φ t (atHeight (fun j => (fixedStart j : ℝ)) (1 / 2)) 0 < upper) ↔ H := by
  have hΛ' : IsMaterialFlow (loaderInput fixedStart q (1 / 2)).period
      (loaderInput fixedStart q (1 / 2)).realizingVelocity Λ := by
    simpa only [loaderInput, Rat.cast_one] using hΛ
  have hload : Φ 1 (atHeight (fun j => (fixedStart j : ℝ)) (1 / 2)) =
      atHeight (fun j => (q j : ℝ)) (1 / 2) := by
    rw [initializedFlow_loading hl hb hΦ hΛ' _ (t := 1) (by norm_num)]
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using loaderFlow_endpoint hl hΛ
  constructor
  · rintro ⟨t, ht, hx, hy⟩
    by_cases hlate : 1 ≤ t
    · apply hbody.mp
      refine ⟨t - 1, by linarith, ?_⟩
      rw [initializedFlow_tail hl hb hΦ hΨ _ hlate, hload] at hx hy
      exact ⟨hx, hy⟩
    · by_contra hn
      have hΛbound := loaderFlow_first_le hl hΛ
        (a := 1 / 3) (by norm_num [fixedStart]) (hq hn)
        (show t ∈ Icc (0 : ℝ) 1 from ⟨ht, (lt_of_not_ge hlate).le⟩)
      rw [initializedFlow_loading hl hb hΦ hΛ' _ ⟨ht, (lt_of_not_ge hlate).le⟩] at hx
      linarith
  · intro h
    obtain ⟨t, ht, hx, hy⟩ := hbody.mpr h
    refine ⟨t + 1, by linarith, ?_⟩
    rw [initializedFlow_tail hl hb hΦ hΨ _ (by linarith), hload]
    simpa only [add_sub_cancel_right] using And.intro hx hy

end ForcedComputation

end

end OAI
