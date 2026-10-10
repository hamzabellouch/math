import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyProcess

namespace OAI

                                  
section

/-! Causality of actual fixed-slot heavy records, including the cooldown state. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

theorem pair_inputs (a : X) (hr : 0≤r) (hΛ : 2*Fintype.card X<Fintype.card Λ)
    (h v : ℕ → Prop) (x y : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) (hh : ∀ j<t, h j ↔ v j) (hx : ∀ j<t, x j=y j) :
    runPair a hr hΛ h x R hR t=runPair a hr hΛ v y R hR t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runPair,runPair,ih (fun j hj => hh j (by omega)) (fun j hj => hx j (by omega))]
    rw [propext (hh t (by omega)),hx t (by omega)]

theorem run_inputs (a : X) (hr : 0≤r) (hΛ : 2*Fintype.card X<Fintype.card Λ)
    (h v : ℕ → Prop) (x y : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) (hh : ∀ j<t, h j ↔ v j) (hx : ∀ j<t, x j=y j) :
    run a hr hΛ h x R hR t=run a hr hΛ v y R hR t := by
  unfold run
  rw [pair_inputs a hr hΛ h v x y R hR t hh hx]

omit [Fintype X] in
theorem centers_inputs (h v : ℕ → Prop) (x y : ℕ → X) (t : ℕ)
    (hh : ∀ j<t, h j ↔ v j) (hx : ∀ j<t, x j=y j) :
    HeavySchedule.centers r h x t=HeavySchedule.centers r v y t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [HeavySchedule.centers,HeavySchedule.centers,
      ih (fun j hj => hh j (by omega)) (fun j hj => hx j (by omega)),
      propext (hh t (by omega)),hx t (by omega)]

end UniformKServer.HeavyProcess

end


end

end OAI
