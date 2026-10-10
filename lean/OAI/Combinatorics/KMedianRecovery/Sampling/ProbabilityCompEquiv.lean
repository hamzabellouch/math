import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Average

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
lemma probability_comp_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (E : Ξ → Prop) : probability (fun x => E (e x)) = probability E := by
  classical
  exact average_equiv e _ _ (fun _ => rfl)

lemma probability_ignore_middle {Ω Ξ Z : Type*} [Fintype Ω] [Fintype Ξ] [Fintype Z]
    [Nonempty Ξ] (E : Ω → Z → Prop) :
    probability (fun seed : (Ω × Ξ) × Z => E seed.1.1 seed.2) =
      probability (fun seed : Ω × Z => E seed.1 seed.2) := by
  classical
  unfold probability
  rw [average_prod,average_prod]
  conv_rhs => rw [average_prod]
  congr 1
  funext x
  exact average_const (Ω := Ξ) (average (fun z : Z => if E x z then 1 else 0))
end MetricKMedianRecovery.FiniteSampling

end OAI
