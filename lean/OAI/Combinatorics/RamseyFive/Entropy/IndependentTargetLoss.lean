import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.ChronologicalCapDomination
import OAI.Combinatorics.RamseyFive.Entropy.TargetLoss

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open ReverseCap
open scoped Classical BigOperators
noncomputable section
local instance (priority := high) independentTargetPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {Ω Θ Z T A B : Type*} [Fintype Ω] [Fintype Θ] [Fintype Z] [Fintype T]
  [Fintype A] [Fintype B]

lemma independent_target_event (p : Law Ω) (q : Law Θ) (P : Ω → Θ → Prop) :
    eventMass (adaptiveLaw p (fun _ => q))
      (Finset.univ.filter (fun z => P z.1 z.2)) =
        ∑ x, p x * eventMass q (Finset.univ.filter (P x)) := by
  simp only [eventMass, Finset.sum_filter, Fintype.sum_prod_type, adaptiveLaw,
    Finset.mul_sum, mul_ite, mul_zero]

lemma independent_target_endpoint_event (p : Law Ω) (q : Law Θ) (endpoint : Ω → B)
    (good : B → Prop) (P : B → Θ → Prop) :
    eventMass (adaptiveLaw p (fun _ => q))
      (Finset.univ.filter (fun z => good (endpoint z.1) ∧ P (endpoint z.1) z.2)) =
      ∑ b, (if good b then map p endpoint b else 0) *
        eventMass q (Finset.univ.filter (P b)) := by
  calc
    _ = ∑ x, p x * eventMass q (Finset.univ.filter
        (fun ξ => good (endpoint x) ∧ P (endpoint x) ξ)) := by
      simp only [eventMass, Finset.sum_filter, Fintype.sum_prod_type, adaptiveLaw,
        Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ x, p x * (if good (endpoint x) then
        eventMass q (Finset.univ.filter (P (endpoint x))) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hg : good (endpoint x) <;> simp [hg, eventMass]
    _ = ∑ b, map p endpoint b * (if good b then
        eventMass q (Finset.univ.filter (P b)) else 0) := (sum_map p endpoint (fun b => if good b then eventMass q (Finset.univ.filter (P b)) else 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      split_ifs <;> simp

lemma independent_level_endpoint_event (p : Law Ω) (μ : Law Z) (q : Law T)
    (endpoint : Ω → A) (good : A → Prop) (P : A → Z → T → Prop) :
    eventMass (adaptiveLaw p (fun _ => adaptiveLaw μ (fun _ => q)))
      (Finset.univ.filter (fun z => good (endpoint z.1) ∧ P (endpoint z.1) z.2.1 z.2.2)) =
      ∑ z, μ z*(∑ a, (if good a then map p endpoint a else 0)*
        eventMass q (Finset.univ.filter (P a z))) := by
  rw [independent_target_endpoint_event p (adaptiveLaw μ (fun _ => q)) endpoint good
    (fun a z => P a z.1 z.2)]
  simp_rw [independent_target_event μ q]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem independent_target_loss (p : Law Ω) (q : Law Θ) (a : Ω → A) (b : Ω → B)
    (goodA : A → Prop) (goodB : B → Prop)
    (ctx : Θ → Option (Finset A × Finset B)) (caps : Θ → Option (Finset B × Finset A))
    (hcoh : ∀ t, caps t≠none → ctx t≠none) :
    eventMass (adaptiveLaw p (fun _ => q)) (Finset.univ.filter
      (fun z => ¬TargetCovered (ctx z.2) (caps z.2) (a z.1) (b z.1))) ≤
      eventMass p (Finset.univ.filter (fun x => ¬goodA (a x))) +
      eventMass p (Finset.univ.filter (fun x => ¬goodB (b x))) +
      eventMass q (Finset.univ.filter (fun t => caps t=none)) +
      (∑ x, (if goodA x then map p a x else 0)*eventMass q
        (Finset.univ.filter (fun t => ∃ C, ctx t=some C ∧ x∉C.1))) +
      (∑ y, (if goodB y then map p b y else 0)*eventMass q
        (Finset.univ.filter (fun t => ∃ C, ctx t=some C ∧ y∉C.2))) +
      (∑ x, (if goodA x then map p a x else 0)*eventMass q
        (Finset.univ.filter (fun t => Excludes x ((caps t).map Prod.snd)))) +
      (∑ y, (if goodB y then map p b y else 0)*eventMass q
        (Finset.univ.filter (fun t => Excludes y ((caps t).map Prod.fst)))) := by
  have h := target_loss_split (adaptiveLaw p (fun _ => q)) (fun z => a z.1) (fun z => b z.1)
    goodA goodB (fun z => ctx z.2) (fun z => caps z.2) (fun z => hcoh z.2)
  rw [adaptive_event_first p (fun _ => q) (fun x => ¬goodA (a x)),
    adaptive_event_first p (fun _ => q) (fun x => ¬goodB (b x)),
    adaptive_event_second p (fun _ => q) (fun t => caps t=none),
    ← Finset.sum_mul, p.sum_one, one_mul] at h
  rw [independent_target_endpoint_event p q a goodA (fun x t => ∃ C, ctx t=some C ∧ x∉C.1),
    independent_target_endpoint_event p q b goodB (fun y t => ∃ C, ctx t=some C ∧ y∉C.2),
    independent_target_endpoint_event p q a goodA (fun x t => Excludes x ((caps t).map Prod.snd)),
    independent_target_endpoint_event p q b goodB (fun y t => Excludes y ((caps t).map Prod.fst))] at h
  exact h
end
end

open scoped Classical BigOperators
noncomputable section
local instance (priority := high) targetProductPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {Z T A : Type*} [Fintype Z] [Fintype T] [Fintype A]
lemma independent_target_event_general (μ : Law Z) (q : Law T) (P : Z × T → Prop) :
    eventMass (adaptiveLaw μ (fun _ => q)) (Finset.univ.filter P) =
      ∑ z, μ z*eventMass q (Finset.univ.filter (fun t => P (z,t))) := by
  exact independent_target_event μ q (fun z t => P (z,t))

lemma independent_weighted_event (μ : Law Z) (q : Law T) (g : A → ℝ)
    (P : A → Z × T → Prop) :
    (∑ a, g a*eventMass (adaptiveLaw μ (fun _ => q))
      (Finset.univ.filter (P a))) =
    ∑ z, μ z*(∑ a, g a*eventMass q (Finset.univ.filter (fun t => P a (z,t)))) := by
  simp_rw [independent_target_event_general μ q]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro a _
  ring
end

end SharpRamseyFive.FiniteEntropy

end OAI
