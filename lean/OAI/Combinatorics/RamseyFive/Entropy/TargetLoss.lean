import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.ProducedCapExclusion

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open ReverseCap
open scoped Classical BigOperators
noncomputable section
local instance (priority := high) targetLossPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {Ω A B : Type*} [Fintype Ω]

lemma target_mass_or (p : Law Ω) (P Q : Ω → Prop) :
    eventMass p (Finset.univ.filter (fun ω => P ω ∨ Q ω)) ≤
      eventMass p (Finset.univ.filter P) + eventMass p (Finset.univ.filter Q) := by
  simp only [eventMass, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp,hq]; linarith [p.nonneg ω]

lemma eventMass_filter_or7 (p : Law Ω) (P Q R S T U V : Ω → Prop) :
    eventMass p (Finset.univ.filter (fun ω => (((((P ω ∨ Q ω) ∨ R ω) ∨ S ω) ∨ T ω) ∨ U ω) ∨ V ω)) ≤
      eventMass p (Finset.univ.filter P) + eventMass p (Finset.univ.filter Q) +
      eventMass p (Finset.univ.filter R) + eventMass p (Finset.univ.filter S) +
      eventMass p (Finset.univ.filter T) + eventMass p (Finset.univ.filter U) +
      eventMass p (Finset.univ.filter V) := by
  have h2 := target_mass_or p P Q
  have h3 := target_mass_or p (fun ω => P ω ∨ Q ω) R
  have h4 := target_mass_or p (fun ω => (P ω ∨ Q ω) ∨ R ω) S
  have h5 := target_mass_or p (fun ω => ((P ω ∨ Q ω) ∨ R ω) ∨ S ω) T
  have h6 := target_mass_or p (fun ω => (((P ω ∨ Q ω) ∨ R ω) ∨ S ω) ∨ T ω) U
  have h7 := target_mass_or p (fun ω => ((((P ω ∨ Q ω) ∨ R ω) ∨ S ω) ∨ T ω) ∨ U ω) V
  linarith only [h2,h3,h4,h5,h6,h7]

def TargetCovered (ctx : Option (Finset A × Finset B))
    (caps : Option (Finset B × Finset A)) (a : A) (b : B) : Prop :=
  ∃ C D, ctx=some C ∧ caps=some D ∧ a∈C.1 ∧ b∈C.2 ∧ a∈D.2 ∧ b∈D.1

theorem target_loss_split (p : Law Ω) (a : Ω → A) (b : Ω → B)
    (goodA : A → Prop) (goodB : B → Prop)
    (ctx : Ω → Option (Finset A × Finset B)) (caps : Ω → Option (Finset B × Finset A))
    (hcoh : ∀ ω, caps ω≠none → ctx ω≠none) :
    eventMass p (Finset.univ.filter (fun ω => ¬TargetCovered (ctx ω) (caps ω) (a ω) (b ω))) ≤
      eventMass p (Finset.univ.filter (fun ω => ¬goodA (a ω))) +
      eventMass p (Finset.univ.filter (fun ω => ¬goodB (b ω))) +
      eventMass p (Finset.univ.filter (fun ω => caps ω=none)) +
      eventMass p (Finset.univ.filter (fun ω => goodA (a ω) ∧ ∃ C, ctx ω=some C ∧ a ω∉C.1)) +
      eventMass p (Finset.univ.filter (fun ω => goodB (b ω) ∧ ∃ C, ctx ω=some C ∧ b ω∉C.2)) +
      eventMass p (Finset.univ.filter (fun ω => goodA (a ω) ∧ Excludes (a ω) ((caps ω).map Prod.snd))) +
      eventMass p (Finset.univ.filter (fun ω => goodB (b ω) ∧ Excludes (b ω) ((caps ω).map Prod.fst))) := by
  let P := fun ω => ¬goodA (a ω)
  let Q := fun ω => ¬goodB (b ω)
  let R := fun ω => caps ω=none
  let S := fun ω => goodA (a ω) ∧ ∃ C, ctx ω=some C ∧ a ω∉C.1
  let T := fun ω => goodB (b ω) ∧ ∃ C, ctx ω=some C ∧ b ω∉C.2
  let U := fun ω => goodA (a ω) ∧ Excludes (a ω) ((caps ω).map Prod.snd)
  let V := fun ω => goodB (b ω) ∧ Excludes (b ω) ((caps ω).map Prod.fst)
  have hs : ∀ ω, ¬TargetCovered (ctx ω) (caps ω) (a ω) (b ω) →
      (((((P ω ∨ Q ω) ∨ R ω) ∨ S ω) ∨ T ω) ∨ U ω) ∨ V ω := by
    intro ω hn
    by_cases hga : goodA (a ω)
    · by_cases hgb : goodB (b ω)
      · cases hd : caps ω with
        | none => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hd))))
        | some D =>
          obtain ⟨C,hc⟩ := Option.ne_none_iff_exists'.mp (hcoh ω (by simp [hd]))
          by_cases ha : a ω∈C.1
          · by_cases hb : b ω∈C.2
            · by_cases ha' : a ω∈D.2
              · by_cases hb' : b ω∈D.1
                · exact (hn ⟨C,D,hc,hd,ha,hb,ha',hb'⟩).elim
                · exact Or.inr ⟨hgb, by simp [Excludes, hd, hb']⟩
              · exact Or.inl (Or.inr ⟨hga, by simp [Excludes, hd, ha']⟩)
            · exact Or.inl (Or.inl (Or.inr ⟨hgb,C,hc,hb⟩))
          · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hga,C,hc,ha⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hgb)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hga)))))
  exact (eventMass_filter_mono p _ _ hs).trans (eventMass_filter_or7 p P Q R S T U V)
end
end SharpRamseyFive.FiniteEntropy

end OAI
