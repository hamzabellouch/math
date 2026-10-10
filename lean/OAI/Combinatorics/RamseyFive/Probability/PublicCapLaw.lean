import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.UniformCutoff
import OAI.Combinatorics.RamseyFive.Entropy.CapDecoder
import OAI.Combinatorics.RamseyFive.Entropy.SequentialLaw

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def publicCapLaw (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) : Law (Option (Finset A)) :=
  map (map (iid (iid (uniformOn W hW) (Fin n)) (Fin (uniformCutoff q C W n)))
    (firstAccepted (validationRows R S U C n q M)))
    (Option.map (cap R U q))

def ValidCap (S U : Finset A) (M : ℝ) (Y : Finset A) : Prop :=
  Y⊆U ∧ (Y.card:ℝ)≤M ∧ (9:ℝ)/10*S.card≤(S∩Y).card

lemma publicCapLaw_none (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) :
    publicCapLaw R S U C W hW n q M none=
      map (iid (iid (uniformOn W hW) (Fin n)) (Fin (uniformCutoff q C W n)))
        (firstAccepted (validationRows R S U C n q M)) none := by
  classical
  simp [publicCapLaw,map,Fintype.sum_option]

lemma publicCapLaw_positive (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ)
    (Y : Finset A) (hY : 0<publicCapLaw R S U C W hW n q M (some Y)) :
    ValidCap S U M Y := by
  obtain ⟨row,hr,he⟩ := map_positive _ _ _ hY
  cases row with
  | none => simp at he
  | some row =>
    have he' : cap R U q row=Y := Option.some.inj he
    subst Y
    obtain ⟨t,_,ht⟩ := map_positive _ _ _ hr
    obtain ⟨i,hi,hm⟩ := firstAccepted_index _ _ ht
    exact ⟨cap_subset _ _ _ _,(Finset.mem_filter.mp hm).2.2⟩

lemma publicCapLaw_failure (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hC : C.Nonempty) (hW : W.Nonempty) (hCW : C⊆W)
    (n : ℕ) (q M : ℝ)
    (hE : (9:ℝ)/10≤eventMass (iid (uniformOn C hC) (Fin n))
      (validationRows R S U C n q M)) :
    publicCapLaw R S U C W hW n q M none≤Real.exp (-q) := by
  rw [publicCapLaw_none]
  exact uniform_cutoff_failure q C W hC hW hCW n _
    (fun row hr=>(Finset.mem_filter.mp hr).2.1) hE

omit [Fintype A] in
lemma ValidCap.source_nonempty {S U Y : Finset A} {M : ℝ}
    (h : ValidCap S U M Y) (hS : S.Nonempty) : (S∩Y).Nonempty := by
  apply Finset.card_pos.mp
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hh := h.2.2
  have : (0:ℝ)<(S∩Y).card := lt_of_lt_of_le (by positivity) hh
  exact_mod_cast this

end SharpRamseyFive.ReverseCap

end OAI
