import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.MapOutput

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section CandidateUniqueness
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def QueryCall.Separated (H : τ → Finset ι) (c : QueryCall ι τ) : Prop :=
  ∀ T, some T ≠ c.parent → ((H T) ∩ c.focus).card ≤ 1

lemma gridCandidates_key_injective (H : τ → Finset ι) (c : QueryCall ι τ)
    (hc : c.Separated H) :
    Set.InjOn Prod.snd (↑(gridCandidates H c.focus c.parent) : Set (ι × τ)) := by
  intro a ha b hb hab
  obtain ⟨haF,haT,haP⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbF,hbT,_⟩ := Finset.mem_filter.mp hb
  have haF := (Finset.mem_product.mp haF).1
  have hbF := (Finset.mem_product.mp hbF).1
  apply Prod.ext _ hab
  have haI : a.1 ∈ H a.2 ∩ c.focus := Finset.mem_inter.mpr ⟨haT,haF⟩
  have hbI : b.1 ∈ H a.2 ∩ c.focus := Finset.mem_inter.mpr ⟨hab ▸ hbT,hbF⟩
  exact (Finset.card_le_one.mp (hc a.2 haP)) _ haI _ hbI

theorem QueryCall.keys_nodup (H : τ → Finset ι) (c : QueryCall ι τ)
    (hc : c.Separated H) : (c.keys H).Nodup := by
  apply List.Nodup.map_on _ (Finset.nodup_toList _)
  intro a ha b hb hab
  exact gridCandidates_key_injective H c hc
    (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb) hab

omit [Fintype τ] [DecidableEq τ] in
lemma separated_singleton (H : τ → Finset ι) (address : List (ι × τ))
    (e : ι) (parent : Option τ) :
    (QueryCall.mk address {e} parent).Separated H := by
  intro T _
  exact (Finset.card_le_card Finset.inter_subset_right).trans (by simp)

omit [Fintype τ] [DecidableEq τ] in

lemma separated_child (H : τ → Finset ι)
    (hlin : ∀ T S, T ≠ S → (H T ∩ H S).card ≤ 1)
    (address : List (ι × τ)) (e : ι) (T : τ) :
    (QueryCall.mk ((e,T)::address) ((H T).erase e) (some T)).Separated H := by
  intro S hS
  have hne : S ≠ T := by simpa using hS
  change (H S ∩ (H T).erase e).card ≤ 1
  apply (Finset.card_le_card (show H S ∩ (H T).erase e ⊆ H S ∩ H T from
    fun x hx => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
      Finset.erase_subset _ _ (Finset.mem_inter.mp hx).2⟩)).trans
  exact hlin S T hne

end CandidateUniqueness
end SharpTerminalLeave

end

end OAI
