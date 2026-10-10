import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationSources
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryRepresentativeSourceSeparation
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairRows HistoryPairRepresentatives
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

theorem internalSlot_ne_of_level_ne (C : InitialSourceChoice d Bs BD Bz k L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h g : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) h)
    (gh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) g)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hm : ∀i,sourceMass C.sources (internalSlot h i)≠0)
    (gm : ∀i,sourceMass C.sources (internalSlot g i)≠0)
    (i : InternalKey h) (j : InternalKey g) (hne : internalLevel h i≠internalLevel g j) :
    (internalSlot h i).value≠(internalSlot g j).value := by
  apply sourceMass_ne_of_disjoint _ (hm i) (gm j)
  apply source_disjoint_of_comp C hsep (internalSlot_source_mem _ h hh i)
    (internalSlot_source_mem _ g gh j) (internalSlot_role h hs i)
  change (internalSlot g j).role≠(internalSlot h i).role
  rw [internalSlot_role h hs i,internalSlot_role g gs j]
  exact fun he=>hne (SlotRole.compensation.inj he).symm

theorem representative_prime_injective (C : InitialSourceChoice d Bs BD Bz k L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h g : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) h)
    (gh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) g)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hm : ∀i,sourceMass C.sources (internalSlot h i)≠0)
    (gm : ∀i,sourceMass C.sources (internalSlot g i)≠0) :
    Function.Injective (prime h g) := by
  intro a b he
  obtain ⟨i,rfl⟩ := label_surjective h g a
  obtain ⟨j,rfl⟩ := label_surjective h g b
  apply (label_eq_iff h g i j).mpr
  refine ⟨?_,he⟩
  by_contra hne
  rcases i with i | i <;> rcases j with j | j
  · exact internalSlot_ne_of_level_ne C hsep h h hh hh hs hs hm hm i j hne he
  · exact internalSlot_ne_of_level_ne C hsep h g hh gh hs gs hm gm i j hne he
  · exact internalSlot_ne_of_level_ne C hsep g h gh hh gs hs gm hm i j hne he
  · exact internalSlot_ne_of_level_ne C hsep g g gh gh gs gs gm gm i j hne he

theorem representative_squares_pairwise (C : InitialSourceChoice d Bs BD Bz k L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h g : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) h)
    (gh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) g)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hm : ∀i,sourceMass C.sources (internalSlot h i)≠0)
    (gm : ∀i,sourceMass C.sources (internalSlot g i)≠0) :
    Pairwise (fun a b : Representative h g=>Nat.Coprime ((prime h g a)^2) ((prime h g b)^2)) := by
  intro a b hab
  exact ((Nat.coprime_primes (representative_prime h g hs gs a)
    (representative_prime h g hs gs b)).mpr
      ((representative_prime_injective C hsep h g hh gh hs gs hm gm).ne hab)).pow 2 2

theorem decoded_representative_prime_injective (C : InitialSourceChoice d Bs BD Bz k L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c e : HistoryChoices C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l)
    (ha : Template.Matches (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) a.small)
    (hb : Template.Matches (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) b.small)
    (hc : choicesMass C.sources _ V l c≠0) (he : choicesMass C.sources _ V l e≠0)
    (hs : (decodeHistory C.sources _ V l a c).Supported V outside)
    (gs : (decodeHistory C.sources _ V l b e).Supported V outside) :
    Function.Injective (prime (decodeHistory C.sources _ V l a c) (decodeHistory C.sources _ V l b e)) :=
  representative_prime_injective C hsep _ _
    (decoded_tree_source_labels _ _ _ _ _ _ ha) (decoded_tree_source_labels _ _ _ _ _ _ hb)
    hs gs (decoded_internalSlot_mass _ _ _ _ _ _ hc) (decoded_internalSlot_mass _ _ _ _ _ _ he)

end Ostmann.Arithmetic.HistoryRepresentativeSourceSeparation

end

end OAI
