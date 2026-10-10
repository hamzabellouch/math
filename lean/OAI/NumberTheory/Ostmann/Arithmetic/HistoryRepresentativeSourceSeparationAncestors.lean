import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationInjective

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryRepresentativeSourceSeparation
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairRows HistoryPairRepresentatives HistoryPairPattern
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

theorem internalSlot_ne_rootSlot (C : InitialSourceChoice d Bs BD Bz k L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h g : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) h)
    (gh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) g)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hm : ∀i,sourceMass C.sources (internalSlot h i)≠0)
    (gm : ∀q∈g.root.small,sourceMass C.sources q≠0)
    (i : InternalKey h) (j : Fin g.root.small.length) :
    (internalSlot h i).value≠(g.root.small.get j).value := by
  apply sourceMass_ne_of_disjoint _ (hm i) (gm _ (List.get_mem _ j))
  apply source_disjoint_of_comp C hsep (internalSlot_source_mem _ h hh i)
    (rootSlot_source_mem _ g gh j) (internalSlot_role h hs i)
  change (g.root.small.get j).role≠(internalSlot h i).role
  rw [internalSlot_role h hs i]
  intro he
  have ht := History.supported_template gs _ (List.get_mem _ j) _ he
  have hi := internalLevel_pos_le h i
  omega

lemma natCast_nonzero_of_prime_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    (q:ZMod p)≠0 := by
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff q p).mp hz
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)

theorem actual_ancestor_units (C : InitialSourceChoice d Bs BD Bz k L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h g : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) h)
    (gh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) g)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hm : ∀i,sourceMass C.sources (internalSlot h i)≠0)
    (gm : ∀i,sourceMass C.sources (internalSlot g i)≠0)
    (hr : ∀q∈h.root.small,sourceMass C.sources q≠0)
    (gr : ∀q∈g.root.small,sourceMass C.sources q≠0) (i : Occurrences h g) :
    AncestorUnits h g (fun j=>(pairSample h g j:ZMod (slot h g i).value)) i := by
  have hprime : h.root.PrimeSmall := by rw [History.Supported.eq_def] at hs; exact hs.2.1
  have gprime : g.root.PrimeSmall := by rw [History.Supported.eq_def] at gs; exact gs.2.1
  rcases i with i | i
  · intro j hj
    dsimp only
    rw [leftMap_sample]
    rcases j with j | j
    · change (((h.root.small.get j).value:ℤ):ZMod (internalSlot h i).value)≠0
      simp only [Int.cast_natCast]
      exact natCast_nonzero_of_prime_ne (internalSlot_prime h hs i)
        (hprime _ (List.get_mem _ j)) (internalSlot_ne_rootSlot C hsep h h hh hh hs hs hm hr i j)
    · change (((internalSlot h j).value:ℤ):ZMod (internalSlot h i).value)≠0
      simp only [Int.cast_natCast]
      exact natCast_nonzero_of_prime_ne (internalSlot_prime h hs i) (internalSlot_prime h hs j)
        (internalSlot_ne_of_level_ne C hsep h h hh hh hs hs hm hm i j (Nat.ne_of_lt hj))
  · intro j hj
    rcases j with j | j
    · change (((g.root.small.get j).value:ℤ):ZMod (internalSlot g i).value)≠0
      simp only [Int.cast_natCast]
      exact natCast_nonzero_of_prime_ne (internalSlot_prime g gs i)
        (gprime _ (List.get_mem _ j)) (internalSlot_ne_rootSlot C hsep g g gh gh gs gs gm gr i j)
    · change (((internalSlot g j).value:ℤ):ZMod (internalSlot g i).value)≠0
      simp only [Int.cast_natCast]
      exact natCast_nonzero_of_prime_ne (internalSlot_prime g gs i) (internalSlot_prime g gs j)
        (internalSlot_ne_of_level_ne C hsep g g gh gh gs gs gm gm i j (Nat.ne_of_lt hj))

end Ostmann.Arithmetic.HistoryRepresentativeSourceSeparation

end

end OAI
