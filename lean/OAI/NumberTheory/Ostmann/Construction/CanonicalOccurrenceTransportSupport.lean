import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportSources

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport

theorem supported_small_nodup {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) : h.root.small.Nodup := by
  have hprime : h.root.PrimeSmall := by
    rw [History.Supported.eq_def] at hs
    exact hs.2.1
  have hc := History.supported_root_coprime hs
  rw [State.Coprime,State.values,List.pairwise_append] at hc
  have hp := (List.pairwise_cons.mp (List.pairwise_cons.mp hc.1).2).2
  have hps := List.pairwise_map.mp hp
  exact hps.imp_of_mem (fun {a b} ha hb hab he => by
    subst b
    exact (hprime a ha).ne_one (by simpa only [Nat.Coprime,Nat.gcd_self] using hab))

theorem supported_left_concat_nodup {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) : (u++hp).Nodup :=
  (History.supported_child_small hs).1.nodup_iff.mp (supported_small_nodup (History.supported_left hs))

theorem supported_right_concat_nodup {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) : (u++hm).Nodup :=
  (History.supported_child_small hs).2.nodup_iff.mp (supported_small_nodup (History.supported_right hs))

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
