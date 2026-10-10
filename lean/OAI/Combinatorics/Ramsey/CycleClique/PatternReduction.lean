import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.ChainProfiles
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.OptimalSystems
import OAI.Combinatorics.Ramsey.CycleClique.PathSystems

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def PatternVerified (k t : ℕ) (D : List (List ℕ)) : Prop :=
  ∃ C : FiniteCertificate, C.Valid k t (patternOrder D) (patternClique D)
    (patternEdges D) (patternAmount D) (patternEdgeCount D) []

theorem PatternVerified.impossible {V : Type*} [Fintype V] {G : SimpleGraph V}
    {Q : Set V} {k t : ℕ} {D : List (List ℕ)} (hD : PatternVerified k t D)
    (H : FiniteHyp G k t) (P : PathSystem G Q) (hP : P.Optimal k)
    (hQ : G.IsClique Q) (hc : Q.ncard = t)
    (hprofile : List.Forall₂ (ChainAmounts Q) P.chains D) : False := by
  obtain ⟨C,hC⟩ := hD
  obtain ⟨v,hv⟩ := Set.nonempty_of_ncard_ne_zero (s := Q) (by have := H.ht; omega)
  obtain ⟨_,ha,he,_⟩ := P.profile_parameters hprofile
  let O : OriginalSystem G Q k t (patternAmount D) (patternEdgeCount D) :=
    ⟨P,hP,hQ,hc,ha.symm,he.symm⟩
  exact C.sound H O (P.labelState hQ hprofile v) (by constructor <;> simp) hC

theorem finite_verified_of_patterns {V : Type*} [Fintype V] {G : SimpleGraph V}
    {Q : Set V} {k t : ℕ} (H : FiniteHyp G k t) (hQ : G.IsClique Q)
    (hc : Q.ncard = t)
    (hverified : ∀ D ∈ patternChoices t (k-t) [], PatternVerified k t D) : False := by
  obtain ⟨P,hP⟩ := PathSystem.exists_optimal G Q (k := k) (by have := H.htk; omega)
  obtain ⟨R,D,hD,hs,hn,ha,he⟩ := P.canonical_realization
  have hR := PathSystem.optimal_of_same hP ha he
  obtain ⟨ht,hL,he',hpos⟩ := R.profile_parameters hD
  have hbudget : patternAmount D ≤ k-t := by
    have hp := hR.1
    rw [←hL, hc] at hp
    omega
  have hm := mem_patternChoices (ht.trans hc) hbudget hpos hs hn (lower := []) (fun A _ => le_of_not_gt (by intro h; cases h))
  exact (hverified D hm).impossible H R hR hQ hc hD

end CycleClique

end OAI
