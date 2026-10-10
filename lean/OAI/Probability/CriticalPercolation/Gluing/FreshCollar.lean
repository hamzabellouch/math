import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.Gluing.ConditionalGluing
import OAI.Probability.CriticalPercolation.Gluing.ContactSelection
import OAI.Probability.CriticalPercolation.Gluing.FewContacts
import OAI.Probability.CriticalPercolation.Gluing.FreshContactTransfer
import OAI.Probability.CriticalPercolation.Gluing.FreshTrial

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem fresh_collar_transfer_from_geometry (hlocal : G.LocallyFinite)
    (q : E → unitInterval) (π : V → ℤ) (o : V) (Input T : Set V)
    (J : Finset ℤ) (hJ : J.Nonempty) (ho : ∀ j∈J, j ≤ π o)
    (hInput : ∀ j∈J, ∀ v∈Input, π v<j)
    (hcross : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (p : unitInterval) (hp : (p : ℝ)<1)
    (hq : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → π v=j → π w<j → (q e : ℝ) ≤ p)
    (D k M N : ℕ) (hD : ∀ j∈J, ∀ v, π v=j → (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hk : M*N ≤ k)
    (C : V → V → Prop) (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (hfinite : ∀ v, {w | C v w}.Finite) (hbound : ∀ v, {w | C v w}.ncard ≤ M)
    (F : ℤ → V → Set E) (B : ℤ → V → Set V)
    (hF : ∀ j∈J, ∀ v, F j v ⊆ (G.inducedEdges {w | j ≤ π w})ᶜ)
    (hconnect : ∀ j∈J, ∀ v, π v=j → ∀ b∈B j v, (G.openGraph (F j v)).Reachable v b)
    (hdis : ∀ j∈J, ∀ v w, ¬C v w → Disjoint (F j v) (F j w))
    (s₀ K η lam : ℝ) (hK : 0 ≤ K) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hs : ∀ j∈J, ∀ v, π v=j → s₀ ≤ (BernoulliProduct.law q).real (allOpen (F j v)))
    (hN : K ≤ N*s₀)
    (hmean : ∀ j∈J, ∀ v, π v=j →
      1-η ≤ (BernoulliProduct.law q).real (G.seedHitEvent (B j v) T)) :
    (BernoulliProduct.law q).real (G.hitEvent o Input\G.hitEvent o T) ≤
      1/((J.card : ℝ)*(1-(p : ℝ))^(D*k))+Real.exp (-K)+(K+1)*η/lam+lam := by
  obtain ⟨j,hj,hfew⟩ := G.exists_few_contact_level hlocal q π o J hJ ho hcross p hp hq D k hD
  obtain ⟨d,hd,hsel⟩ := G.honest_contact_selection π j o k C hrefl hsymm M N hM hk
    hfinite hbound (fun v => (BernoulliProduct.law q).real (allOpen (F j v))) s₀ K hK
    (fun v hv => ⟨hs j hj v hv,measureReal_le_one⟩) hN
  have hh := G.fresh_contact_transfer q (G.inducedEdges {v | j ≤ π v})
    (G.inducedEdges {v | j ≤ π v})ᶜ disjoint_compl_right d (F j) (B j)
    {v | π v=j} T Input o hd (hF j hj) (hconnect j hj)
    (G.manyContacts π j o k) (G.fewContacts π j o k) (G.measurableSet_manyContacts π j o k)
    (by
      intro ω hω
      have hne := G.levelContacts_nonempty_of_hit π j o (ho j hj) (hcross j hj) ω
        (G.hitEvent_mono_target o (hInput j hj) hω)
      by_cases hf : ω∈G.fewContacts π j o k
      · exact Or.inl hf
      · exact Or.inr ⟨hne,hf⟩)
    (by
      intro ω hω v hv
      have hmem := (hsel ω hω).1 hv
      exact ⟨hmem.2,G.levelContacts_reachable π j o ω hmem⟩)
    K η lam (by linarith) hη hlam (hmean j hj)
    (by
      intro ω hω v hv w hw hvw
      exact hdis j hj v w ((hsel ω hω).2.1 hv hw hvw))
    (fun ω hω => (hsel ω hω).2.2.1) (fun ω hω => (hsel ω hω).2.2.2)
  linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
