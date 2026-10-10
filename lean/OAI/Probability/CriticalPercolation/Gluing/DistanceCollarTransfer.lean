import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.FreshCollar
import OAI.Probability.CriticalPercolation.Gluing.InwardTrial
import OAI.Probability.CriticalPercolation.Gluing.OpenTrialBound

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem distance_collar_transfer (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (q : E → unitInterval) (Input T : Set V) (hInput : Input.Nonempty) (o : V)
    (m R : ℕ) (J : Finset ℤ) (hJ : J.Nonempty)
    (hJrange : ∀ j∈J, (m : ℤ)<j ∧ j ≤ R)
    (ho : R ≤ G.distanceTo Input o)
    (p₀ p : unitInterval) (hp : (p : ℝ)<1)
    (hq : ∀ e∈G.inducedEdges (G.vertexCollar Input R), (p₀ : ℝ) ≤ q e ∧ (q e : ℝ) ≤ p)
    (D k M N VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hk : M*N ≤ k)
    (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (K η lam : ℝ) (hK : 0 ≤ K) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hN : K ≤ N*(p₀ : ℝ)^(m+1+VM))
    (hmean : ∀ y∈G.vertexCollar Input R,
      1-η ≤ (BernoulliProduct.law q).real (G.seedHitEvent (G.vertexBall y m) T)) :
    (BernoulliProduct.law q).real (G.hitEvent o Input\G.hitEvent o T) ≤
      1/((J.card : ℝ)*(1-(p : ℝ))^(D*k))+Real.exp (-K)+(K+1)*η/lam+lam := by
  let π : V → ℤ := fun v => G.distanceTo Input v
  let Q : Set V := {v | m<G.distanceTo Input v}
  have ht : ∀ v : Q, ∃ (y : V) (F : Set E), F.Finite ∧
      F.ncard ≤ m+1+(G.vertexBall y m).ncard ∧
      G.distanceTo Input y+(m+1)=G.distanceTo Input v ∧
      F⊆G.inducedEdges (G.vertexBall v (2*m+1)∩{z | G.distanceTo Input z ≤ G.distanceTo Input v}) ∧
      F⊆(G.inducedEdges {z | G.distanceTo Input v ≤ G.distanceTo Input z})ᶜ ∧
      ∀ z∈G.vertexBall y m, (G.openGraph F).Reachable v z := by
    intro v
    exact G.inward_seed_trial hc hl hInput v m v.2
  choose y F hfin hcard hy hends hfresh hreach using ht
  let Ft (j : ℤ) (v : V) : Set E := if h : π v=j ∧ v∈Q then F ⟨v,h.2⟩ else ∅
  let Bt (j : ℤ) (v : V) : Set V := if h : π v=j ∧ v∈Q then G.vertexBall (y ⟨v,h.2⟩) m else ∅
  have hlevel (j : ℤ) (hj : j∈J) (v : V) (hv : π v=j) : π v=j ∧ v∈Q := by
    refine ⟨hv,?_⟩
    change m<G.distanceTo Input v
    have hh := (hJrange j hj).1
    change (G.distanceTo Input v : ℤ)=j at hv
    omega
  have hsupp (j : ℤ) (v : V) : Ft j v⊆G.inducedEdges (G.vertexBall v (2*m+1)) := by
    dsimp only [Ft]
    split_ifs with h
    · intro e he z hz
      exact (hends ⟨v,h.2⟩ he z hz).1
    · exact Set.empty_subset _
  have hcollar (j : ℤ) (hj : j∈J) (v : V) : Ft j v⊆G.inducedEdges (G.vertexCollar Input R) := by
    dsimp only [Ft]
    split_ifs with h
    · intro e he z hz
      apply (G.distanceTo_le_iff hc hInput z R).mp
      have h1 : G.distanceTo Input z ≤ G.distanceTo Input v := (hends ⟨v,h.2⟩ he z hz).2
      have h2 := (hJrange j hj).2
      have h3 : (G.distanceTo Input v : ℤ)=j := h.1
      omega
    · exact Set.empty_subset _
  apply G.fresh_collar_transfer_from_geometry hl q π o Input T J hJ
    (by
      intro j hj
      change j ≤ (G.distanceTo Input o : ℤ)
      have := (hJrange j hj).2
      omega)
    (by
      intro j hj v hv
      have hv0 := (G.distanceTo_eq_zero_iff hc hInput v).mpr hv
      change (G.distanceTo Input v : ℤ)<j
      have := (hJrange j hj).1
      omega)
    (by
      intro j hj e v w he hv hw
      by_cases hvw : v=w
      · subst w; omega
      · have ha : G.fullGraph.Adj w v := ⟨⟨e,Set.mem_univ _,by simpa only [Sym2.eq_swap] using he⟩,Ne.symm hvw⟩
        have hs := G.distanceTo_adj hc hInput ha
        change j ≤ (G.distanceTo Input v : ℤ) at hv
        change (G.distanceTo Input w : ℤ)<j at hw
        change (G.distanceTo Input v : ℤ)=j
        omega)
    p hp
    (by
      intro j hj e v w he hv hw
      apply (hq e ?_).2
      intro z hz
      rw [he] at hz
      have hz' : z=v ∨ z=w := Sym2.mem_iff.mp hz
      apply (G.distanceTo_le_iff hc hInput z R).mp
      have hjR := (hJrange j hj).2
      change (G.distanceTo Input v : ℤ)=j at hv
      change (G.distanceTo Input w : ℤ)<j at hw
      rcases hz' with hz'|hz' <;> subst z <;> omega)
    D k M N (fun _j _hj v _hv => hD v) hM hk
    (fun v w => w∈G.vertexBall v (4*m+2))
    (fun v => G.mem_vertexBall_self v _) (fun {_ _} h => G.vertexBall_comm.mp h)
    (fun v => G.vertexBall_finite hl v _) hMbound Ft Bt
    (by
      intro j hj v
      dsimp only [Ft]
      split_ifs with h
      · intro e he he'
        apply hfresh ⟨v,h.2⟩ he
        intro z hz
        have hh := he' z hz
        change j ≤ (G.distanceTo Input z : ℤ) at hh
        have hv : (G.distanceTo Input v : ℤ)=j := h.1
        change G.distanceTo Input v ≤ G.distanceTo Input z
        omega
      · exact Set.empty_subset _)
    (by
      intro j hj v hv b hb
      have hh := hlevel j hj v hv
      dsimp only [Bt] at hb
      rw [dite_eq_left hh] at hb
      dsimp only [Ft]
      rw [dite_eq_left hh]
      exact hreach ⟨v,hh.2⟩ b hb)
    (by
      intro j hj v w h
      exact G.inward_trials_disjoint (Ft j) m (hsupp j) h)
    ((p₀ : ℝ)^(m+1+VM)) K η lam hK hη hlam
    (by
      intro j hj v hv
      have hh := hlevel j hj v hv
      have hFfinite : (Ft j v).Finite := by simpa only [Ft,dite_eq_left hh] using hfin ⟨v,hh.2⟩
      apply law_allOpen_lower q (Ft j v) hFfinite p₀ (m+1+VM)
      · rw [show Ft j v=F ⟨v,hh.2⟩ by simp only [Ft,dite_eq_left hh]]
        exact (hcard ⟨v,hh.2⟩).trans (by have := hVM (y ⟨v,hh.2⟩); omega)
      · intro e he
        exact (hq e (hcollar j hj v he)).1)
    hN
    (by
      intro j hj v hv
      have hh := hlevel j hj v hv
      dsimp only [Bt]
      rw [dite_eq_left hh]
      apply hmean
      apply (G.distanceTo_le_iff hc hInput _ R).mp
      have h1 := hy ⟨v,hh.2⟩
      change G.distanceTo Input (y ⟨v,hh.2⟩)+(m+1)=G.distanceTo Input v at h1
      have h2 := (hJrange j hj).2
      change (G.distanceTo Input v : ℤ)=j at hv
      omega)

end CriticalPercolation.BondGraph
end
end
end

end OAI
