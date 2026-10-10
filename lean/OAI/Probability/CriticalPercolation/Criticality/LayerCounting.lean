import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.Exploration.BallIncidence
import OAI.Probability.CriticalPercolation.Exploration.LayerExposure
import OAI.Probability.CriticalPercolation.Gluing.StripMoves
import OAI.Probability.CriticalPercolation.Criticality.BlockLocalization
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def layerComponent (D H : Set V) (ω : Set E) (x : V) : Set V :=
  G.cluster ((ω∩G.inducedEdges D)∩G.inducedEdges Hᶜ) x

def openLayerExits (D H : Set V) (ω : Set E) (x : V) : Set E :=
  G.freshClusterBoundary (G.inducedEdges Hᶜ) x (ω∩G.inducedEdges D)∩(ω∩G.inducedEdges D)

lemma openLayerExit_endpoints {D H : Set V} {ω : Set E} {x : V} (hx : x∉H)
    {e : E} (he : e∈G.openLayerExits D H ω x) :
    ∃ u v, G.ends e=s(u,v) ∧ u∈H ∧ v∉H ∧ v∈G.layerComponent D H ω x ∧ e∈ω ∧
      e∈G.inducedEdges D := by
  obtain ⟨⟨⟨u,v,heuv,hu,hv⟩,heH⟩,heω,heD⟩ := he
  have hvH := G.cluster_induced_subset (ω∩G.inducedEdges D) Hᶜ hx hv
  refine ⟨u,v,heuv,?_,hvH,hv,heω,heD⟩
  by_contra huH
  apply heH
  intro z hz
  rw [heuv] at hz
  rcases Sym2.mem_iff.mp hz with rfl|rfl
  · exact huH
  · exact hvH

lemma openLayerExit_child {D H : Set V} (hHD : H⊆D) {o x : V} {ω : Set E}
    (hx : x∈G.entrySeeds D o ω) (hxH : x∉H) {e : E}
    (he : e∈G.openLayerExits D H ω x) :
    e∈G.incidentEdges (G.entrySeeds H o ω) := by
  obtain ⟨u,v,heuv,huH,hvH,hv,heω,heD⟩ := G.openLayerExit_endpoints hxH he
  have hprevious : x∈G.cluster (ω∩(G.inducedEdges H)ᶜ) o := by
    apply G.cluster_mono _ o hx.1
    intro f hf
    exact ⟨hf.1,fun hh => hf.2 (G.inducedEdges_monotone hHD hh)⟩
  have hmiddle : v∈G.cluster (ω∩(G.inducedEdges H)ᶜ) x := by
    apply G.cluster_mono _ x hv
    intro f hf
    refine ⟨hf.1.1,?_⟩
    intro hh
    obtain ⟨a,b,hab⟩ : ∃ a b, G.ends f=s(a,b) := Sym2.exists.mp ⟨G.ends f,rfl⟩
    have ha : a∈G.ends f := by rw [hab]; simp
    exact hf.2 a ha (hh a ha)
  have hneq : v≠u := by intro hh; subst v; exact hvH huH
  have hedge : (G.openGraph (ω∩(G.inducedEdges H)ᶜ)).Adj v u := by
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨⟨e,⟨heω,?_⟩,?_⟩,hneq⟩
    · intro hh
      exact hvH (hh v (by rw [heuv]; simp))
    · rw [heuv,Sym2.eq_swap]
  exact ⟨u,⟨hprevious.trans (hmiddle.trans hedge.reachable),huH⟩,by rw [heuv]; simp⟩

lemma openLayerExit_common_component {D H : Set V} {ω : Set E} {x y : V}
    (hx : x∉H) (hy : y∉H) {e : E}
    (hex : e∈G.openLayerExits D H ω x) (hey : e∈G.openLayerExits D H ω y) :
    y∈G.layerComponent D H ω x := by
  obtain ⟨u,v,heuv,huH,hvH,hv,_,_⟩ := G.openLayerExit_endpoints hx hex
  obtain ⟨a,b,heab,haH,hbH,hb,_,_⟩ := G.openLayerExit_endpoints hy hey
  have hevb : v=b := by
    have heq : s(u,v)=s(a,b) := heuv.symm.trans heab
    rcases Sym2.eq_iff.mp heq with hh|hh
    · exact hh.2
    · exact False.elim (hvH (hh.2 ▸ haH))
  subst b
  exact hv.trans hb.symm

lemma comparable_parents_card_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) (C : Set V) (A : Finset V) (hAC : (A : Set V)⊆C)
    (a T : ℝ) (ha : 0<a) (hT : 0<T)
    (hband : ∀ y∈A, a*T≤G.modularRatio y o)
    (hx : G.modularRatio x o≤T) (M K : ℕ) (hMK : (M:ℝ)≤a*K)
    (hm : G.modularMass x C≤M) : A.card≤K := by
  have hlow := G.finset_weight_lower o C A hAC (ENNReal.ofReal (a*T))
    (fun y hy => ENNReal.ofReal_le_ofReal (hband y hy))
  have hmass : G.modularMass o C≤ENNReal.ofReal T*M := by
    rw [G.modularMass_change_base hc hl o x C]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hx) hm
  have hh := hlow.trans hmass
  have hh' : a*T*(A.card:ℝ)≤T*M := by
    rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (mul_pos ha hT).le,
      ←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul hT.le] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ)≤T*M)).mp hh
  apply Nat.cast_le.mp (show (A.card:ℝ)≤K from ?_)
  have hc' : a*(A.card:ℝ)≤M := (mul_le_mul_iff_right₀ hT).mp (by
    calc
      T*(a*(A.card:ℝ))=a*T*(A.card:ℝ) := by ring
      _ ≤ T*M := hh')
  exact (mul_le_mul_iff_right₀ ha).mp (hc'.trans hMK)

lemma finite_relation_count {α β : Type*} (A : Finset α) (B : Finset β)
    (r : α → β → Prop) (N K : ℕ)
    (hN : ∀ x∈A, N≤(B.filter (r x)).card)
    (hK : ∀ y∈B, (A.filter (fun x => r x y)).card≤K) :
    N*A.card≤K*B.card := by
  calc
    N*A.card = ∑ _x∈A, N := by simp [Nat.mul_comm]
    _ ≤ ∑ x∈A, (B.filter (r x)).card := Finset.sum_le_sum hN
    _ = ∑ y∈B, (A.filter (fun x => r x y)).card := by
      simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
      exact Finset.sum_comm
    _ ≤ ∑ _y∈B, K := Finset.sum_le_sum hK
    _ = K*B.card := by simp [Nat.mul_comm]

lemma layer_exit_fiber_card (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D H : Set V) (ω : Set E) (o : V) (A : Finset V)
    (a T : ℝ) (ha : 0<a) (hT : 0<T) (M N K : ℕ) (hMK : (M:ℝ)≤a*K)
    (hA : ∀ x∈A, x∉H ∧ a*T≤G.modularRatio x o ∧ G.modularRatio x o≤T ∧
      ω∈G.boundedDomainFreshExitEvent D Hᶜ x N M) (e : E) :
    (A.filter (fun x => e∈G.openLayerExits D H ω x)).card≤K := by
  let F := A.filter (fun x => e∈G.openLayerExits D H ω x)
  by_cases hF : F.Nonempty
  · obtain ⟨x,hx⟩ := hF
    have hxA := (Finset.mem_filter.mp hx).1
    apply G.comparable_parents_card_le hc hl o x (G.layerComponent D H ω x) F _
      a T ha hT _ (hA x hxA).2.2.1 M K hMK (hA x hxA).2.2.2.2
    · intro y hy
      exact G.openLayerExit_common_component (hA x hxA).1
        (hA y (Finset.mem_filter.mp hy).1).1 (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    · intro y hy
      exact (hA y (Finset.mem_filter.mp hy).1).2.1
  · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card≤K
    rw [he,Finset.card_empty]
    exact Nat.zero_le K

lemma layer_seed_counting (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D H : Set V) (hHD : H⊆D) (ω : Set E) (o : V) (A : Finset V)
    (a T : ℝ) (ha : 0<a) (hT : 0<T) (M N K d : ℕ) (hMK : (M:ℝ)≤a*K)
    (hd : ∀ v, (G.incidentEdges {v}).ncard≤d)
    (hfinite : (G.entrySeeds H o ω).Finite)
    (hA : ∀ x∈A, x∈G.entrySeeds D o ω ∧ x∉H ∧ a*T≤G.modularRatio x o ∧
      G.modularRatio x o≤T ∧ ω∈G.boundedDomainFreshExitEvent D Hᶜ x N M) :
    N*A.card≤K*d*(G.entrySeeds H o ω).ncard := by
  let F := (G.finite_incident hl hfinite).toFinset
  have hN : ∀ x∈A, N≤(F.filter (fun e => e∈G.openLayerExits D H ω x)).card := by
    intro x hx
    obtain ⟨B,hB,hBx⟩ := (hA x hx).2.2.2.2.1
    apply hB.trans (Finset.card_le_card _)
    intro e he
    apply Finset.mem_filter.mpr
    have hh : e∈G.openLayerExits D H ω x := hBx he
    exact ⟨(G.finite_incident hl hfinite).mem_toFinset.mpr
      (G.openLayerExit_child hHD (hA x hx).1 (hA x hx).2.1 hh),hh⟩
  have hK : ∀ e∈F, (A.filter (fun x => e∈G.openLayerExits D H ω x)).card≤K :=
    fun e _ => G.layer_exit_fiber_card hc hl D H ω o A a T ha hT M N K hMK
      (fun x hx => (hA x hx).2) e
  have hcount := finite_relation_count A F (fun x e => e∈G.openLayerExits D H ω x) N K hN hK
  have hF : F.card≤(G.entrySeeds H o ω).ncard*d := by
    rw [←Set.ncard_eq_toFinset_card _ (G.finite_incident hl hfinite)]
    exact G.incident_ncard_le _ hfinite d (fun v _ => hd v)
  calc
    N*A.card ≤ K*F.card := hcount
    _ ≤ K*((G.entrySeeds H o ω).ncard*d) := Nat.mul_le_mul_left K hF
    _ = K*d*(G.entrySeeds H o ω).ncard := by ring

end CriticalPercolation.BondGraph
end
end

end OAI
