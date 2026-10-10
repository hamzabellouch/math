import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalEndpointGeometry
import OAI.Combinatorics.Ramsey.CycleClique.Construction.StartingIncident
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OrientedSingleton
import OAI.Combinatorics.Ramsey.CycleClique.Construction.MissingCoverage
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalClassification

namespace OAI

/-! The actual three terminal configurations, including restrictions on
both targets of every short path between starting representatives. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

theorem IsOptimal.terminal_starting_classification {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    (U : RawPathSystem G Q) (hUa : U.amount = S.amount)
    (hUe : U.assignedCount = S.assignedCount) (hUi : U.normalize.incident = S.incident)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    {P M R : List (List V)} {B D : List V} {x y : V}
    (hsys : U.chains = P ++ (x :: B) :: M ++ (y :: D) :: R)
    (hBx : B = [] ↔ x ∉ S.vertices) (hDy : D = [] ↔ y ∉ S.vertices)
    (hne : x ≠ y) (h : OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d) :
    S.amount = k - Q.card ∧
      (∃ original, SystemAssignedAmounts Q U.chains original ∧ ∀ b ∈ original, d ≤ b) ∧
      ((d = 2 ∧ Q.card ≤ S.incident + 2 ∧ Q \ S.vertices ⊆ {x, y}) ∨
       (d = 3 ∧ (Q.card = 9 ∨ Q.card = 11) ∧
         2 * S.assignedCount = Q.card - 3 ∧ S.incident = Q.card - 3 ∧
         (∀ l ∈ S.chains, chainCliqueCount Q l = 2) ∧ x ∉ S.vertices ∧ y ∉ S.vertices) ∨
       (d = 5 ∧ Q.card = 9 ∧ k = 19 ∧ S.assignedCount = 2 ∧ S.incident = 4 ∧
         (∀ l ∈ S.chains, chainCliqueCount Q l = 2) ∧ x ∉ S.vertices ∧ y ∉ S.vertices)) := by
  classical
  obtain ⟨hL, _, _, hde⟩ := hopt.terminal_different_chain_starts ht hQk hkQ hQ hcycle hd hd'
    U hUa hUe hUvertices (A := []) (C := []) (by simpa using hsys) (by simp) (by simp) h
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := h.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hpos : J ≠ [] := by intro he; simp only [he, List.length_nil] at hJlen; omega
  have hdis : J.Disjoint U.chains.flatten := by
    apply List.disjoint_left.mpr
    intro z hz hzU
    exact hJout z hz (hUvertices z (List.mem_toFinset.mpr hzU))
  obtain ⟨T, original, output, kept, removed, hT, hTa, ho, hout, hp, hq⟩ :=
    U.replace_different_chains_profiled (A := []) (C := [])
      (by simpa using hsys) (by simp) (by simp) hJ hJQ hpos hdis hpath
  obtain ⟨_, _, _, _, hweights⟩ := hopt.terminal_increment_profiles ht hQk hkQ hQ hcycle
    hd hd' U T hUa hUe ho hout hp hq (by omega)
  have hTchain : T.chains = P ++ [] :: M ++ [] ::
      (B.reverse ++ x :: (J ++ y :: D)) :: R := by simpa using hT
  have hTi := U.starting_replacement_incident T hsys hTchain hJQ hpos
  rw [hUi] at hTi
  have hTna : T.normalize.amount = S.amount + d := by
    rw [RawPathSystem.normalize_amount]
    omega
  have hd2 : 2 ≤ d := by
    by_contra hn
    have hd1 : d = 1 := by omega
    exact hopt.no_one_vertex_increase (by omega) hQk hQ hcycle T.normalize (by omega)
  have hinterval : k + 1 < T.normalize.amount + T.normalize.incident := by
    by_contra hn
    exact T.normalize.forbidden_interval (by omega) hQ hcycle (by omega) (by omega)
  have htarget : Q.card + 2 ≤ S.incident + d +
      (if B = [] then 1 else 0) + (if D = [] then 1 else 0) := by omega
  have htv : Q.card ≤ S.incident + d := by
    split_ifs at htarget <;> omega
  have hxQ : x ∈ Q := (U.endpoints _ (show x :: B ∈ U.chains by simp [hsys])).1 x (by simp)
  have hyQ : y ∈ Q := (U.endpoints _ (show y :: D ∈ U.chains by simp [hsys])).1 y (by simp)
  have hmissing : (Q \ S.vertices).card + S.incident = Q.card := by
    simpa only [incident, Finset.inter_comm] using Finset.card_sdiff_add_card_inter Q S.vertices
  have hBxM : B = [] ↔ x ∈ Q \ S.vertices := by
    simpa only [Finset.mem_sdiff, hxQ, true_and] using hBx
  have hDyM : D = [] ↔ y ∈ Q \ S.vertices := by
    simpa only [Finset.mem_sdiff, hyQ, true_and] using hDy
  have hboth (ha : 2 ≤ (if B = [] then 1 else 0) + (if D = [] then 1 else 0)) :
      x ∉ S.vertices ∧ y ∉ S.vertices := by
    have hBnil : B = [] := by by_contra hn; simp only [hn, ↓reduceIte] at ha; split_ifs at ha <;> omega
    have hDnil : D = [] := by by_contra hn; simp only [hn, ↓reduceIte] at ha; (split_ifs at ha; omega)
    exact ⟨hBx.mp hBnil, hDy.mp hDnil⟩
  refine ⟨hL, ⟨original, ho, hweights⟩, ?_⟩
  rcases terminal_classification_arithmetic ht hQk hkQ hL hd2 hd' hde htv
      S.incident_le_twice_assignedCount with htwo | hthree | hfive
  · obtain ⟨hd2, hv⟩ := htwo
    refine Or.inl ⟨hd2, hv, ?_⟩
    apply subset_pair_of_card_le_indicators _ hne
    simp only [← hBxM, ← hDyM]
    omega
  · obtain ⟨hd3, ht3, he3, hv3⟩ := hthree
    have hmiss := hboth (by omega)
    refine Or.inr (Or.inl ⟨hd3, ht3, he3, hv3, ?_, hmiss.1, hmiss.2⟩)
    exact S.matching_of_incident_eq_twice (by omega)
  · obtain ⟨hd5, ht5, hk5, he5, hv5⟩ := hfive
    have hmiss := hboth (by omega)
    refine Or.inr (Or.inr ⟨hd5, ht5, hk5, he5, hv5, ?_, hmiss.1, hmiss.2⟩)
    exact S.matching_of_incident_eq_twice (by omega)

end CycleClique.Construction.ExpandedPathSystem

end OAI
