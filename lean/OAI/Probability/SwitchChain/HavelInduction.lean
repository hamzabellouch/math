import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.HavelCanonical

theorem exists_top_subset {V : Type*} [DecidableEq V]
    (R : Finset V) (weight : V → Nat) (k : Nat) (hk : k ≤ R.card) :
    ∃ T : Finset V, T ⊆ R ∧ T.card = k ∧
      ∀ i ∈ R, i ∉ T → ∀ j ∈ T, weight i ≤ weight j := by
  classical
  obtain ⟨T₀, hT₀R, hT₀k⟩ := Finset.exists_subset_card_eq hk
  have hne : (R.powersetCard k).Nonempty :=
    ⟨T₀, Finset.mem_powersetCard.mpr ⟨hT₀R, hT₀k⟩⟩
  obtain ⟨T, hT, hmax⟩ :=
    Finset.exists_max_image (R.powersetCard k) (fun S => ∑ x ∈ S, weight x) hne
  obtain ⟨hTR, hTk⟩ := Finset.mem_powersetCard.mp hT
  refine ⟨T, hTR, hTk, ?_⟩
  intro i hiR hiT j hjT
  let U := insert i (T.erase j)
  have hiE : i ∉ T.erase j := fun h => hiT (Finset.mem_of_mem_erase h)
  have hUR : U ⊆ R := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · simpa [h] using hiR
    · exact hTR (Finset.mem_of_mem_erase h)
  have hUk : U.card = k := by
    simp only [U, Finset.card_insert_of_notMem hiE, Finset.card_erase_of_mem hjT]
    have hjpos : 0 < T.card := Finset.card_pos.mpr ⟨j, hjT⟩
    omega
  have hbound := hmax U (Finset.mem_powersetCard.mpr ⟨hUR, hUk⟩)
  have hsum : (∑ x ∈ T.erase j, weight x) + weight j = ∑ x ∈ T, weight x :=
    Finset.sum_erase_add T weight hjT
  simp only [U, Finset.sum_insert hiE] at hbound
  omega

def AgreeOutside {V : Type*} (R : Finset V) (G H : SimpleGraph V) : Prop :=
  ∀ v, v ∉ R → ∀ w, G.Adj v w ↔ H.Adj v w

theorem residual_degree_eq {V : Type*} [Fintype V] [DecidableEq V]
    (R : Finset V) (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hout : AgreeOutside R G H) (hdegree : ∀ v, G.degree v = H.degree v) (v : V) :
    (R.filter (G.Adj v)).card = (R.filter (H.Adj v)).card := by
  classical
  have hin (K : SimpleGraph V) [DecidableRel K.Adj] :
      (K.neighborFinset v).filter (fun w => w ∈ R) = R.filter (K.Adj v) := by
    ext w
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact and_comm
  have hext : (G.neighborFinset v).filter (fun w => w ∉ R) =
      (H.neighborFinset v).filter (fun w => w ∉ R) := by
    ext w
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hvw, hwR⟩
      exact ⟨((hout w hwR v).mp hvw.symm).symm, hwR⟩
    · rintro ⟨hvw, hwR⟩
      exact ⟨((hout w hwR v).mpr hvw.symm).symm, hwR⟩
  have hG := (G.neighborFinset v).card_filter_add_card_filter_not (fun w => w ∈ R)
  have hH := (H.neighborFinset v).card_filter_add_card_filter_not (fun w => w ∈ R)
  rw [hin G, hext, SimpleGraph.card_neighborFinset_eq_degree] at hG
  rw [hin H, SimpleGraph.card_neighborFinset_eq_degree] at hH
  have hd := hdegree v
  omega

theorem agreeOutside_erase {V : Type*} [DecidableEq V]
    {R : Finset V} {G H : SimpleGraph V} {v : V}
    (hout : AgreeOutside R G H) (hrow : ∀ w, G.Adj v w ↔ H.Adj v w) :
    AgreeOutside (R.erase v) G H := by
  intro u hu w
  by_cases huv : u = v
  · simpa [huv] using hrow w
  · exact hout u (fun huR => hu (Finset.mem_erase.mpr ⟨huv, huR⟩)) w

theorem connected_of_row_alignment
    {V X : Type*} [Fintype V] [DecidableEq V]
    (graph : X → SimpleGraph V) (hinj : Function.Injective graph)
    (r : X → X → Prop) (hsymm : ∀ ⦃first second⦄, r first second → r second first)
    (halign : ∀ (R : Finset V) (v : V), v ∈ R → ∀ x y : X,
      AgreeOutside R (graph x) (graph y) →
      ∃ x' y' : X,
        Relation.ReflTransGen r x x' ∧ Relation.ReflTransGen r y y' ∧
        AgreeOutside R (graph x') (graph y') ∧
        ∀ w, (graph x').Adj v w ↔ (graph y').Adj v w)
    (x y : X) : Relation.ReflTransGen r x y := by
  classical
  have hreverse {a b : X} (h : Relation.ReflTransGen r a b) :
      Relation.ReflTransGen r b a := by
    induction h with
    | refl => exact .refl
    | tail hab hbc ih => exact (Relation.ReflTransGen.single (hsymm hbc)).trans ih
  have haux : ∀ R : Finset V, ∀ a b : X,
      AgreeOutside R (graph a) (graph b) → Relation.ReflTransGen r a b := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
      intro a b hab
      have hgraphs : graph a = graph b := by
        apply SimpleGraph.ext
        funext v w
        exact propext (hab v (by simp) w)
      have heq := hinj hgraphs
      subst b
      exact .refl
    | @insert v R hv ih =>
      intro a b hab
      obtain ⟨a', b', haa', hbb', hout, hrow⟩ :=
        halign (insert v R) v (Finset.mem_insert_self v R) a b hab
      have hout' : AgreeOutside R (graph a') (graph b') := by
        simpa [Finset.erase_insert hv] using agreeOutside_erase hout hrow
      exact haa'.trans ((ih a' b' hout').trans (hreverse hbb'))
  exact haux Finset.univ x y (by intro v hv; exact False.elim (hv (Finset.mem_univ v)))

theorem connected_of_neighborhood_repair
    {V X : Type*} [Fintype V] [DecidableEq V]
    (graph : X → SimpleGraph V) [∀ x, DecidableRel (graph x).Adj]
    (hinj : Function.Injective graph) (r : X → X → Prop)
    (hsymm : ∀ ⦃first second⦄, r first second → r second first)
    (hdegree : ∀ x y v, (graph x).degree v = (graph y).degree v)
    (hrepair : ∀ (R T : Finset V) (v : V) (x : X),
      v ∈ R → T ⊆ R.erase v → T.card = (R.filter ((graph x).Adj v)).card →
      (∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
        (R.filter ((graph x).Adj i)).card ≤ (R.filter ((graph x).Adj j)).card) →
      ∃ x' : X, Relation.ReflTransGen r x x' ∧
        AgreeOutside R (graph x) (graph x') ∧ R.filter ((graph x').Adj v) = T)
    (x y : X) : Relation.ReflTransGen r x y := by
  classical
  apply connected_of_row_alignment graph hinj r hsymm _ x y
  intro R v hv a b hab
  have hcard : (R.filter ((graph a).Adj v)).card ≤ (R.erase v).card := by
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hwR, hvw⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_erase.mpr ⟨hvw.ne.symm, hwR⟩
  obtain ⟨T, hTR, hTcard, htop⟩ := exists_top_subset (R.erase v)
    (fun w => (R.filter ((graph a).Adj w)).card)
    (R.filter ((graph a).Adj v)).card hcard
  have hsortedA : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter ((graph a).Adj i)).card ≤ (R.filter ((graph a).Adj j)).card := by
    intro i hiR hiv hiT j hjT
    exact htop i (Finset.mem_erase.mpr ⟨hiv, hiR⟩) hiT j hjT
  have hres : ∀ w, (R.filter ((graph a).Adj w)).card =
      (R.filter ((graph b).Adj w)).card :=
    residual_degree_eq R (graph a) (graph b) hab (hdegree a b)
  have hsizeB : T.card = (R.filter ((graph b).Adj v)).card :=
    hTcard.trans (hres v)
  have hsortedB : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter ((graph b).Adj i)).card ≤ (R.filter ((graph b).Adj j)).card := by
    intro i hiR hiv hiT j hjT
    rw [← hres i, ← hres j]
    exact hsortedA i hiR hiv hiT j hjT
  obtain ⟨a', haa', houtA, hrowA⟩ := hrepair R T v a hv hTR hTcard hsortedA
  obtain ⟨b', hbb', houtB, hrowB⟩ := hrepair R T v b hv hTR hsizeB hsortedB
  have hout' : AgreeOutside R (graph a') (graph b') := by
    intro u hu w
    exact (houtA u hu w).symm.trans ((hab u hu w).trans (houtB u hu w))
  refine ⟨a', b', haa', hbb', hout', ?_⟩
  intro w
  by_cases hw : w ∈ R
  · have h := Finset.ext_iff.mp (hrowA.trans hrowB.symm) w
    simpa only [Finset.mem_filter, hw, true_and] using h
  · constructor
    · intro h
      exact ((hout' w hw v).mp h.symm).symm
    · intro h
      exact ((hout' w hw v).mpr h.symm).symm

end Problem315.HavelCanonical

end

end OAI
