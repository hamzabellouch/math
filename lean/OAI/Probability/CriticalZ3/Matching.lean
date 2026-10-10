import OAI.Probability.CriticalZ3.PlanarBoundary

namespace OAI

universe uAlpha uE uV

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

/-! Exact greedy constants used in the shell trials and contour estimate. -/
namespace GreedyPacking
open Classical

variable {α : Type uAlpha}

/-- Greedily deleting at most M conflicts loses at most M elements per choice. -/
theorem exists_packing (t : Finset α) (R : α → α → Prop)
    (hrefl : ∀ a ∈ t, R a a) (hsym : ∀ a ∈ t, ∀ b ∈ t, R a b → R b a)
    (M : ℕ) (hM : ∀ a ∈ t, (t.filter (R a)).card ≤ M) :
    ∃ s : Finset α, s ⊆ t ∧ (s : Set α).Pairwise (fun a b => ¬R a b) ∧ t.card ≤ M*s.card := by
  classical
  induction t using Finset.strongInduction with
  | H t ih =>
    by_cases ht : t = ∅
    · subst t
      exact ⟨∅,by simp,by simp,by simp⟩
    obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr ht
    let u := t.filter (fun b => ¬R a b)
    have hu : u ⊆ t := Finset.filter_subset _ _
    have hau : a ∉ u := by simp [u,hrefl a ha]
    have hut : u ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨hu,by intro h; exact hau (h.symm ▸ ha)⟩
    obtain ⟨s,hs,hpair,hcard⟩ := ih u hut
      (fun b hb => hrefl b (hu hb))
      (fun b hb c hc h => hsym b (hu hb) c (hu hc) h)
      (fun b hb => le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hu)) (hM b (hu hb)))
    refine ⟨insert a s,Finset.insert_subset ha (hs.trans hu),?_,?_⟩
    · simp only [Finset.coe_insert]
      rw [Set.pairwise_insert]
      refine ⟨hpair,?_⟩
      intro b hb _
      exact ⟨(Finset.mem_filter.mp (hs hb)).2,
        fun h => (Finset.mem_filter.mp (hs hb)).2 (hsym b (hu (hs hb)) a ha h)⟩
    · have has : a ∉ s := fun h => hau (hs h)
      rw [Finset.card_insert_of_notMem has]
      have he : (t.filter (R a)).card+u.card = t.card := by
        exact Finset.card_filter_add_card_filter_not (s := t) (R a)
      have hm := hM a ha
      nlinarith

/-- The prescribed K choices exist once there are K M candidates. -/
theorem exists_packing_card (t : Finset α) (R : α → α → Prop)
    (hrefl : ∀ a ∈ t, R a a) (hsym : ∀ a ∈ t, ∀ b ∈ t, R a b → R b a)
    (M K : ℕ) (hM0 : 0 < M) (hM : ∀ a ∈ t, (t.filter (R a)).card ≤ M)
    (ht : K*M ≤ t.card) :
    ∃ s : Finset α, s ⊆ t ∧ s.card = K ∧ (s : Set α).Pairwise (fun a b => ¬R a b) := by
  obtain ⟨s,hs,hpair,hcard⟩ := exists_packing t R hrefl hsym M hM
  have hk : K ≤ s.card := by nlinarith
  obtain ⟨u,hu,huc⟩ := Finset.exists_subset_card_eq hk
  exact ⟨u,hu.trans hs,huc,hpair.mono hu⟩

end GreedyPacking

namespace FiniteMatching
open Classical
variable {E : Type uE} {V : Type uV} [Fintype E]

noncomputable def incident (a b : E → V) (v : V) : Finset E :=
  Finset.univ.filter (fun e => a e = v ∨ b e = v)

def conflict (a b : E → V) (e f : E) : Prop :=
  a e = a f ∨ a e = b f ∨ b e = a f ∨ b e = b f

omit [Fintype E] in
theorem conflict_refl (a b : E → V) (e : E) : conflict a b e e := Or.inl rfl

omit [Fintype E] in
theorem conflict_symm (a b : E → V) {e f : E} : conflict a b e f → conflict a b f e := by
  unfold conflict
  aesop

theorem conflict_card (a b : E → V)
    (hdeg : ∀ v, (incident a b v).card ≤ 4) (e : E) :
    (Finset.univ.filter (conflict a b e)).card ≤ 7 := by
  have heq : Finset.univ.filter (conflict a b e) = incident a b (a e) ∪ incident a b (b e) := by
    ext f
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,incident,conflict,
      Finset.mem_filter,Finset.mem_univ,true_and]
    aesop
  rw [heq]
  have hi : e ∈ incident a b (a e) ∩ incident a b (b e) := by simp [incident]
  have hpos := Finset.card_pos.mpr ⟨e,hi⟩
  have he := Finset.card_union_add_card_inter (incident a b (a e)) (incident a b (b e))
  have ha := hdeg (a e)
  have hb := hdeg (b e)
  omega

theorem exists_matching (a b : E → V) (hdeg : ∀ v, (incident a b v).card ≤ 4) :
    ∃ s : Finset E, (s : Set E).Pairwise (fun e f => ¬conflict a b e f) ∧
      Fintype.card E ≤ 7*s.card := by
  obtain ⟨s,_,hp,hc⟩ := GreedyPacking.exists_packing Finset.univ (conflict a b)
    (fun e _ => conflict_refl a b e) (fun _ _ _ _ => conflict_symm a b)
    7 (fun e _ => conflict_card a b hdeg e)
  exact ⟨s,hp,by simpa only [Finset.card_univ] using hc⟩

/- Choosing either endpoint of each edge of a matching gives distinct vertices. -/
omit [Fintype E] in
theorem endpoint_injective (a b : E → V) (s : Finset E)
    (hp : (s : Set E).Pairwise (fun e f => ¬conflict a b e f)) (choice : s → Bool) :
    Function.Injective (fun e : s => if choice e then a e.val else b e.val) := by
  intro e f hef
  by_contra hne
  have hn : e.val ≠ f.val := fun h => hne (Subtype.ext h)
  have hc := hp e.property f.property hn
  cases he : choice e <;> cases hf : choice f <;> simp only [he,hf,Bool.false_eq_true,
    ite_false,ite_true] at hef
  · exact hc (Or.inr (Or.inr (Or.inr hef)))
  · exact hc (Or.inr (Or.inr (Or.inl hef)))
  · exact hc (Or.inr (Or.inl hef))
  · exact hc (Or.inl hef)

end FiniteMatching

namespace PlanarBoundary
open Classical

def primalInside {X : Finset Point} (e : Boundary X) : Point := e.val.1
def primalOutside {X : Finset Point} (e : Boundary X) : Point := e.val.1+outward e.val.2

/-- Boundary edges incident to a fixed primal vertex have at most four possibilities. -/
theorem boundary_degree (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // primalInside e = v ∨ primalOutside e = v} ≤ 4 := by
  let f : {e : Boundary X // primalInside e = v ∨ primalOutside e = v} → Direction :=
    fun e => e.val.val.2
  have hinj : Function.Injective f := by
    intro e g he
    have hd : e.val.val.2 = g.val.val.2 := he
    have hc : e.val.val.1 = g.val.val.1 := by
      by_cases hv : v ∈ X
      · have hve : primalInside e.val = v := e.property.resolve_right
          (by intro h; apply e.val.property.2; change primalOutside e.val ∈ X; rwa [h])
        have hvg : primalInside g.val = v := g.property.resolve_right
          (by intro h; apply g.val.property.2; change primalOutside g.val ∈ X; rwa [h])
        exact hve.trans hvg.symm
      · have hve : primalOutside e.val = v := e.property.resolve_left
          (fun h => hv (h ▸ e.val.property.1))
        have hvg : primalOutside g.val = v := g.property.resolve_left
          (fun h => hv (h ▸ g.val.property.1))
        have hh := hve.trans hvg.symm
        change e.val.val.1+outward e.val.val.2 = g.val.val.1+outward g.val.val.2 at hh
        rw [hd] at hh
        exact add_right_cancel hh
    exact Subtype.ext (Subtype.ext (Prod.ext hc hd))
  exact (Fintype.card_le_of_injective f hinj).trans_eq (Fintype.card_fin 4)

def Valid {n : ℕ} (c : Code n) : Prop :=
  ∃ X : Finset Point, ∃ e : Fin n → Boundary X, Function.Injective e ∧
    ∀ i, traceSide c i = (e i).val

def inner {n : ℕ} (c : Code n) (i : Fin n) : Point := (traceSide c i).1
def outer {n : ℕ} (c : Code n) (i : Fin n) : Point :=
  (traceSide c i).1+outward (traceSide c i).2

theorem code_degree {n : ℕ} (c : Code n) (hc : Valid c) (v : Point) :
    (FiniteMatching.incident (inner c) (outer c) v).card ≤ 4 := by
  obtain ⟨X,e,hinj,he⟩ := hc
  let f : {i : Fin n // inner c i = v ∨ outer c i = v} →
      {e : Boundary X // primalInside e = v ∨ primalOutside e = v} := fun i =>
    ⟨e i.val,by simpa only [primalInside,primalOutside,inner,outer,he] using i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact hinj (congrArg Subtype.val hij)
  have hh := (Fintype.card_le_of_injective f hf).trans (boundary_degree X v)
  have heq : (FiniteMatching.incident (inner c) (outer c) v).card =
      Fintype.card {i : Fin n // inner c i = v ∨ outer c i = v} := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext i
    simp only [FiniteMatching.incident, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [heq]
  exact hh

theorem exists_code_matching {n : ℕ} (c : Code n) (hc : Valid c) :
    ∃ s : Finset (Fin n),
      (s : Set (Fin n)).Pairwise (fun i j => ¬FiniteMatching.conflict (inner c) (outer c) i j) ∧
      n ≤ 7*s.card := by
  simpa only [Fintype.card_fin] using FiniteMatching.exists_matching _ _ (code_degree c hc)

end PlanarBoundary

end OAI
