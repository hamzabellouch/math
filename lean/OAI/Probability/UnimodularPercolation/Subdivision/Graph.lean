import Mathlib
import OAI.Probability.UnimodularPercolation.Clusters.LargeContacts

namespace OAI

/-! Subdivision of indexed bond graphs and its basic geometry. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory

abbrev SubdivisionEdge (G : BondGraph V E) := {ev : E × V // ev.2 ∈ G ev.1}

def subdivision (G : BondGraph V E) : BondGraph (V ⊕ E) (SubdivisionEdge G) :=
  fun ev => s(Sum.inl ev.val.2, Sum.inr ev.val.1)

theorem subdivision_injective (G : BondGraph V E) : Function.Injective (subdivision G) := by
  intro ⟨⟨e,x⟩,hx⟩ ⟨⟨f,y⟩,hy⟩ h
  simp only [subdivision,Sym2.eq_iff] at h
  rcases h with ⟨hxy,hef⟩ | ⟨hbad,_⟩
  · have h₁ : x = y := Sum.inl.inj hxy
    have h₂ : e = f := Sum.inr.inj hef
    subst y; subst f; rfl
  · cases hbad

@[simp] theorem subdivision_adj_inl_inr (G : BondGraph V E) (x : V) (e : E) :
    Adj (subdivision G) (.inl x) (.inr e) ↔ x ∈ G e := by
  constructor
  · rintro ⟨⟨⟨f,y⟩,hy⟩,h⟩
    simp only [subdivision,Sym2.eq_iff] at h
    rcases h with ⟨hyx,hfe⟩ | ⟨hbad,_⟩
    · have : y = x := Sum.inl.inj hyx
      have : f = e := Sum.inr.inj hfe
      subst y; subst f; exact hy
    · cases hbad
  · intro hx
    exact ⟨⟨(e,x),hx⟩,rfl⟩

@[simp] theorem subdivision_adj_inl_inl (G : BondGraph V E) (x y : V) :
    ¬ Adj (subdivision G) (.inl x) (.inl y) := by
  rintro ⟨⟨⟨e,z⟩,hz⟩,h⟩
  simp [subdivision] at h

@[simp] theorem subdivision_adj_inr_inr (G : BondGraph V E) (e f : E) :
    ¬ Adj (subdivision G) (.inr e) (.inr f) := by
  rintro ⟨⟨⟨d,z⟩,hz⟩,h⟩
  simp [subdivision] at h

@[simp] theorem subdivision_adj_inr_inl (G : BondGraph V E) (e : E) (x : V) :
    Adj (subdivision G) (.inr e) (.inl x) ↔ x ∈ G e := by
  exact ⟨fun h => (subdivision_adj_inl_inr G x e).mp (adj_symm _ h),
    fun h => adj_symm _ ((subdivision_adj_inl_inr G x e).mpr h)⟩

theorem subdivision_loopless (G : BondGraph V E) (x : V ⊕ E) :
    ¬ Adj (subdivision G) x x := by cases x <;> simp

theorem subdivision_locallyFinite (G : BondGraph V E) (hloc : LocallyFinite G) :
    LocallyFinite (subdivision G) := by
  classical
  intro z
  cases z with
  | inl x =>
    apply Set.Finite.of_finite_image (f := fun e : SubdivisionEdge G => e.val.1)
    · apply (hloc x).subset
      rintro e ⟨⟨⟨f,y⟩,hy⟩,hz,rfl⟩
      have he : x = y := by simpa [subdivision] using hz
      simpa [he] using hy
    · intro e he f hf hef
      apply Subtype.ext
      apply Prod.ext hef
      have hx : x = e.val.2 := by simpa [subdivision] using he
      have hy : x = f.val.2 := by simpa [subdivision] using hf
      exact hx.symm.trans hy
  | inr e =>
    apply Set.Finite.of_finite_image (f := fun f : SubdivisionEdge G => f.val.2)
    · apply (Sym2.toFinset (G e)).finite_toSet.subset
      rintro x ⟨⟨⟨f,y⟩,hy⟩,hz,rfl⟩
      have he : e = f := by simpa [subdivision] using hz
      simpa [he] using hy
    · intro f hf g hg hfg
      apply Subtype.ext
      apply Prod.ext _ hfg
      have h₁ : e = f.val.1 := by simpa [subdivision] using hf
      have h₂ : e = g.val.1 := by simpa [subdivision] using hg
      exact h₁.symm.trans h₂

theorem subdivision_connected (G : BondGraph V E) (hconn : Connected G) :
    Connected (subdivision G) := by
  have hold (x y : V) : Relation.ReflTransGen (Adj (subdivision G)) (.inl x) (.inl y) := by
    induction hconn x y with
    | refl => exact .refl
    | @tail y z hxy hyz ih =>
      obtain ⟨e,he⟩ := hyz
      exact (ih.tail ((subdivision_adj_inl_inr G y e).mpr (by simp [he]))).tail
        ((subdivision_adj_inr_inl G e z).mpr (by simp [he]))
  have attach (z : V ⊕ E) : ∃ x : V, Relation.ReflTransGen (Adj (subdivision G)) z (.inl x) := by
    cases z with
    | inl x => exact ⟨x,.refl⟩
    | inr e =>
      exact ⟨(G e).out.1,Relation.ReflTransGen.single
        ((subdivision_adj_inr_inl G e _).mpr (G e).out_fst_mem)⟩
  have rev {a b : V ⊕ E} (h : Relation.ReflTransGen (Adj (subdivision G)) a b) :
      Relation.ReflTransGen (Adj (subdivision G)) b a := by
    induction h with
    | refl => exact .refl
    | tail _ hab ih => exact (Relation.ReflTransGen.single (adj_symm _ hab)).trans ih
  intro z w
  obtain ⟨x,hx⟩ := attach z
  obtain ⟨y,hy⟩ := attach w
  exact hx.trans ((hold x y).trans (rev hy))

 
theorem incidence_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (e : E) (x : V) : a x ∈ G (b e) ↔ x ∈ G e := by
  rw [hab e]
  simp only [Sym2.mem_map,a.injective.eq_iff,exists_eq_right]

 
noncomputable def subdivisionAutEdges (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) : SubdivisionEdge G ≃ SubdivisionEdge G :=
  (b.prodCongr a).subtypeEquiv (fun p => (incidence_aut_iff G hab p.1 p.2).symm)

theorem subdivision_isAut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) :
    IsAut (subdivision G) (a.sumCongr b) (subdivisionAutEdges G hab) := by
  intro e
  rfl

 

theorem finite_edge_roots (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) :
    ∃ R : Finset E, ∀ e, ∃ f ∈ R, ∃ a : V ≃ V, ∃ b : E ≃ E,
      IsAut G a b ∧ b f = e := by
  classical
  obtain ⟨S,hS⟩ := hqt
  let R := S.biUnion (fun x => (hloc x).toFinset)
  refine ⟨R,fun e => ?_⟩
  obtain ⟨x,hx,a,b,hab,hax⟩ := hS (G e).out.1
  refine ⟨b.symm e,Finset.mem_biUnion.mpr ⟨x,hx,?_⟩,a,b,hab,b.apply_symm_apply e⟩
  apply (hloc x).mem_toFinset.mpr
  apply (incidence_aut_iff G hab _ _).mp
  simpa only [Equiv.apply_symm_apply,hax] using (G e).out_fst_mem

theorem subdivision_quasiTransitive (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) : QuasiTransitive (subdivision G) := by
  classical
  obtain ⟨S,hS⟩ := hqt
  obtain ⟨R,hR⟩ := finite_edge_roots G hloc ⟨S,hS⟩
  refine ⟨S.image Sum.inl ∪ R.image Sum.inr,?_⟩
  intro z
  cases z with
  | inl x =>
    obtain ⟨o,ho,a,b,hab,hax⟩ := hS x
    refine ⟨.inl o,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨o,ho,rfl⟩),
      a.sumCongr b,subdivisionAutEdges G hab,subdivision_isAut G hab,?_⟩
    exact congrArg Sum.inl hax
  | inr e =>
    obtain ⟨f,hf,a,b,hab,hbe⟩ := hR e
    refine ⟨.inr f,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f,hf,rfl⟩),
      a.sumCongr b,subdivisionAutEdges G hab,subdivision_isAut G hab,?_⟩
    exact congrArg Sum.inr hbe

 

theorem subdivision_old_boundary_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset (V ⊕ E)) :
    hV G * (A.toLeft.card : ℝ) ≤
      2 * ((vertexBoundary (subdivision G) A).ncard : ℝ) := by
  classical
  let B := (finite_vertexBoundary (subdivision G) (subdivision_locallyFinite G hloc) A).toFinset
  let C := (finite_vertexBoundary G hloc A.toLeft).toFinset
  have hsub : C ⊆ B.toLeft ∪ B.toRight.biUnion (fun e => (G e).toFinset) := by
    intro y hy
    obtain ⟨hy,x,hx,e,he⟩ := (finite_vertexBoundary G hloc A.toLeft).mem_toFinset.mp hy
    by_cases heA : Sum.inr e ∈ A
    · apply Finset.mem_union_left
      apply Finset.mem_toLeft.mpr
      apply (finite_vertexBoundary (subdivision G) (subdivision_locallyFinite G hloc) A).mem_toFinset.mpr
      exact ⟨fun h => hy (Finset.mem_toLeft.mpr h),.inr e,heA,
        (subdivision_adj_inr_inl G e y).mpr (by simp [he])⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨e,?_,Sym2.mem_toFinset.mpr (by simp [he])⟩
      apply Finset.mem_toRight.mpr
      apply (finite_vertexBoundary (subdivision G) (subdivision_locallyFinite G hloc) A).mem_toFinset.mpr
      exact ⟨heA,.inl x,Finset.mem_toLeft.mp hx,
        (subdivision_adj_inl_inr G x e).mpr (by simp [he])⟩
  have hcard : C.card ≤ B.toLeft.card + 2*B.toRight.card := by
    calc
      C.card ≤ (B.toLeft ∪ B.toRight.biUnion (fun e => (G e).toFinset)).card := Finset.card_le_card hsub
      _ ≤ B.toLeft.card + (B.toRight.biUnion (fun e => (G e).toFinset)).card := Finset.card_union_le _ _
      _ ≤ B.toLeft.card + ∑ e ∈ B.toRight, (G e).toFinset.card :=
        Nat.add_le_add_left (Finset.card_biUnion_le) _
      _ ≤ B.toLeft.card + ∑ _e ∈ B.toRight, 2 := by
        apply Nat.add_le_add_left
        apply Finset.sum_le_sum
        intro e _
        rw [Sym2.card_toFinset]
        split_ifs <;> omega
      _ = _ := by simp [Nat.mul_comm]
  have hcard' : C.card ≤ 2*B.card := by
    have hsum := B.card_toLeft_add_card_toRight
    omega
  have hh := hV_mul_card_le G A.toLeft
  have hc : C.card = (vertexBoundary G A.toLeft).ncard := (Set.ncard_eq_toFinset_card _ _).symm
  have hb : B.card = (vertexBoundary (subdivision G) A).ncard := (Set.ncard_eq_toFinset_card _ _).symm
  rw [←hc] at hh
  exact hh.trans (by exact_mod_cast (hcard'.trans_eq (by rw [hb])))

 

theorem subdivision_new_card_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (A : Finset (V ⊕ E)) :
    A.toRight.card ≤ d*(A.toLeft.card + (vertexBoundary (subdivision G) A).ncard) := by
  classical
  let B := (finite_vertexBoundary (subdivision G) (subdivision_locallyFinite G hloc) A).toFinset
  let C := A.toLeft ∪ B.toLeft
  have hsub : A.toRight ⊆ C.biUnion (fun x => (hloc x).toFinset) := by
    intro e he
    let x := (G e).out.1
    have hx : x ∈ G e := (G e).out_fst_mem
    refine Finset.mem_biUnion.mpr ⟨x,?_,(hloc x).mem_toFinset.mpr hx⟩
    by_cases hxA : x ∈ A.toLeft
    · exact Finset.mem_union_left _ hxA
    · apply Finset.mem_union_right
      apply Finset.mem_toLeft.mpr
      apply (finite_vertexBoundary (subdivision G) (subdivision_locallyFinite G hloc) A).mem_toFinset.mpr
      exact ⟨fun h => hxA (Finset.mem_toLeft.mpr h),.inr e,Finset.mem_toRight.mp he,
        (subdivision_adj_inr_inl G e x).mpr hx⟩
  have hc : C.card ≤ A.toLeft.card+B.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left B.card_toLeft_le _)
  have hb : B.card = (vertexBoundary (subdivision G) A).ncard := (Set.ncard_eq_toFinset_card _ _).symm
  calc
    A.toRight.card ≤ (C.biUnion (fun x => (hloc x).toFinset)).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ C, (hloc x).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ C, d := by
      apply Finset.sum_le_sum
      intro x _
      rw [←Set.ncard_eq_toFinset_card _ (hloc x)]
      exact (incident_ncard_le_degree G hloc x).trans (hd x)
    _ = d*C.card := by simp [Nat.mul_comm]
    _ ≤ d*(A.toLeft.card+B.card) := Nat.mul_le_mul_left d hc
    _ = _ := by rw [hb]

 

theorem subdivision_hV_pos [Nonempty V] (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) : 0 < hV (subdivision G) := by
  classical
  obtain ⟨d,hd,hdg⟩ := exists_degree_bound G hqt
  let c := hV G / (2*((d:ℝ)+1)+(d:ℝ)*hV G)
  have hden : 0 < 2*((d:ℝ)+1)+(d:ℝ)*hV G := by positivity
  have hc : 0 < c := div_pos hh hden
  apply hc.trans_le
  apply le_csInf
  · exact ⟨_,{Sum.inl (Classical.arbitrary V)},Finset.singleton_nonempty _,rfl⟩
  · rintro r ⟨A,hA,rfl⟩
    have ho := subdivision_old_boundary_bound G hloc A
    have hn : (A.toRight.card:ℝ) ≤ (d:ℝ)*((A.toLeft.card:ℝ)+
        ((vertexBoundary (subdivision G) A).ncard:ℝ)) := by
      exact_mod_cast subdivision_new_card_bound G hloc d hdg A
    have hs : (A.toLeft.card:ℝ)+(A.toRight.card:ℝ) = A.card := by
      exact_mod_cast A.card_toLeft_add_card_toRight
    have hcard : (0:ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
    apply (le_div_iff₀ hcard).mpr
    dsimp only [c]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    have h₁ := mul_le_mul_of_nonneg_left ho (show 0 ≤ (d:ℝ)+1 by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hn hh.le
    rw [←hs]
    nlinarith only [h₁,h₂]

end Percolation

end OAI
