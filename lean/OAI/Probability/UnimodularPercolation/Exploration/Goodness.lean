import Mathlib
import OAI.Probability.UnimodularPercolation.Exploration.Moments

namespace OAI

/-! Pruning, finite and infinite goodness events and uniform bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteCappedRadius
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def pairOpenPivotals (G : BondGraph V E) (Q : Finset E) (x y : V)
    (ω : Finset E) : Finset E :=
  Q.filter fun e => e ∈ ω ∧ Conn G (ω : Set E) x y ∧ ¬Conn G (ω.erase e : Set E) x y

 
def CappedRadiusEvent (G : BondGraph V E) (Q : Finset E) (x : V) (M r : ℕ)
    (ω : Finset E) : Prop :=
  (finiteRootComponent G ω x).card ≤ M ∧
    ∃ y, Conn G (ω : Set E) x y ∧ r ≤ (pairOpenPivotals G Q x y ω).card

noncomputable def finiteCappedRadiusTail (G : BondGraph V E) (Q : Finset E)
    (x : V) (M r : ℕ) (p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => if CappedRadiusEvent G Q x M r ω then 1 else 0) p

 
theorem sole_root_mark (G : BondGraph V E) (Q : Finset E) (x y : V) (ω : Finset E)
    (m : Finset V) (hxy : Conn G (ω : Set E) x y)
    (hm : m ∩ finiteRootComponent G ω x = {y}) :
    MarkedEvent G ω m x ∧ markedOpenPivotals G Q x ω m = pairOpenPivotals G Q x y ω := by
  have hyW : y ∈ finiteRootComponent G ω x := by
    change y ∈ (finiteRootComponent G ω x : Set V)
    rwa [coe_finiteRootComponent]
  have hym : y ∈ m := (Finset.mem_inter.mp (hm ▸ Finset.mem_singleton_self y)).1
  have hmconn (η : Finset E) (hη : η ⊆ ω) :
      MarkedEvent G η m x ↔ Conn G (η : Set E) x y := by
    constructor
    · rintro ⟨z,hzm,hxz⟩
      have hzW : z ∈ finiteRootComponent G ω x := by
        change z ∈ (finiteRootComponent G ω x : Set V)
        rw [coe_finiteRootComponent]
        exact conn_mono G (by exact_mod_cast hη) hxz
      have hzy : z = y := Finset.mem_singleton.mp (hm ▸ Finset.mem_inter.mpr ⟨hzm,hzW⟩)
      rwa [hzy] at hxz
    · exact fun h => ⟨y,hym,h⟩
  refine ⟨⟨y,hym,hxy⟩,?_⟩
  ext e
  simp only [markedOpenPivotals,pairOpenPivotals,Finset.mem_filter]
  change (e ∈ Q ∧ e ∈ ω ∧ MarkedEvent G ω m x ∧ ¬MarkedEvent G (ω.erase e) m x) ↔ _
  rw [hmconn ω Finset.Subset.rfl,hmconn (ω.erase e) (Finset.erase_subset e ω)]

 
theorem bernoulliPolynomial_exact_indicator (F S : Finset V) (hSF : S ⊆ F) (h : ℝ) :
    bernoulliPolynomial F (fun m => if m = S then (1:ℝ) else 0) h =
      h^S.card*(1-h)^(F.card-S.card) := by
  unfold bernoulliPolynomial
  rw [Finset.sum_eq_single_of_mem S (Finset.mem_powerset.mpr hSF)]
  · simp
  · intro m hm hne
    simp [hne]

 
theorem bernoulliPolynomial_sole_root_mark (G : BondGraph V E) (Q : Finset E)
    (F : Finset V) (x y : V) (ω : Finset E) (hω : ω ⊆ Q)
    (hF : insert x (searchVertices G Q) ⊆ F) (hxy : Conn G (ω : Set E) x y) (h : ℝ) :
    bernoulliPolynomial F (fun m => if m ∩ finiteRootComponent G ω x = {y} then (1:ℝ) else 0) h =
      h*(1-h)^((finiteRootComponent G ω x).card-1) := by
  rw [bernoulliPolynomial_restrict _ _ (finiteRootComponent_subset G Q F x ω hω hF)
    (fun a => if a = {y} then (1:ℝ) else 0) h]
  have hy : y ∈ finiteRootComponent G ω x := by
    change y ∈ (finiteRootComponent G ω x : Set V)
    rwa [coe_finiteRootComponent]
  rw [bernoulliPolynomial_exact_indicator _ {y} (Finset.singleton_subset_iff.mpr hy)]
  simp

 
theorem cappedRadius_mark_comparison (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (M r : ℕ) (p h : unitInterval)
    (hF : insert x (searchVertices G Q) ⊆ F) :
    (h:ℝ)*(1-h)^M*finiteCappedRadiusTail G Q x M r p ≤ finiteMarkedTail G Q F x r h p := by
  unfold finiteCappedRadiusTail finiteMarkedTail
  rw [← bernoulliPolynomial_const_mul]
  apply bernoulliPolynomial_mono _ _ _ _ p.2
  intro ω hω
  by_cases he : CappedRadiusEvent G Q x M r ω
  · obtain ⟨hcap,y,hxy,hr⟩ := he
    have he : CappedRadiusEvent G Q x M r ω := ⟨hcap,y,hxy,hr⟩
    simp only [he,ite_true,mul_one]
    calc
      (h:ℝ)*(1-h)^M ≤ (h:ℝ)*(1-h)^((finiteRootComponent G ω x).card-1) := by
        apply mul_le_mul_of_nonneg_left _ h.2.1
        exact pow_le_pow_of_le_one (sub_nonneg.mpr h.2.2) (by linarith [h.2.1])
          (Nat.le_trans (Nat.sub_le _ _) hcap)
      _ = bernoulliPolynomial F
          (fun m => if m ∩ finiteRootComponent G ω x = {y} then (1:ℝ) else 0) h :=
        (bernoulliPolynomial_sole_root_mark G Q F x y ω hω hF hxy h).symm
      _ ≤ _ := by
        apply bernoulliPolynomial_mono _ _ _ _ h.2
        intro m hm
        by_cases hs : m ∩ finiteRootComponent G ω x = {y}
        · obtain ⟨heq,hpiv⟩ := sole_root_mark G Q x y ω m hxy hs
          have hlarge : r ≤ (markedOpenPivotals G Q x ω m).card := hpiv ▸ hr
          simp only [hs,heq,hlarge,and_self,ite_true,le_refl]
        · simp only [hs,ite_false]
          split_ifs <;> norm_num
  · simp only [he,ite_false,mul_zero]
    apply bernoulliPolynomial_nonneg _ _ _ h.2
    intro m hm
    split_ifs <;> norm_num

theorem finiteMarkedMoment_zero_le_one (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (p h : unitInterval) : finiteMarkedMoment G Q F x 0 h p ≤ 1 := by
  unfold finiteMarkedMoment
  rw [← bernoulliPolynomial_const Q (1:ℝ) (p:ℝ)]
  apply bernoulliPolynomial_mono _ _ _ _ p.2
  intro ω hω
  rw [← bernoulliPolynomial_const F (1:ℝ) (h:ℝ)]
  apply bernoulliPolynomial_mono _ _ _ _ h.2
  intro m hm
  rw [markedMomentValue_zero]
  split_ifs <;> norm_num

 
theorem finiteCappedRadiusTail_exponential [Nonempty V] (G : BondGraph V E)
    (p h : unitInterval) (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (hh1 : (h:ℝ) < 1)
    (d : ℕ) (hd : 0 < d) (Q : Finset E) (x : V)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (B : ℝ) (hB : 1 ≤ B)
    (hAB : (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h) ≤ B) (M r : ℕ) :
    finiteCappedRadiusTail G Q x M r p ≤
      (2/((h:ℝ)*(1-h)^M))*Real.exp (-(r:ℝ)/(4*B)) := by
  let F := insert x (searchVertices G Q)
  have hcomp := cappedRadius_mark_comparison G Q F x M r p h Finset.Subset.rfl
  have ht := finiteMarkedTail_exponential G p h hp hh d hd Q F x hdeg Finset.Subset.rfl B hB hAB r
  have hm := finiteMarkedMoment_zero_le_one G Q F x p h
  have hb : 0 < (h:ℝ)*(1-h)^M := mul_pos hh (pow_pos (sub_pos.mpr hh1) _)
  have hbound : (h:ℝ)*(1-h)^M*finiteCappedRadiusTail G Q x M r p ≤
      2*Real.exp (-(r:ℝ)/(4*B)) := by
    have hpos : 0 ≤ 2*Real.exp (-(r:ℝ)/(4*B)) := by positivity
    have hl := mul_le_mul_of_nonneg_left hm hpos
    rw [mul_one] at hl
    exact hcomp.trans (ht.trans hl)
  calc
    _ ≤ (2*Real.exp (-(r:ℝ)/(4*B)))/((h:ℝ)*(1-h)^M) :=
      (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hbound)
    _ = _ := by ring

end FiniteCappedRadius

section PruningGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem pairOpenPivotals_symm (G : BondGraph V E) (Q : Finset E) (ω : Finset E) (x y : V) :
    pairOpenPivotals G Q x y ω = pairOpenPivotals G Q y x ω := by
  ext e
  simp only [pairOpenPivotals,Finset.mem_filter]
  have h₁ : Conn G (ω : Set E) x y ↔ Conn G (ω : Set E) y x :=
    ⟨conn_symm G _,conn_symm G _⟩
  have h₂ : Conn G (ω.erase e : Set E) x y ↔ Conn G (ω.erase e : Set E) y x :=
    ⟨conn_symm G _,conn_symm G _⟩
  rw [h₁,h₂]

 
theorem pairOpenPivotals_triangle_subset (G : BondGraph V E) (Q : Finset E) (ω : Finset E)
    (x y z : V) (hxy : Conn G (ω : Set E) x y) (hyz : Conn G (ω : Set E) y z) :
    pairOpenPivotals G Q x z ω ⊆ pairOpenPivotals G Q x y ω ∪ pairOpenPivotals G Q y z ω := by
  intro e he
  obtain ⟨heQ,heω,_,hnxz⟩ := Finset.mem_filter.mp he
  by_cases hxy' : Conn G (ω.erase e : Set E) x y
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨heQ,heω,hyz,fun hyz' => hnxz (hxy'.trans hyz')⟩)
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heQ,heω,hxy,hxy'⟩)

theorem pairOpenPivotals_triangle (G : BondGraph V E) (Q : Finset E) (ω : Finset E)
    (x y z : V) (hxy : Conn G (ω : Set E) x y) (hyz : Conn G (ω : Set E) y z) :
    (pairOpenPivotals G Q x z ω).card ≤
      (pairOpenPivotals G Q x y ω).card+(pairOpenPivotals G Q y z ω).card :=
  (Finset.card_le_card (pairOpenPivotals_triangle_subset G Q ω x y z hxy hyz)).trans
    (Finset.card_union_le _ _)

 
theorem conn_no_crossing_internal (G : BondGraph V E) (W : Set V) (ω : Set E)
    (hc : ∀ e ∈ ω, ¬CutExists G W e) {x y : V} (hx : x ∈ W) (hxy : Conn G ω x y) :
    Conn G (ω ∩ internalEdges G W) x y ∧ y ∈ W := by
  induction hxy with
  | refl => exact ⟨conn_refl _ _ _,hx⟩
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    have hb : b ∈ W := by
      by_contra hn
      exact hc e he ⟨a,b,heq,ih.2,hn⟩
    exact ⟨ih.1.tail ⟨e,⟨he,(mem_internalEdges_of_ends G W e a b heq).mpr ⟨ih.2,hb⟩⟩,heq⟩,hb⟩

 
theorem conn_one_attachment_internal (G : BondGraph V E) (W : Set V) (ω : Set E)
    (e : E) (he : e ∈ ω) (hec : CutExists G W e)
    (hone : ∀ f ∈ ω, CutExists G W f → f = e)
    {x y : V} (hx : x ∈ W) (hy : y ∈ W) (hxy : Conn G ω x y) :
    Conn G (ω ∩ internalEdges G W) x y := by
  obtain ⟨a,b,hab,ha,hb⟩ := hec
  let η := ω \ {e}
  have hn : ∀ f ∈ η, ¬CutExists G W f := by
    intro f hf hc
    exact hf.2 (Set.mem_singleton_iff.mpr (hone f hf.1 hc))
  have hη (u v : V) (hu : u ∈ W) (huv : Conn G η u v) :=
    conn_no_crossing_internal G W η hn hu huv
  have hω : insert e η = ω := by dsimp [η]; ext f; simp [he]
  have hw : Conn G (insert e η) x y := hω ▸ hxy
  rcases (conn_insert_iff G η e a b x y hab).mp hw with h | ⟨_,h⟩ | ⟨h,_⟩
  · exact conn_mono G (show η ∩ internalEdges G W ⊆ ω ∩ internalEdges G W from
      fun _ hf => ⟨hf.1.1,hf.2⟩) (hη x y hx h).1
  · exact (hb (hη y b hy (conn_symm G η h)).2).elim
  · exact (hb (hη x b hx h).2).elim

noncomputable def internalBonds (G : BondGraph V E) (ω : Finset E) (W : Set V) : Finset E :=
  ω.filter fun e => e ∈ internalEdges G W

@[simp] theorem coe_internalBonds (G : BondGraph V E) (ω : Finset E) (W : Set V) :
    (internalBonds G ω W : Set E) = (ω : Set E) ∩ internalEdges G W := by
  ext e; simp [internalBonds]

 
theorem pairOpenPivotals_one_attachment (G : BondGraph V E) (Q ω : Finset E) (W : Set V)
    (e : E) (he : e ∈ ω) (hec : CutExists G W e)
    (hone : ∀ f ∈ ω, CutExists G W f → f = e)
    {x y : V} (hx : x ∈ W) (hy : y ∈ W) :
    pairOpenPivotals G Q x y (internalBonds G ω W) ⊆ pairOpenPivotals G Q x y ω := by
  intro f hf
  obtain ⟨hfQ,hfω,hxy,hnxy⟩ := Finset.mem_filter.mp hf
  have hfint : f ∈ internalEdges G W := (Finset.mem_filter.mp hfω).2
  have hfe : e ≠ f := by
    intro hef
    obtain ⟨a,b,hab,ha,hb⟩ := hec
    have hh : e ∈ internalEdges G W := hef ▸ hfint
    exact hb ((mem_internalEdges_of_ends G W e a b hab).mp hh).2
  have he' : e ∈ ω.erase f := Finset.mem_erase.mpr ⟨hfe,he⟩
  have hcoe : (internalBonds G ω W).erase f = internalBonds G (ω.erase f) W := by
    ext g; simp [internalBonds]; tauto
  refine Finset.mem_filter.mpr ⟨hfQ,(Finset.mem_filter.mp hfω).1,?_,?_⟩
  · exact conn_mono G (by simpa only [coe_internalBonds] using Set.inter_subset_left) hxy
  · intro h
    have hh := conn_one_attachment_internal G W (ω.erase f : Set E) e he' hec
      (fun g hg hc => hone g (Finset.mem_of_mem_erase hg) hc) hx hy h
    apply hnxy
    simpa only [hcoe,coe_internalBonds] using hh

 
theorem conn_first_entry (G : BondGraph V E) (W : Set V) (ω : Set E)
    {x y : V} (hx : x ∉ W) (hy : y ∈ W) (hxy : Conn G ω x y) :
    ∃ a b e, a ∉ W ∧ b ∈ W ∧ e ∈ ω ∧ G e = s(a,b) ∧
      Conn G (ω ∩ internalEdges G Wᶜ) x a := by
  let Entry : Prop := ∃ a b e, a ∉ W ∧ b ∈ W ∧ e ∈ ω ∧ G e = s(a,b) ∧
      Conn G (ω ∩ internalEdges G Wᶜ) x a
  have haux : Conn G (ω ∩ internalEdges G Wᶜ) x y ∨ Entry := by
    clear hy
    induction hxy with
    | refl => exact Or.inl (conn_refl _ _ _)
    | @tail a b hxa hab ih =>
      rcases ih with ih | ih
      · have ha : a ∉ W := conn_internal_endpoint G Wᶜ hx ih
        obtain ⟨e,he,heq⟩ := hab
        by_cases hb : b ∈ W
        · exact Or.inr ⟨a,b,e,ha,hb,he,heq,ih⟩
        · exact Or.inl (ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G Wᶜ e a b heq).mpr ⟨ha,hb⟩⟩,heq⟩)
      · exact Or.inr ih
  rcases haux with h | h
  · exact ((conn_internal_endpoint G Wᶜ hx h) hy).elim
  · exact h

 
noncomputable def pruneContacts (G : BondGraph V E) (ω : Finset E) (W : Set V) (e : E) : Finset E :=
  ω.filter fun f => ¬CutExists G W f ∨ f = e

theorem internal_not_cut (G : BondGraph V E) (W : Set V) {e : E}
    (he : e ∈ internalEdges G W) : ¬CutExists G W e := by
  rintro ⟨a,b,hab,ha,hb⟩
  exact hb ((mem_internalEdges_of_ends G W e a b hab).mp he).2

theorem exterior_not_cut (G : BondGraph V E) (W : Set V) {e : E}
    (he : e ∈ internalEdges G Wᶜ) : ¬CutExists G W e := by
  rintro ⟨a,b,hab,ha,hb⟩
  exact ((mem_internalEdges_of_ends G Wᶜ e a b hab).mp he).1 ha

theorem internal_pruneContacts (G : BondGraph V E) (ω : Finset E) (W : Set V) (e : E) :
    internalBonds G (pruneContacts G ω W e) W = internalBonds G ω W := by
  ext f
  simp only [internalBonds,pruneContacts,Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,Or.inl (internal_not_cut G W h.2)⟩,h.2⟩

theorem pruneContacts_only_attachment (G : BondGraph V E) (ω : Finset E) (W : Set V) (e : E) :
    ∀ f ∈ pruneContacts G ω W e, CutExists G W f → f = e := by
  intro f hf hc
  exact (Finset.mem_filter.mp hf).2.resolve_left (not_not.mpr hc)

 
theorem exists_pruneContacts_root (G : BondGraph V E) (ω : Finset E) (W : Set V) (x : V)
    (hWroot : W ⊆ cluster G ω x) (hWconn : ∀ a ∈ W, ∀ b ∈ W,
      Conn G (ω ∩ internalEdges G W) a b)
    (hcontact : ∃ e ∈ ω, CutExists G W e) :
    ∃ e ∈ ω, CutExists G W e ∧ W ⊆ cluster G (pruneContacts G ω W e) x := by
  by_cases hx : x ∈ W
  · obtain ⟨e,he,hec⟩ := hcontact
    refine ⟨e,he,hec,?_⟩
    intro y hy
    apply conn_mono G _ (hWconn x hx y hy)
    intro f hf
    exact Finset.mem_filter.mpr ⟨hf.1,Or.inl (internal_not_cut G W hf.2)⟩
  · obtain ⟨e₀,he₀,a,b,hab,ha,hb⟩ := hcontact
    obtain ⟨c,z,e,hc,hz,he,hez,hxc⟩ := conn_first_entry G W ω hx ha (hWroot ha)
    have hec : CutExists G W e := ⟨z,c,by simpa only [Sym2.eq_swap] using hez,hz,hc⟩
    have hep : e ∈ pruneContacts G ω W e := Finset.mem_filter.mpr ⟨he,Or.inr rfl⟩
    have hxz : Conn G (pruneContacts G ω W e : Set E) x z :=
      (conn_mono G (fun f hf => Finset.mem_filter.mpr ⟨hf.1,Or.inl (exterior_not_cut G W hf.2)⟩) hxc).tail
        ⟨e,hep,hez⟩
    refine ⟨e,he,hec,?_⟩
    intro y hy
    exact hxz.trans (conn_mono G (fun f hf =>
      Finset.mem_filter.mpr ⟨hf.1,Or.inl (internal_not_cut G W hf.2)⟩) (hWconn z hz y hy))

end PruningGeometry

section GoodnessGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] theorem mem_pairOpenPivotals (G : BondGraph V E) (Q : Finset E) (x y : V)
    (ω : Finset E) (e : E) : e ∈ pairOpenPivotals G Q x y ω ↔
      e ∈ Q ∧ OpenMarkedPivotal G (ω : Set E) {y} x e := by
  simp only [pairOpenPivotals,Finset.mem_filter,OpenMarkedPivotal,MarkedEvent,
    Set.mem_singleton_iff,exists_eq_left,Finset.coe_erase,Finset.mem_coe]

 
theorem pairOpenPivotals_card_le (G : BondGraph V E) (Q : Finset E) (x y : V) (ω : Finset E) :
    (pairOpenPivotals G Q x y ω).card ≤ (finiteRootComponent G ω x).card-1 := by
  let N := (finiteRootComponent G ω x).card
  have hN : (cluster G (ω : Set E) x).ncard = N := by
    rw [← coe_finiteRootComponent,Set.ncard_coe_finset]
  have hm : Set.MapsTo (pivotalRank G ω x) (pairOpenPivotals G Q x y ω : Set E)
      (Finset.Ico 1 N : Set ℕ) := by
    intro e he
    have he' := ((mem_pairOpenPivotals G Q x y ω e).mp he).2
    have hfin := cluster_finite_of_finite_edges G (ω := (ω : Set E) \ {e}) (ω.finite_toSet.subset Set.sdiff_subset) x
    have hpos : 0 < pivotalRank G ω x e :=
      (Set.ncard_pos hfin).mpr ⟨x,conn_refl G _ x⟩
    have hlt : pivotalRank G ω x e < N := by
      rw [pivotalRank,← hN]
      apply Set.ncard_lt_ncard _ (cluster_finite_of_finite_edges G ω.finite_toSet x)
      refine Set.ssubset_iff_subset_ne.mpr ⟨fun z hz => conn_mono G Set.sdiff_subset hz,?_⟩
      intro heq
      obtain ⟨z,hz,hxz⟩ := he'.2.1
      have hz' : z ∈ cluster G (ω : Set E) x := hxz
      have hz'' : z ∈ cluster G ((ω : Set E) \ {e}) x := heq.symm ▸ hz'
      exact he'.2.2 ⟨z,hz,hz''⟩
    exact Finset.mem_Ico.mpr ⟨hpos,hlt⟩
  have hi : Set.InjOn (pivotalRank G ω x) (pairOpenPivotals G Q x y ω : Set E) := by
    intro e he f hf h
    exact pivotalRank_injective G ω.finite_toSet {y} x
      ((mem_pairOpenPivotals G Q x y ω e).mp he).2
      ((mem_pairOpenPivotals G Q x y ω f).mp hf).2 h
  simpa [N] using Finset.card_le_card_of_injOn (pivotalRank G ω x) hm hi

theorem finiteRootComponent_mono (G : BondGraph V E) {ω η : Finset E} (h : ω ⊆ η) (x : V) :
    finiteRootComponent G ω x ⊆ finiteRootComponent G η x := by
  intro y hy
  change y ∈ (finiteRootComponent G η x : Set V)
  rw [coe_finiteRootComponent]
  apply conn_mono G (show (ω : Set E) ⊆ η from h)
  change y ∈ (finiteRootComponent G ω x : Set V) at hy
  rwa [coe_finiteRootComponent] at hy

 
noncomputable def openContacts (G : BondGraph V E) (ω : Finset E) (W : Set V) : Finset E :=
  ω.filter fun e => CutExists G W e

 
def BadPieceEvent (G : BondGraph V E) (Q : Finset E) (x : V) (M K : ℕ) (L : ℝ)
    (ω : Finset E) : Prop :=
  (finiteRootComponent G ω x).card ≤ M ∧ ∃ W : Finset V,
    W ⊆ finiteRootComponent G ω x ∧
    (∀ a ∈ W, ∀ b ∈ W, Conn G (internalBonds G ω (W : Set V) : Set E) a b) ∧
    (openContacts G ω (W : Set V)).card = K ∧
    ∃ a ∈ W, ∃ b ∈ W, (K:ℝ)*L < (pairOpenPivotals G Q a b (internalBonds G ω (W : Set V))).card

 
theorem badPieceEvent_contact_bound (G : BondGraph V E) (Q : Finset E) (x : V)
    (M K : ℕ) (L : ℝ) (ω : Finset E) (h : BadPieceEvent G Q x M K L ω) :
    (K:ℝ)*L < (M:ℝ) := by
  obtain ⟨hcap,W,hW,_,_,a,ha,b,_,hbad⟩ := h
  have hsub : finiteRootComponent G (internalBonds G ω (W : Set V)) a ⊆ W := by
    intro z hz
    apply conn_internal_endpoint G (W : Set V) (ω := (ω : Set E)) ha
    change z ∈ (finiteRootComponent G (internalBonds G ω (W : Set V)) a : Set V) at hz
    rw [coe_finiteRootComponent] at hz
    simpa only [coe_internalBonds,cluster,Set.mem_ofPred_eq] using hz
  have hab := pairOpenPivotals_card_le G Q a b (internalBonds G ω (W : Set V))
  have hpos : 0 < (finiteRootComponent G (internalBonds G ω (W : Set V)) a).card := by
    apply Finset.card_pos.mpr
    refine ⟨a,?_⟩
    change a ∈ (finiteRootComponent G (internalBonds G ω (W : Set V)) a : Set V)
    rw [coe_finiteRootComponent]
    exact conn_refl G _ a
  have hn : (pairOpenPivotals G Q a b (internalBonds G ω (W : Set V))).card < M := by
    have h₁ := Finset.card_le_card hsub
    have h₂ := Finset.card_le_card hW
    omega
  exact hbad.trans (by exact_mod_cast hn)

 
noncomputable def incidentBonds (G : BondGraph V E) (Q : Finset E) (W : Finset V) : Finset E :=
  W.biUnion fun v => Q.filter fun e => v ∈ G e

@[simp] theorem mem_incidentBonds (G : BondGraph V E) (Q : Finset E) (W : Finset V) (e : E) :
    e ∈ incidentBonds G Q W ↔ e ∈ Q ∧ ∃ v ∈ W, v ∈ G e := by
  simp only [incidentBonds,Finset.mem_biUnion,Finset.mem_filter]
  aesop

theorem incidentBonds_card_le (G : BondGraph V E) (Q : Finset E) (W : Finset V) (d : ℕ)
    (hd : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) :
    (incidentBonds G Q W).card ≤ d*W.card := by
  calc
    _ ≤ ∑ v ∈ W, (Q.filter fun e => v ∈ G e).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ W, d := Finset.sum_le_sum fun _ _ => hd _
    _ = _ := by simp [Nat.mul_comm]

 

theorem badPieceEvent_pruning (G : BondGraph V E) (Q : Finset E) (x : V) (M K r : ℕ)
    (L : ℝ) (hK : 0 < K) (hr : 2*(r:ℝ) ≤ (K:ℝ)*L)
    (ω : Finset E) (hω : ω ⊆ Q) (h : BadPieceEvent G Q x M K L ω) :
    ∃ η : Finset E, η ⊆ ω ∧ CappedRadiusEvent G Q x M r η ∧
      (ω \ η).card ≤ K ∧ ω \ η ⊆ incidentBonds G Q (finiteRootComponent G η x) := by
  obtain ⟨hcap,W,hW,hWconn,hcontacts,a,ha,b,hb,hbad⟩ := h
  have hcontact : ∃ e ∈ ω, CutExists G (W : Set V) e := by
    have : (openContacts G ω (W : Set V)).Nonempty := Finset.card_pos.mp (hcontacts ▸ hK)
    obtain ⟨e,he⟩ := this
    exact ⟨e,(Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2⟩
  have hWroot : (W : Set V) ⊆ cluster G ω x := by
    intro z hz
    have hh : z ∈ (finiteRootComponent G ω x : Set V) := hW hz
    rwa [coe_finiteRootComponent] at hh
  obtain ⟨e,he,hec,hWη⟩ := exists_pruneContacts_root G ω (W : Set V) x hWroot
    (by intro a ha b hb; simpa only [coe_internalBonds] using hWconn a ha b hb) hcontact
  let η := pruneContacts G ω (W : Set V) e
  have hη : η ⊆ ω := Finset.filter_subset _ _
  have hep : e ∈ η := Finset.mem_filter.mpr ⟨he,Or.inr rfl⟩
  have hpiv := pairOpenPivotals_one_attachment G Q η (W : Set V) e hep hec
    (pruneContacts_only_attachment G ω (W : Set V) e) ha hb
  rw [internal_pruneContacts] at hpiv
  have hfar : (K:ℝ)*L < (pairOpenPivotals G Q a b η).card :=
    hbad.trans_le (by exact_mod_cast Finset.card_le_card hpiv)
  have hxa : Conn G (η : Set E) x a := hWη ha
  have hxb : Conn G (η : Set E) x b := hWη hb
  have htri := pairOpenPivotals_triangle G Q η a x b (conn_symm G η hxa) hxb
  rw [pairOpenPivotals_symm G Q η a x] at htri
  have hlarge : r ≤ (pairOpenPivotals G Q x a η).card ∨
      r ≤ (pairOpenPivotals G Q x b η).card := by
    by_contra hn
    push Not at hn
    have htri' : ((pairOpenPivotals G Q a b η).card:ℝ) ≤
        (pairOpenPivotals G Q x a η).card+(pairOpenPivotals G Q x b η).card := by exact_mod_cast htri
    have h₁ : ((pairOpenPivotals G Q x a η).card:ℝ) < r := by exact_mod_cast hn.1
    have h₂ : ((pairOpenPivotals G Q x b η).card:ℝ) < r := by exact_mod_cast hn.2
    linarith
  have hchanges : ω \ η ⊆ openContacts G ω (W : Set V) := by
    intro f hf
    obtain ⟨hfω,hfη⟩ := Finset.mem_sdiff.mp hf
    refine Finset.mem_filter.mpr ⟨hfω,?_⟩
    by_contra hn
    exact hfη (Finset.mem_filter.mpr ⟨hfω,Or.inl hn⟩)
  refine ⟨η,hη,⟨(Finset.card_le_card (finiteRootComponent_mono G hη x)).trans hcap,?_⟩,
    (Finset.card_le_card hchanges).trans (le_of_eq hcontacts),?_⟩
  · rcases hlarge with h | h
    · exact ⟨a,hxa,h⟩
    · exact ⟨b,hxb,h⟩
  · intro f hf
    obtain ⟨hfω,c,z,hcz,hc,_⟩ := Finset.mem_filter.mp (hchanges hf)
    refine (mem_incidentBonds G Q _ f).mpr ⟨hω hfω,c,?_,?_⟩
    · change c ∈ (finiteRootComponent G η x : Set V)
      rw [coe_finiteRootComponent]
      exact hWη hc
    · simp [hcz]

end GoodnessGeometry

section FiniteInverseCost
attribute [local instance] Classical.propDecidable Classical.decEq

 
def bernoulliWeight (Q ω : Finset E) (p : ℝ) : ℝ :=
  p^ω.card*(1-p)^(Q.card-ω.card)

theorem bernoulliWeight_nonneg (Q ω : Finset E) (p : unitInterval) :
    0 ≤ bernoulliWeight Q ω p := mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)

 
theorem bernoulliWeight_closure_ratio (Q ω η : Finset E) (hη : η ⊆ ω) (hω : ω ⊆ Q)
    (p : ℝ) (hp : p < 1) :
    bernoulliWeight Q ω p = bernoulliWeight Q η p*(p/(1-p))^((ω \ η).card) := by
  have h₁ := Finset.card_le_card hη
  have h₂ := Finset.card_le_card hω
  have hj : (ω \ η).card = ω.card-η.card := Finset.card_sdiff_of_subset hη
  have ha : ω.card = η.card+(ω \ η).card := by omega
  have hb : Q.card-η.card = (Q.card-ω.card)+(ω \ η).card := by omega
  have hq : (1-p) ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  unfold bernoulliWeight
  rw [hb,pow_add,div_pow]
  rw [← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero _ hq)).mpr
  rw [ha,pow_add]
  ring

 
theorem bernoulliWeight_closure_le (Q ω η : Finset E) (hη : η ⊆ ω) (hω : ω ⊆ Q)
    (p : unitInterval) (hp : (p:ℝ) < 1) (K : ℕ) (hj : (ω \ η).card ≤ K) :
    bernoulliWeight Q ω p ≤ (max 1 ((p:ℝ)/(1-p)))^K*bernoulliWeight Q η p := by
  rw [bernoulliWeight_closure_ratio Q ω η hη hω p hp,mul_comm]
  apply mul_le_mul_of_nonneg_right _ (bernoulliWeight_nonneg Q η p)
  calc
    _ ≤ (max 1 ((p:ℝ)/(1-p)))^((ω \ η).card) :=
      pow_le_pow_left₀ (div_nonneg p.2.1 (sub_nonneg.mpr p.2.2)) (le_max_right ..) _
    _ ≤ _ := pow_le_pow_right₀ (le_max_left ..) hj

 
theorem card_small_subsets_le (S : Finset E) (K N : ℕ) (hS : S.card ≤ N) (hN : 1 ≤ N) :
    (S.powerset.filter fun T => T.card ≤ K).card ≤ (K+1)*N^K := by
  have hsub : S.powerset.filter (fun T => T.card ≤ K) ⊆
      (Finset.range (K+1)).biUnion (fun j => S.powersetCard j) := by
    intro T hT
    obtain ⟨hTS,hTK⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_biUnion.mpr ⟨T.card,Finset.mem_range.mpr (Nat.lt_succ_of_le hTK),
      Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hTS,rfl⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (K+1), (S.powersetCard j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (K+1), N^K := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left hS _).trans
        (Nat.pow_le_pow_right hN (Nat.le_of_lt_succ (Finset.mem_range.mp hj))))
    _ = _ := by simp

 
theorem closure_fiber_card_le (A : Finset (Finset E)) (f : Finset E → Finset E)
    (S : Finset E) (η : Finset E) (K N : ℕ) (hN : 1 ≤ N) (hS : S.card ≤ N)
    (hf : ∀ ω ∈ A, f ω = η → f ω ⊆ ω ∧ (ω \ f ω).card ≤ K ∧ ω \ f ω ⊆ S) :
    (A.filter fun ω => f ω = η).card ≤ (K+1)*N^K := by
  have hm : Set.MapsTo (fun ω : Finset E => ω \ η) (A.filter fun ω => f ω = η : Set (Finset E))
      (S.powerset.filter fun T => T.card ≤ K : Set (Finset E)) := by
    intro ω hω
    obtain ⟨hωA,heq⟩ := Finset.mem_filter.mp hω
    obtain ⟨_,hj,hs⟩ := hf ω hωA heq
    rw [heq] at hj hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs,hj⟩
  have hi : Set.InjOn (fun ω : Finset E => ω \ η) (A.filter fun ω => f ω = η : Set (Finset E)) := by
    intro ω hω ζ hζ heq
    obtain ⟨hωA,hωη⟩ := Finset.mem_filter.mp hω
    obtain ⟨hζA,hζη⟩ := Finset.mem_filter.mp hζ
    have h₁ := (hf ω hωA hωη).1
    have h₂ := (hf ζ hζA hζη).1
    rw [hωη] at h₁
    rw [hζη] at h₂
    have : η ∪ (ω \ η) = η ∪ (ζ \ η) := congrArg (fun s => η ∪ s) heq
    simpa only [Finset.union_sdiff_of_subset h₁,Finset.union_sdiff_of_subset h₂] using this
  exact (Finset.card_le_card_of_injOn (fun ω => ω \ η) hm hi).trans (card_small_subsets_le S K N hS hN)

 
theorem finite_closure_comparison (Q : Finset E) (A B : Finset (Finset E))
    (hA : A ⊆ Q.powerset) (f : Finset E → Finset E) (S : Finset E → Finset E)
    (K N : ℕ) (hN : 1 ≤ N) (p : unitInterval) (hp : (p:ℝ) < 1)
    (hf : ∀ ω ∈ A, f ω ∈ B ∧ f ω ⊆ ω ∧ (ω \ f ω).card ≤ K ∧ ω \ f ω ⊆ S (f ω))
    (hS : ∀ η ∈ B, (S η).card ≤ N) :
    (∑ ω ∈ A, bernoulliWeight Q ω p) ≤
      (((K+1)*N^K : ℕ):ℝ)*(max 1 ((p:ℝ)/(1-p)))^K*∑ η ∈ B, bernoulliWeight Q η p := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun ω hω => (hf ω hω).1) (fun ω => bernoulliWeight Q ω p),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro η hη
  let T := A.filter fun ω => f ω = η
  have hc : T.card ≤ (K+1)*N^K := closure_fiber_card_le A f (S η) η K N hN (hS η hη) (by
    intro ω hω heq
    have hh := (hf ω hω).2
    simpa only [heq] using hh)
  have hweight : ∀ ω ∈ T, bernoulliWeight Q ω p ≤
      (max 1 ((p:ℝ)/(1-p)))^K*bernoulliWeight Q η p := by
    intro ω hω
    obtain ⟨hωA,heq⟩ := Finset.mem_filter.mp hω
    have hh := bernoulliWeight_closure_le Q ω (f ω) (hf ω hωA).2.1
      (Finset.mem_powerset.mp (hA hωA)) p hp K (hf ω hωA).2.2.1
    simpa only [heq] using hh
  calc
    _ ≤ ∑ _ω ∈ T, (max 1 ((p:ℝ)/(1-p)))^K*bernoulliWeight Q η p := Finset.sum_le_sum hweight
    _ = (T.card:ℝ)*((max 1 ((p:ℝ)/(1-p)))^K*bernoulliWeight Q η p) := by simp
    _ ≤ (((K+1)*N^K:ℕ):ℝ)*((max 1 ((p:ℝ)/(1-p)))^K*bernoulliWeight Q η p) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
        (mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left ..)) _) (bernoulliWeight_nonneg Q η p))
    _ = _ := by ring

end FiniteInverseCost

section FiniteGoodnessProbability
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteBadPieceProbability (G : BondGraph V E) (Q : Finset E)
    (x : V) (M K : ℕ) (L p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => if BadPieceEvent G Q x M K L ω then 1 else 0) p

theorem bernoulliPolynomial_indicator_weight (Q : Finset E) (P : Finset E → Prop) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => if P ω then 1 else 0) p =
      ∑ ω ∈ Q.powerset.filter P, bernoulliWeight Q ω p := by
  rw [Finset.sum_filter]
  unfold bernoulliPolynomial
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : P ω <;> simp [h,bernoulliWeight]

 
theorem finiteBadPieceProbability_le_radius (G : BondGraph V E) (Q : Finset E) (x : V)
    (M K r d : ℕ) (L : ℝ) (hK : 0 < K) (hN : 1 ≤ d*M)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d)
    (hr : 2*(r:ℝ) ≤ (K:ℝ)*L) (p : unitInterval) (hp : (p:ℝ) < 1) :
    finiteBadPieceProbability G Q x M K L p ≤
      (((K+1)*(d*M)^K:ℕ):ℝ)*(max 1 ((p:ℝ)/(1-p)))^K*finiteCappedRadiusTail G Q x M r p := by
  let A := Q.powerset.filter (BadPieceEvent G Q x M K L)
  let B := Q.powerset.filter (CappedRadiusEvent G Q x M r)
  let S := fun η => incidentBonds G Q (finiteRootComponent G η x)
  have hex : ∀ ω : Finset E, ∃ η : Finset E, ω ∈ A →
      η ∈ B ∧ η ⊆ ω ∧ (ω \ η).card ≤ K ∧ ω \ η ⊆ S η := by
    intro ω
    by_cases hω : ω ∈ A
    · obtain ⟨hωQ,hωbad⟩ := Finset.mem_filter.mp hω
      have hωsub := Finset.mem_powerset.mp hωQ
      obtain ⟨η,hη,hcap,hcard,hS⟩ := badPieceEvent_pruning G Q x M K r L hK hr ω hωsub hωbad
      exact ⟨η,fun _ => ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hη.trans hωsub),hcap⟩,
        hη,hcard,hS⟩⟩
    · exact ⟨∅,fun h => (hω h).elim⟩
  choose f hf using hex
  have hS : ∀ η ∈ B, (S η).card ≤ d*M := by
    intro η hη
    exact (incidentBonds_card_le G Q (finiteRootComponent G η x) d hdeg).trans
      (Nat.mul_le_mul_left d (Finset.mem_filter.mp hη).2.1)
  have hc := finite_closure_comparison Q A B (Finset.filter_subset _ _) f S K (d*M) hN p hp hf hS
  simpa only [finiteBadPieceProbability,finiteCappedRadiusTail,bernoulliPolynomial_indicator_weight,
    A,B] using hc

 
theorem finiteBadPieceProbability_exponential [Nonempty V] (G : BondGraph V E)
    (Q : Finset E) (x : V) (M K d : ℕ) (L : ℝ) (hK : 0 < K) (hN : 1 ≤ d*M)
    (hL : 4 ≤ (K:ℝ)*L) (hd : 0 < d)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d)
    (p h : unitInterval) (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (hh1 : (h:ℝ) < 1)
    (B : ℝ) (hB : 1 ≤ B)
    (hAB : (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h) ≤ B) :
    finiteBadPieceProbability G Q x M K L p ≤
      (((K+1)*(d*M)^K:ℕ):ℝ)*(max 1 ((p:ℝ)/(1-p)))^K*
        (2/((h:ℝ)*(1-h)^M))*Real.exp (-((K:ℝ)*L)/(16*B)) := by
  let r := ⌈(K:ℝ)*L/4⌉₊
  have hpos : 0 ≤ (K:ℝ)*L/4 := by linarith
  have hrlo : (K:ℝ)*L/4 ≤ r := Nat.le_ceil _
  have hrhi : (r:ℝ) < (K:ℝ)*L/4+1 := Nat.ceil_lt_add_one hpos
  have hr : 2*(r:ℝ) ≤ (K:ℝ)*L := by linarith
  have hrad := finiteCappedRadiusTail_exponential G p h hp hh hh1 d hd Q x hdeg B hB hAB M r
  have hcmp := finiteBadPieceProbability_le_radius G Q x M K r d L hK hN hdeg hr p hp
  have hc : 0 ≤ (((K+1)*(d*M)^K:ℕ):ℝ)*(max 1 ((p:ℝ)/(1-p)))^K := by positivity
  have hhfac : 0 ≤ 2/((h:ℝ)*(1-h)^M) := by positivity
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hratio : -((r:ℝ)/(4*B)) ≤ -((K:ℝ)*L)/(16*B) := by
    apply (le_div_iff₀ (by positivity : 0 < 16*B)).mpr
    field_simp
    nlinarith
  exact hcmp.trans ((mul_le_mul_of_nonneg_left hrad hc).trans (by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by simpa only [neg_div] using hratio)) (mul_nonneg hc hhfac)))

 

def FiniteGoodForScale (G : BondGraph V E) (Q : Finset E) (x : V) (L : ℝ) (ω : Finset E) : Prop :=
  ∀ W : Finset V, W ⊆ finiteRootComponent G ω x →
    (∀ a ∈ W, ∀ b ∈ W, Conn G (internalBonds G ω (W : Set V) : Set E) a b) →
    0 < (openContacts G ω (W : Set V)).card →
    ∀ a ∈ W, ∀ b ∈ W,
      (pairOpenPivotals G Q a b (internalBonds G ω (W : Set V))).card ≤
        ((openContacts G ω (W : Set V)).card:ℝ)*L

def CappedBadGoodnessEvent (G : BondGraph V E) (Q : Finset E) (x : V) (M : ℕ) (L : ℝ)
    (ω : Finset E) : Prop :=
  (finiteRootComponent G ω x).card ≤ M ∧ ¬FiniteGoodForScale G Q x L ω

noncomputable def finiteBadGoodnessProbability (G : BondGraph V E) (Q : Finset E)
    (x : V) (M : ℕ) (L p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => if CappedBadGoodnessEvent G Q x M L ω then 1 else 0) p

 
theorem cappedBadGoodness_iff (G : BondGraph V E) (Q : Finset E) (x : V) (M d : ℕ)
    (L : ℝ) (ω : Finset E) (hω : ω ⊆ Q)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) :
    CappedBadGoodnessEvent G Q x M L ω ↔
      ∃ K ∈ Finset.Icc 1 (d*M), BadPieceEvent G Q x M K L ω := by
  constructor
  · rintro ⟨hcap,hbad⟩
    simp only [FiniteGoodForScale,not_forall] at hbad
    obtain ⟨W,hbad⟩ := hbad
    push Not at hbad
    obtain ⟨hW,hWconn,hK,a,ha,b,hb,hfar⟩ := hbad
    have hinc : openContacts G ω (W : Set V) ⊆ incidentBonds G Q W := by
      intro e he
      obtain ⟨heω,c,z,hcz,hc,_⟩ := Finset.mem_filter.mp he
      exact (mem_incidentBonds G Q W e).mpr ⟨hω heω,c,hc,by simp [hcz]⟩
    have hbound := (Finset.card_le_card hinc).trans ((incidentBonds_card_le G Q W d hdeg).trans
      (Nat.mul_le_mul_left d ((Finset.card_le_card hW).trans hcap)))
    exact ⟨_,Finset.mem_Icc.mpr ⟨hK,hbound⟩,hcap,W,hW,hWconn,rfl,a,ha,b,hb,hfar⟩
  · rintro ⟨K,hK,hcap,W,hW,hWconn,hcontacts,a,ha,b,hb,hfar⟩
    refine ⟨hcap,fun hgood => ?_⟩
    have hh := hgood W hW hWconn (by rw [hcontacts]; exact (Finset.mem_Icc.mp hK).1) a ha b hb
    rw [hcontacts] at hh
    exact not_lt_of_ge hh hfar

 
theorem finiteBadGoodnessProbability_le_sum (G : BondGraph V E) (Q : Finset E) (x : V)
    (M d : ℕ) (L : ℝ) (p : unitInterval)
    (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) :
    finiteBadGoodnessProbability G Q x M L p ≤
      ∑ K ∈ Finset.Icc 1 (d*M), finiteBadPieceProbability G Q x M K L p := by
  unfold finiteBadPieceProbability finiteBadGoodnessProbability
  rw [← bernoulliPolynomial_sum]
  apply bernoulliPolynomial_mono _ _ _ _ p.2
  intro ω hω
  by_cases he : CappedBadGoodnessEvent G Q x M L ω
  · obtain ⟨K,hK,hbad⟩ := (cappedBadGoodness_iff G Q x M d L ω hω hdeg).mp he
    simp only [he,ite_true]
    exact (by simp [hbad] : (1:ℝ) ≤ if BadPieceEvent G Q x M K L ω then 1 else 0).trans
      (Finset.single_le_sum (f := fun j => if BadPieceEvent G Q x M j L ω then (1:ℝ) else 0)
        (fun j _ => by split_ifs <;> norm_num) hK)
  · simp only [he,ite_false]
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

 
theorem finiteBadGoodnessProbability_geometric [Nonempty V] (G : BondGraph V E)
    (Q : Finset E) (x : V) (M d : ℕ) (L : ℝ) (hN : 1 ≤ d*M) (hL : 4 ≤ L)
    (hd : 0 < d) (hdeg : ∀ v, (Q.filter fun e => v ∈ G e).card ≤ d)
    (p h : unitInterval) (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (hh1 : (h:ℝ) < 1)
    (B : ℝ) (hB : 1 ≤ B)
    (hAB : (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h) ≤ B)
    (hq : ((d*M:ℕ):ℝ)*max 1 ((p:ℝ)/(1-p))*Real.exp (-L/(16*B)) ≤ 1) :
    finiteBadGoodnessProbability G Q x M L p ≤
      (2/((h:ℝ)*(1-h)^M))*((d*M:ℕ):ℝ)*((d*M:ℕ)+1)*
        (((d*M:ℕ):ℝ)*max 1 ((p:ℝ)/(1-p))*Real.exp (-L/(16*B))) := by
  let N := d*M
  let a := max 1 ((p:ℝ)/(1-p))
  let H := 2/((h:ℝ)*(1-h)^M)
  let q := (N:ℝ)*a*Real.exp (-L/(16*B))
  have ha : 0 ≤ a := le_trans zero_le_one (le_max_left ..)
  have hq0 : 0 ≤ q := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) (Real.exp_nonneg _)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hkbound : ∀ K ∈ Finset.Icc 1 N, finiteBadPieceProbability G Q x M K L p ≤ H*((N:ℝ)+1)*q := by
    intro K hK
    obtain ⟨hK1,hKN⟩ := Finset.mem_Icc.mp hK
    have hKR : (1:ℝ) ≤ K := by exact_mod_cast hK1
    have hKL : 4 ≤ (K:ℝ)*L := by nlinarith
    have hexp := finiteBadPieceProbability_exponential G Q x M K d L hK1 hN hKL hd hdeg
      p h hp hh hh1 B hB hAB
    have hid : (((K+1)*(d*M)^K:ℕ):ℝ)*(max 1 ((p:ℝ)/(1-p)))^K*
        (2/((h:ℝ)*(1-h)^M))*Real.exp (-((K:ℝ)*L)/(16*B)) = H*((K:ℝ)+1)*q^K := by
      rw [show -((K:ℝ)*L)/(16*B) = (K:ℝ)*(-L/(16*B)) by ring,Real.exp_nat_mul]
      simp only [q,H,N,a,mul_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
      ring
    rw [hid] at hexp
    have hpow : q^K ≤ q := by
      simpa only [pow_one] using pow_le_pow_of_le_one hq0 hq hK1
    calc
      _ ≤ H*((K:ℝ)+1)*q^K := hexp
      _ ≤ H*((N:ℝ)+1)*q := mul_le_mul
        (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hKN 1) hH)
        hpow (pow_nonneg hq0 _) (mul_nonneg hH (by positivity))
  calc
    _ ≤ ∑ K ∈ Finset.Icc 1 N, finiteBadPieceProbability G Q x M K L p :=
      finiteBadGoodnessProbability_le_sum G Q x M d L p hdeg
    _ ≤ ∑ _K ∈ Finset.Icc 1 N, H*((N:ℝ)+1)*q := Finset.sum_le_sum hkbound
    _ = (N:ℝ)*(H*((N:ℝ)+1)*q) := by simp
    _ = _ := by dsimp [N,H,q,a]; push_cast; ring

end FiniteGoodnessProbability

section GoodnessAsymptotics

 
theorem inverse_mark_cost_le (h : ℝ) (hh : 0 ≤ h) (hh2 : h ≤ 1/2) (M : ℕ) :
    ((1-h)^M)⁻¹ ≤ Real.exp (2*(M:ℝ)*h) := by
  have hq : 0 < 1-h := by linarith
  have hi : 1/(1-h) ≤ 1+2*h := (div_le_iff₀ hq).mpr (by nlinarith)
  have hl := Real.one_sub_inv_le_log_of_pos hq
  rw [one_div] at hi
  have hlog : -2*h ≤ Real.log (1-h) := by linarith
  calc
    ((1-h)^M)⁻¹ = Real.exp (-((M:ℝ)*Real.log (1-h))) := by
      rw [← Real.log_pow,Real.exp_neg,Real.exp_log (pow_pos hq _)]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M)
      nlinarith)

 

theorem ghost_scale_estimates (M : ℕ) (ε c a : ℝ) (d : ℕ)
    (hM : 1 ≤ (M:ℝ)) (hε : 0 < ε) (hε1 : ε < 1/2) (hc : 1 ≤ c)
    (ha : 1 ≤ a) (hd : 1 ≤ d)
    (hsmall : (M:ℝ)^(ε-1) ≤ 1/2)
    (hlog : 4*Real.log M ≤ (M:ℝ)^ε)
    (hlog2 : Real.log M ≤ (M:ℝ)^(ε/2))
    (hgrowth : 80*c ≤ (M:ℝ)^(ε/4))
    (hconstant : Real.log (2*(d:ℝ)^2*((d:ℝ)+1)*a) ≤ (M:ℝ)^ε) :
    let h := (M:ℝ)^(ε-1)
    let B := c*(M:ℝ)^(1/2-ε/4)
    let L := (M:ℝ)^(1/2+ε)
    0 < h ∧ h ≤ 1/2 ∧ 1 ≤ B ∧
      c*Real.sqrt (Real.log (1/h)/h) ≤ B ∧
      (2/(h*(1-h)^M))*((d*M:ℕ):ℝ)*((d*M:ℕ)+1)*
        (((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B))) ≤ Real.exp (-(M:ℝ)^ε) := by
  dsimp only
  let h := (M:ℝ)^(ε-1)
  let B := c*(M:ℝ)^(1/2-ε/4)
  let L := (M:ℝ)^(1/2+ε)
  have hMp : 0 < (M:ℝ) := lt_of_lt_of_le zero_lt_one hM
  have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hdp : 0 < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hhp : 0 < h := Real.rpow_pos_of_pos hMp _
  have hq : 0 < 1-h := by dsimp [h] at *; linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hinv : 1/h = (M:ℝ)^(1-ε) := by
    dsimp [h]
    rw [show 1-ε = -(ε-1) by ring,Real.rpow_neg hMp.le,one_div]
  have hmh : (M:ℝ)*h = (M:ℝ)^ε := by
    dsimp [h]
    calc
      _ = (M:ℝ)^((1:ℝ)+(ε-1)) := by rw [Real.rpow_add hMp,Real.rpow_one]
      _ = _ := by congr 1; ring
  have hhM : 1/h ≤ (M:ℝ) := by
    rw [hinv]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hM (show 1-ε ≤ (1:ℝ) by linarith)
  have hB1 : 1 ≤ B := by
    have hp := Real.one_le_rpow hM (show 0 ≤ 1/2-ε/4 by linarith)
    dsimp [B]
    nlinarith
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hAB : c*Real.sqrt (Real.log (1/h)/h) ≤ B := by
    apply mul_le_mul_of_nonneg_left _ hcp.le
    have hl : Real.log (1/h) ≤ Real.log M := by
      rw [hinv,Real.log_rpow hMp]
      nlinarith
    have hl2 : Real.log (1/h)/h ≤ (M:ℝ)^(1-ε/2) := by
      calc
        _ = Real.log (1/h)*(M:ℝ)^(1-ε) := by rw [div_eq_mul_one_div,hinv]
        _ ≤ (M:ℝ)^(ε/2)*(M:ℝ)^(1-ε) :=
          mul_le_mul_of_nonneg_right (hl.trans hlog2) (Real.rpow_nonneg hMp.le _)
        _ = _ := by rw [← Real.rpow_add hMp]; congr 1; ring
    calc
      _ ≤ Real.sqrt ((M:ℝ)^(1-ε/2)) := Real.sqrt_le_sqrt hl2
      _ = (M:ℝ)^(1/2-ε/4) := by
        rw [Real.sqrt_eq_rpow,← Real.rpow_mul hMp.le]
        congr 1
        ring
  have hratio : 5*(M:ℝ)^ε ≤ L/(16*B) := by
    have hid : (M:ℝ)^ε*(M:ℝ)^(ε/4)*(M:ℝ)^(1/2-ε/4) = L := by
      dsimp [L]
      rw [← Real.rpow_add hMp,← Real.rpow_add hMp]
      congr 1
      ring
    apply (le_div_iff₀ (by positivity : 0 < 16*B)).mpr
    have hh := mul_le_mul_of_nonneg_left hgrowth
      (mul_nonneg (Real.rpow_nonneg hMp.le ε) (Real.rpow_nonneg hMp.le (1/2-ε/4)))
    dsimp [B]
    nlinarith [hid]
  refine ⟨hhp,hsmall,hB1,hAB,?_⟩
  let A := 2*(d:ℝ)^2*((d:ℝ)+1)*a
  have hAp : 0 < A := by dsimp [A]; positivity
  have hcost : 2/(h*(1-h)^M) ≤ 2*(M:ℝ)*Real.exp (2*(M:ℝ)^ε) := by
    calc
      _ = 2*(1/h)*((1-h)^M)⁻¹ := by field_simp
      _ ≤ 2*(M:ℝ)*Real.exp (2*(M:ℝ)*h) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hhM (by norm_num))
          (inverse_mark_cost_le h hhp.le hsmall M) (inv_nonneg.mpr (pow_nonneg hq.le _)) (by positivity)
      _ = _ := by rw [show 2*(M:ℝ)*h = 2*(M:ℝ)^ε by rw [mul_assoc,hmh]]
  have hN1 : ((d*M:ℕ):ℝ)+1 ≤ ((d:ℝ)+1)*(M:ℝ) := by push_cast; nlinarith
  have hpoint :
      (2/(h*(1-h)^M))*((d*M:ℕ):ℝ)*((d*M:ℕ)+1)*
        (((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B))) ≤
      A*(M:ℝ)^4*Real.exp (2*(M:ℝ)^ε-L/(16*B)) := by
    calc
      _ ≤ (2*(M:ℝ)*Real.exp (2*(M:ℝ)^ε))*((d*M:ℕ):ℝ)*(((d:ℝ)+1)*(M:ℝ))*
          (((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_right hcost (by positivity)) hN1
          (by positivity) (by positivity)
      _ = _ := by
        rw [show 2*(M:ℝ)^ε-L/(16*B) = 2*(M:ℝ)^ε+(-L/(16*B)) by ring,Real.exp_add]
        dsimp [A]
        push_cast
        ring
  have heq : A*(M:ℝ)^4*Real.exp (2*(M:ℝ)^ε-L/(16*B)) =
      Real.exp (Real.log A+4*Real.log M+2*(M:ℝ)^ε-L/(16*B)) := by
    rw [show Real.log A+4*Real.log M+2*(M:ℝ)^ε-L/(16*B) =
      Real.log A+4*Real.log M+(2*(M:ℝ)^ε-L/(16*B)) by ring,Real.exp_add,
      Real.exp_add,Real.exp_log hAp]
    have hh : Real.exp (4*Real.log M) = (M:ℝ)^4 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hMp] using Real.exp_nat_mul (Real.log M) 4
    rw [hh]
  rw [heq] at hpoint
  exact hpoint.trans (Real.exp_le_exp.mpr (by linarith))

 

theorem eventually_ghost_scale (ε c a : ℝ) (d : ℕ) (hε : 0 < ε) (hε1 : ε < 1/2)
    (hc : 1 ≤ c) (ha : 1 ≤ a) (hd : 1 ≤ d) :
    ∀ᶠ M : ℕ in Filter.atTop,
      let h := (M:ℝ)^(ε-1)
      let B := c*(M:ℝ)^(1/2-ε/4)
      let L := (M:ℝ)^(1/2+ε)
      1 ≤ M ∧ 4 ≤ L ∧ 0 < h ∧ h ≤ 1/2 ∧ 1 ≤ B ∧
        c*Real.sqrt (Real.log (1/h)/h) ≤ B ∧
        (2/(h*(1-h)^M))*((d*M:ℕ):ℝ)*((d*M:ℕ)+1)*
          (((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B))) ≤ Real.exp (-(M:ℝ)^ε) := by
  have hh : ∀ᶠ m : ℝ in Filter.atTop, m^(ε-1) ≤ 1/2 := by
    have ht := tendsto_rpow_neg_atTop (show 0 < 1-ε by linarith)
    filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with m hm
    simpa only [neg_sub] using (show m^(-(1-ε)) < 1/2 from hm).le
  have hl := (isLittleO_log_rpow_atTop hε).bound (show (0:ℝ) < 1/4 by norm_num)
  have hl2 := (isLittleO_log_rpow_atTop (show 0 < ε/2 by linarith)).bound zero_lt_one
  have hg := (tendsto_rpow_atTop (show 0 < ε/4 by linarith)).eventually (Filter.eventually_ge_atTop (80*c))
  have hC := (tendsto_rpow_atTop hε).eventually
    (Filter.eventually_ge_atTop (Real.log (2*(d:ℝ)^2*((d:ℝ)+1)*a)))
  have hL := (tendsto_rpow_atTop (show 0 < 1/2+ε by linarith)).eventually (Filter.eventually_ge_atTop 4)
  have hnum : ∀ᶠ m : ℝ in Filter.atTop, 1 ≤ m ∧ 4 ≤ m^(1/2+ε) ∧ m^(ε-1) ≤ 1/2 ∧
      4*Real.log m ≤ m^ε ∧ Real.log m ≤ m^(ε/2) ∧ 80*c ≤ m^(ε/4) ∧
      Real.log (2*(d:ℝ)^2*((d:ℝ)+1)*a) ≤ m^ε := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hh,hl,hl2,hg,hC,hL] with m hm hh hl hl2 hg hC hL
    have hm0 : 0 ≤ m := le_trans zero_le_one hm
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hm),
      abs_of_nonneg (Real.rpow_nonneg hm0 ε)] at hl
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hm),
      abs_of_nonneg (Real.rpow_nonneg hm0 (ε/2)),one_mul] at hl2
    exact ⟨hm,hL,hh,by linarith,hl2,hg,hC⟩
  have hcast : Filter.Tendsto (fun M : ℕ => (M:ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually hnum] with M hM
  obtain ⟨hM,hL,hh,hl,hl2,hg,hC⟩ := hM
  exact ⟨by exact_mod_cast hM,hL,ghost_scale_estimates M ε c a d hM hε hε1 hc ha hd hh hl hl2 hg hC⟩

 
theorem ghost_ratio_le_one (M d : ℕ) (hM : 1 ≤ M) (hd : 1 ≤ d)
    (h B L a ε : ℝ) (hh : 0 < h) (hh2 : h ≤ 1/2) (ha : 0 ≤ a)
    (hb : (2/(h*(1-h)^M))*((d*M:ℕ):ℝ)*((d*M:ℕ)+1)*
      (((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B))) ≤ Real.exp (-(M:ℝ)^ε)) :
    ((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B)) ≤ 1 := by
  have hq : 0 < 1-h := by linarith
  have hp : (1-h)^M ≤ 1 := pow_le_one₀ hq.le (by linarith)
  have hden : 0 < h*(1-h)^M := mul_pos hh (pow_pos hq _)
  have hH : 1 ≤ 2/(h*(1-h)^M) := by
    apply (le_div_iff₀ hden).mpr
    have := mul_le_mul_of_nonneg_left hp hh.le
    nlinarith
  have hN : (1:ℝ) ≤ (d*M:ℕ) := by exact_mod_cast Nat.mul_le_mul hd hM
  have hprod : 1 ≤ (2/(h*(1-h)^M))*((d*M:ℕ):ℝ)*((d*M:ℕ)+1) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hH hN) (by linarith)
  have hq0 : 0 ≤ ((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B)) := by positivity
  exact (le_mul_of_one_le_left hq0 hprod).trans (hb.trans
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Nat.cast_nonneg M) ε))))

end GoodnessAsymptotics

section UniformFiniteGoodness
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_bad_goodness_stretched_exp [Nonempty V] (G : BondGraph V E)
    (d : ℕ) (hd : 0 < d) (pbar : unitInterval) (hpbar : (pbar:ℝ) < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) :
    ∀ᶠ M : ℕ in Filter.atTop, ∀ (Q : Finset E) (x : V),
      (∀ v, (Q.filter fun e => v ∈ G e).card ≤ d) →
      ∀ p : unitInterval, p ≤ pbar →
        finiteBadGoodnessProbability G Q x M ((M:ℝ)^(1/2+ε)) p ≤
          Real.exp (-(M:ℝ)^ε) := by
  let c := max 1 (Real.sqrt ((d:ℝ)/2)/(1-pbar))
  let a := max 1 ((pbar:ℝ)/(1-pbar))
  have hc : 1 ≤ c := le_max_left ..
  have ha : 1 ≤ a := le_max_left ..
  filter_upwards [eventually_ghost_scale ε c a d hε hε1 hc ha hd] with M hM
  dsimp only at hM
  obtain ⟨hM1,hL,hh,hh2,hB,hAB,hpref⟩ := hM
  intro Q x hdeg p hpp
  have hpp' : (p:ℝ) ≤ pbar := hpp
  have hp : (p:ℝ) < 1 := hpp'.trans_lt hpbar
  let h : unitInterval := ⟨(M:ℝ)^(ε-1),hh.le,by linarith⟩
  let B := c*(M:ℝ)^(1/2-ε/4)
  let L := (M:ℝ)^(1/2+ε)
  have hodds : max 1 ((p:ℝ)/(1-p)) ≤ a := by
    apply max_le (le_max_left ..)
    have hr : (p:ℝ)/(1-p) ≤ (pbar:ℝ)/(1-pbar) :=
      div_le_div₀ pbar.2.1 hpp' (by linarith) (by linarith)
    exact hr.trans (le_max_right ..)
  have hcoeff : Real.sqrt ((d:ℝ)/2)/(1-p) ≤ c := by
    have hr : Real.sqrt ((d:ℝ)/2)/(1-p) ≤ Real.sqrt ((d:ℝ)/2)/(1-pbar) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by linarith) (by linarith)
    exact hr.trans (le_max_right ..)
  have hsqrt : 0 ≤ Real.sqrt (Real.log (1/(h:ℝ))/h) := Real.sqrt_nonneg _
  have hqbar := ghost_ratio_le_one M d hM1 hd h B L a ε hh hh2
    (le_trans zero_le_one ha) hpref
  have hqcmp : ((d*M:ℕ):ℝ)*max 1 ((p:ℝ)/(1-p))*Real.exp (-L/(16*B)) ≤
      ((d*M:ℕ):ℝ)*a*Real.exp (-L/(16*B)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hodds (Nat.cast_nonneg _)) (Real.exp_nonneg _)
  have hg := finiteBadGoodnessProbability_geometric G Q x M d L (Nat.mul_le_mul hd hM1)
    hL hd hdeg p h hp hh (by dsimp [h]; linarith) B hB
    ((mul_le_mul_of_nonneg_right hcoeff hsqrt).trans hAB) (hqcmp.trans hqbar)
  refine hg.trans ((mul_le_mul_of_nonneg_left hqcmp ?_).trans hpref)
  have hnon : 0 ≤ 1-(h:ℝ) := sub_nonneg.mpr h.2.2
  positivity

end UniformFiniteGoodness

section ClusterLocality
attribute [local instance] Classical.propDecidable Classical.decEq

theorem reachBall_le_step (G : BondGraph V E) (x : V) (n : ℕ) :
    reachBall G x n ⊆ reachBall G x (n+1) := fun _ h => Or.inl h

theorem reachBall_mono_local (G : BondGraph V E) (x : V) : Monotone (reachBall G x) :=
  monotone_nat_of_le_succ (reachBall_le_step G x)

theorem walk_mem_reachBall (G : BondGraph V E) (ω : Set E) {a b x : V}
    (w : (openSimpleGraph G ω).Walk a b) (n : ℕ) (ha : a ∈ reachBall G x n) :
    b ∈ reachBall G x (n+w.length) := by
  induction w generalizing n with
  | nil => simpa using ha
  | @cons a z b hz w ih =>
    have hz' : z ∈ reachBall G x (n+1) := by
      apply Or.inr
      simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
      obtain ⟨e,he,hend⟩ := hz.2
      exact ⟨a,ha,e,hend⟩
    simpa only [SimpleGraph.Walk.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      using ih (n+1) hz'

 
theorem finite_cluster_subset_reachBall (G : BondGraph V E) (ω : Set E) (x : V)
    (hfin : (cluster G ω x).Finite) (M : ℕ) (hM : (cluster G ω x).ncard ≤ M) :
    cluster G ω x ⊆ reachBall G x M := by
  intro y hy
  obtain ⟨w⟩ := (conn_iff_reachable G ω x y).mp hy
  let q := w.toPath
  have hs : q.val.support.toFinset ⊆ hfin.toFinset := by
    intro z hz
    have hz' : z ∈ q.val.support := List.mem_toFinset.mp hz
    exact hfin.mem_toFinset.mpr ((conn_iff_reachable G ω x z).mpr ⟨q.val.takeUntil z hz'⟩)
  have hc : q.val.length+1 ≤ (cluster G ω x).ncard := by
    have hc := Finset.card_le_card hs
    rwa [List.toFinset_card_of_nodup q.property.support_nodup,
      SimpleGraph.Walk.length_support,← Set.ncard_eq_toFinset_card _ hfin] at hc
  have hr := walk_mem_reachBall G ω q.val 0 (Set.mem_singleton x)
  simp only [Nat.zero_add] at hr
  exact reachBall_mono_local G x (by omega) hr

 

theorem cluster_restrict_incident_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (ω : Set E) (x : V)
    (hsub : cluster G (ω ∩ (incidentSupport G hloc Λ : Set E)) x ⊆ Λ) :
    cluster G (ω ∩ (incidentSupport G hloc Λ : Set E)) x = cluster G ω x := by
  apply Set.Subset.antisymm
  · exact fun _ h => conn_mono G Set.inter_subset_left h
  · intro y hy
    induction hy with
    | refl => exact conn_refl G _ x
    | @tail a b _ hab ih =>
      obtain ⟨e,he,hend⟩ := hab
      have heQ : e ∈ incidentSupport G hloc Λ :=
        (mem_incidentSupport G hloc Λ e).mpr ⟨a,hsub ih,by simp [hend]⟩
      exact ih.tail ⟨e,⟨he,heQ⟩,hend⟩

theorem cluster_restrict_incident_of_full (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (ω : Set E) (x : V) (hsub : cluster G ω x ⊆ Λ) :
    cluster G (ω ∩ (incidentSupport G hloc Λ : Set E)) x = cluster G ω x := by
  apply cluster_restrict_incident_eq G hloc Λ ω x
  exact (fun _ h => hsub (conn_mono G Set.inter_subset_left h))

 
theorem capped_cluster_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (ω : Set E) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    ((cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M) ↔
      ((cluster G (ω ∩ (Q : Set E)) x).Finite ∧
        (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ M) := by
  dsimp only
  let Λ := (finite_reachBall hloc x M).toFinset
  let Q := incidentSupport G hloc Λ
  constructor
  · rintro ⟨hfin,hcap⟩
    have hsub : cluster G ω x ⊆ Λ := by
      simpa only [Λ,Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hfin M hcap
    rw [cluster_restrict_incident_of_full G hloc Λ ω x hsub]
    exact ⟨hfin,hcap⟩
  · rintro ⟨hfin,hcap⟩
    have hsub : cluster G (ω ∩ (Q : Set E)) x ⊆ Λ := by
      simpa only [Λ,Set.Finite.coe_toFinset] using
        finite_cluster_subset_reachBall G (ω ∩ (Q : Set E)) x hfin M hcap
    have heq := cluster_restrict_incident_eq G hloc Λ ω x hsub
    rw [heq] at hfin hcap
    exact ⟨hfin,hcap⟩

end ClusterLocality

section InfiniteGoodness
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def pivotalDistance (G : BondGraph V E) (ω : Set E) (a b : V) : ℕ :=
  {e | OpenMarkedPivotal G ω {b} a e}.ncard

 
def contactSet (G : BondGraph V E) (ω : Set E) (W : Set V) : Set E :=
  {e | e ∈ ω ∧ CutExists G W e}

 
def GoodForScale (G : BondGraph V E) (ω : Set E) (x : V) (L : ℝ) : Prop :=
  ∀ W : Finset V, (W : Set V) ⊆ cluster G ω x →
    (∀ a ∈ W, ∀ b ∈ W, Conn G (ω ∩ internalEdges G (W : Set V)) a b) →
    0 < (contactSet G ω (W : Set V)).ncard →
    ∀ a ∈ W, ∀ b ∈ W,
      (pivotalDistance G (ω ∩ internalEdges G (W : Set V)) a b : ℝ) ≤
        (contactSet G ω (W : Set V)).ncard*L

 
def CappedBadGoodness (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) (L : ℝ) : Prop :=
  (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M ∧ ¬GoodForScale G ω x L

theorem pivotalDistance_finset (G : BondGraph V E) (Q ω : Finset E) (hω : ω ⊆ Q) (a b : V) :
    pivotalDistance G (ω : Set E) a b = (pairOpenPivotals G Q a b ω).card := by
  have he : {e | OpenMarkedPivotal G (ω : Set E) {b} a e} =
      (pairOpenPivotals G Q a b ω : Set E) := by
    ext e
    simp only [Finset.mem_coe,mem_pairOpenPivotals,Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨hω h.1,h⟩,And.right⟩
  simp only [pivotalDistance,he,Set.ncard_coe_finset]

theorem contactSet_finset (G : BondGraph V E) (ω : Finset E) (W : Set V) :
    contactSet G (ω : Set E) W = (openContacts G ω W : Set E) := by
  ext e
  simp only [contactSet,openContacts,Finset.mem_coe,Finset.mem_filter,Set.mem_ofPred_eq]

theorem finiteGoodForScale_iff (G : BondGraph V E) (Q ω : Finset E) (hω : ω ⊆ Q)
    (x : V) (L : ℝ) : FiniteGoodForScale G Q x L ω ↔ GoodForScale G (ω : Set E) x L := by
  have hroot : ∀ W : Finset V, W ⊆ finiteRootComponent G ω x ↔ (W : Set V) ⊆ cluster G ω x := by
    intro W
    rw [← coe_finiteRootComponent]
    exact Finset.coe_subset.symm
  have hpiv (W : Finset V) (a b : V) := pivotalDistance_finset G Q
    (internalBonds G ω (W : Set V)) ((Finset.filter_subset _ _).trans hω) a b
  simp only [FiniteGoodForScale,GoodForScale,hroot,← coe_internalBonds,contactSet_finset,
    Set.ncard_coe_finset,hpiv]

theorem cappedBadGoodness_finset_iff (G : BondGraph V E) (Q ω : Finset E) (hω : ω ⊆ Q)
    (x : V) (M : ℕ) (L : ℝ) :
    CappedBadGoodness G (ω : Set E) x M L ↔ CappedBadGoodnessEvent G Q x M L ω := by
  have hfin := cluster_finite_of_finite_edges G ω.finite_toSet x
  simp only [CappedBadGoodness,CappedBadGoodnessEvent,hfin,true_and]
  rw [← coe_finiteRootComponent,Set.ncard_coe_finset,finiteGoodForScale_iff G Q ω hω]

 
theorem internal_config_eq_of_incident (G : BondGraph V E) (ω η : Set E) (C W : Set V)
    (hW : W ⊆ C) (he : ∀ e, (∃ v ∈ C, v ∈ G e) → (e ∈ ω ↔ e ∈ η)) :
    ω ∩ internalEdges G W = η ∩ internalEdges G W := by
  ext e
  by_cases hi : e ∈ internalEdges G W
  · have hinc : ∃ v ∈ C, v ∈ G e :=
      ⟨(G e).out.1,hW (hi _ (Sym2.out_fst_mem _)),Sym2.out_fst_mem _⟩
    simp only [Set.mem_inter_iff,hi,and_true,he e hinc]
  · simp only [Set.mem_inter_iff,hi,and_false]

theorem contacts_eq_of_incident (G : BondGraph V E) (ω η : Set E) (C W : Set V)
    (hW : W ⊆ C) (he : ∀ e, (∃ v ∈ C, v ∈ G e) → (e ∈ ω ↔ e ∈ η)) :
    contactSet G ω W = contactSet G η W := by
  ext e
  by_cases hi : CutExists G W e
  · obtain ⟨a,b,hab,ha,_⟩ := hi
    have hinc : ∃ v ∈ C, v ∈ G e := ⟨a,hW ha,by simp [hab]⟩
    simp only [contactSet,Set.mem_ofPred_eq,he e hinc]
  · simp only [contactSet,Set.mem_ofPred_eq,hi,and_false]

 
theorem goodForScale_congr (G : BondGraph V E) (ω η : Set E) (x : V) (L : ℝ)
    (hC : cluster G ω x = cluster G η x)
    (he : ∀ e, (∃ v ∈ cluster G ω x, v ∈ G e) → (e ∈ ω ↔ e ∈ η)) :
    GoodForScale G ω x L ↔ GoodForScale G η x L := by
  unfold GoodForScale
  apply forall_congr'
  intro W
  rw [← hC]
  apply forall_congr'
  intro hW
  rw [internal_config_eq_of_incident G ω η _ _ hW he,contacts_eq_of_incident G ω η _ _ hW he]

theorem goodForScale_restrict_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (ω : Set E) (x : V) (L : ℝ) (hsub : cluster G ω x ⊆ Λ) :
    GoodForScale G ω x L ↔ GoodForScale G (ω ∩ (incidentSupport G hloc Λ : Set E)) x L := by
  apply goodForScale_congr G ω _ x L
    (cluster_restrict_incident_of_full G hloc Λ ω x hsub).symm
  intro e he
  obtain ⟨v,hv,hve⟩ := he
  have hQ := (mem_incidentSupport G hloc Λ e).mpr ⟨v,hsub hv,hve⟩
  simp only [Set.mem_inter_iff,Finset.mem_coe,hQ,and_true]

 
theorem cappedBadGoodness_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (L : ℝ) (ω : Set E) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    CappedBadGoodness G ω x M L ↔ CappedBadGoodness G (ω ∩ (Q : Set E)) x M L := by
  let Λ := (finite_reachBall hloc x M).toFinset
  let Q := incidentSupport G hloc Λ
  change CappedBadGoodness G ω x M L ↔ CappedBadGoodness G (ω ∩ (Q : Set E)) x M L
  have hcap := capped_cluster_local G hloc x M ω
  change ((cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M) ↔
    ((cluster G (ω ∩ (Q : Set E)) x).Finite ∧ (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ M) at hcap
  have hg : ((cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M) →
      (GoodForScale G ω x L ↔ GoodForScale G (ω ∩ (Q : Set E)) x L) := by
    rintro ⟨hfin,hM⟩
    apply goodForScale_restrict_incident G hloc Λ ω x L
    simpa only [Λ,Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hfin M hM
  constructor
  · rintro ⟨hfin,hM,hbad⟩
    exact ⟨(hcap.mp ⟨hfin,hM⟩).1,(hcap.mp ⟨hfin,hM⟩).2,fun hh => hbad ((hg ⟨hfin,hM⟩).mpr hh)⟩
  · rintro ⟨hfin,hM,hbad⟩
    have hc := hcap.mpr ⟨hfin,hM⟩
    exact ⟨hc.1,hc.2,fun hh => hbad ((hg hc).mp hh)⟩

end InfiniteGoodness

section GoodnessLaw
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurableSet_finite_restriction (Q : Finset E) (A : Set (Set E)) :
    MeasurableSet {ω : Set E | ω ∩ (Q : Set E) ∈ A} := by
  have hm : MeasurableSet {η : Set (Q : Set E) | (Subtype.val '' η : Set E) ∈ A} := .of_discrete
  convert hm.preimage (measurable_set_restrict (Q : Set E)) using 1
  ext ω
  have he : (Subtype.val '' (Subtype.val ⁻¹' ω : Set (Q : Set E)) : Set E) = ω ∩ (Q : Set E) := by
    ext e
    simp [and_comm]
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,he]

theorem measurableSet_cappedBadGoodness (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (L : ℝ) : MeasurableSet {ω | CappedBadGoodness G ω x M L} := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
  have he : {ω | CappedBadGoodness G ω x M L} =
      {ω | ω ∩ (Q : Set E) ∈ {η | CappedBadGoodness G η x M L}} := by
    ext ω
    exact cappedBadGoodness_local G hloc x M L ω
  rw [he]
  exact measurableSet_finite_restriction Q _

 
theorem bad_goodness_law_eq_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (L : ℝ) (p : unitInterval) :
    (law p).real {ω | CappedBadGoodness G ω x M L} =
      finiteBadGoodnessProbability G
        (incidentSupport G hloc (finite_reachBall hloc x M).toFinset) x M L p := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
  have he : finiteBadGoodnessProbability G Q x M L p =
      finiteEventPolynomial Q {ω | CappedBadGoodness G ω x M L} p := by
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [Set.mem_ofPred_eq,cappedBadGoodness_finset_iff G Q ω hω]
  change _ = finiteBadGoodnessProbability G Q x M L p
  rw [he,finiteEventPolynomial_restrict]
  congr 1
  ext ω
  exact cappedBadGoodness_local G hloc x M L ω

theorem incident_filter_card_le_degree (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (x : V) : (Q.filter fun e => x ∈ G e).card ≤ degree G x := by
  let : Fintype (Step G x) := (finite_steps G hloc x).fintype
  have hex (e : {e // e ∈ Q.filter fun e => x ∈ G e}) : ∃ y, G e.val = s(x,y) :=
    Sym2.mem_iff_exists.mp (Finset.mem_filter.mp e.property).2
  let f : {e // e ∈ Q.filter fun e => x ∈ G e} → Step G x :=
    fun e => ⟨(e.val,(hex e).choose),(hex e).choose_spec⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : Step G x => z.val.1) hab)
  simpa only [degree,Nat.card_eq_fintype_card,Fintype.card_coe] using Fintype.card_le_of_injective f hf

 

theorem bad_goodness_stretched_exp [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (pbar : unitInterval) (hpbar : (pbar:ℝ) < 1) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) :
    ∀ᶠ M : ℕ in Filter.atTop, ∀ x : V, ∀ p : unitInterval, p ≤ pbar →
      (law p).real {ω | CappedBadGoodness G ω x M ((M:ℝ)^(1/2+ε))} ≤
        Real.exp (-(M:ℝ)^ε) := by
  obtain ⟨d,hd,hdeg⟩ := exists_degree_bound G hqt
  filter_upwards [finite_bad_goodness_stretched_exp G d hd pbar hpbar ε hε hε1] with M hM
  intro x p hp
  rw [bad_goodness_law_eq_finite G hloc]
  exact hM _ x (fun v => (incident_filter_card_le_degree G hloc _ v).trans (hdeg v)) p hp

end GoodnessLaw

end Percolation

end OAI
