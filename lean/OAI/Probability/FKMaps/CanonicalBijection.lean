import OAI.Probability.FKMaps.InventoryDrift
import OAI.Probability.FKMaps.Matching
import OAI.Probability.FKMaps.TourActivity

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Chords
variable {n : ℕ}

lemma sameCycle_edge_out (a p : Perm (Dart n)) (ha : Function.Involutive a) (y : Dart n) :
    p.SameCycle (orbit a y).out (a (orbit a y).out) ↔ p.SameCycle y (a y) := by
  rcases (MapFinite.mk_eq_iff_involution a ha y (orbit a y)).mp rfl with hh|hh
  · conv_rhs => rw [hh]
  · conv_rhs => rw [hh,ha]
    exact ⟨SameCycle.symm,SameCycle.symm⟩

lemma orbit_opener_injective (a : Perm (Dart n)) (ha : Function.Involutive a) :
    Function.Injective (fun x : Opener a => orbit a x.val) := by
  intro x y hh
  rcases (MapFinite.sameCycle_involution a ha x.val y.val).mp (Quotient.exact hh) with hh|hh
  · exact Subtype.ext hh.symm
  · have hx := x.property
    have hy := y.property
    rw [hh,ha] at hy
    exact False.elim ((not_lt_of_ge hx.le) hy)

/-- Exact fundamental-cut incidence for a selected tree edge in canonical
rooted tour order. All representative choices have been removed. -/
theorem fundamentalCross_tree_chord (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (T : Finset (Orbit a)) (hT : Multiforest a s T)
    (ht : s*partialReversal a ha T=(List.finRange (2*(n+1))).formPerm)
    (x y : Opener a) (hx : orbit a x.val∈T) (hne : x≠y) :
    FundamentalCross a s T (orbit a x.val) (orbit a y.val) ↔ Cross a x y := by
  have hneq : orbit a x.val≠orbit a y.val := fun h => hne (orbit_opener_injective a ha h)
  rw [fundamentalCross_tour_cut a s ha T hT hx hneq,ht,edgeSwap_eq a ha x.val,
    sameCycle_edge_out a _ ha y.val]
  obtain ⟨h1,h2,h3,h4⟩ := opener_endpoints_ne a ha y x hne.symm
  rw [ordered_tour_cut _ (List.pairwise_lt_finRange _) List.mem_finRange x.val (a x.val)
    x.property y.val (a y.val) h1 h2 h3 h4]
  have hx' := x.property
  have hy' := y.property
  have hv1 := Fin.val_ne_of_ne h1
  have hv2 := Fin.val_ne_of_ne h2
  have hv3 := Fin.val_ne_of_ne h3
  have hv4 := Fin.val_ne_of_ne h4
  unfold Cross
  simp only [Fin.lt_def] at hx' hy' ⊢
  omega

/-- In a genuine planar two-colour canonical tour, fundamental incidence is
exactly alternating chords. The dual maximal-orbit condition excludes
crossings between two non-tree edges. -/
theorem fundamentalCross_iff_chord (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (T : Finset (Orbit a)) (hT : Multiforest a s T)
    (ht : s*partialReversal a ha T=(List.finRange (2*(n+1))).formPerm)
    (hdual : Nat.card (Orbit (partialReversal a ha Tᶜ*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+Tᶜ.card)
    (x y : Opener a) (hne : x≠y) :
    FundamentalCross a s T (orbit a x.val) (orbit a y.val) ↔ Cross a x y := by
  by_cases hx : orbit a x.val∈T
  · exact fundamentalCross_tree_chord a s ha T hT ht x y hx hne
  by_cases hy : orbit a y.val∈T
  · rw [fundamentalCross_symm]
    exact (fundamentalCross_tree_chord a s ha T hT ht y x hy hne.symm).trans or_comm
  have hnc : ¬Cross a x y := by
    rintro (hh|hh)
    · exact ordered_no_crossing a ha _ (List.pairwise_lt_finRange _) List.mem_finRange Tᶜ hdual
        x.val y.val (Finset.mem_compl.mpr hx) (Finset.mem_compl.mpr hy) hh.1 hh.2.1 hh.2.2
    · exact ordered_no_crossing a ha _ (List.pairwise_lt_finRange _) List.mem_finRange Tᶜ hdual
        y.val x.val (Finset.mem_compl.mpr hy) (Finset.mem_compl.mpr hx) hh.1 hh.2.1 hh.2.2
  simp only [FundamentalCross,hx,hy,false_and,or_self,hnc]

end FKCRT
end


noncomputable section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

def relabelPerm (r p : Perm (Dart n)) : Perm (Dart n) := r⁻¹*p*r

lemma relabelPerm_apply (r p : Perm (Dart n)) (d : Dart n) :
    relabelPerm r p d=r.symm (p (r d)) := rfl

lemma relabelPerm_mul (r p q : Perm (Dart n)) :
    relabelPerm r (p*q)=relabelPerm r p*relabelPerm r q := by unfold relabelPerm; group

lemma relabelPerm_involutive (r a : Perm (Dart n)) (ha : Function.Involutive a) :
    Function.Involutive (relabelPerm r a) := by
  intro d
  simp only [relabelPerm_apply,Equiv.apply_symm_apply]
  rw [ha,Equiv.symm_apply_apply]

lemma relabelPerm_no_fixed (r a : Perm (Dart n)) (hf : ∀ d,a d≠d) :
    ∀ d,relabelPerm r a d≠d := by
  intro d h
  have hh := congrArg r h
  exact hf (r d) (by simpa only [relabelPerm_apply,Equiv.apply_symm_apply] using hh)

def relabelOrbit (r p : Perm (Dart n)) : Orbit (relabelPerm r p) ≃ Orbit p :=
  Quotient.congr r (by
    intro d e
    change (r⁻¹*p*r).SameCycle d e ↔ p.SameCycle (r d) (r e)
    simpa only [inv_inv] using (sameCycle_conj (g := r⁻¹) (f := p) (x := d) (y := e)))

@[simp] lemma relabelOrbit_apply (r p : Perm (Dart n)) (d : Dart n) :
    relabelOrbit r p (orbit (relabelPerm r p) d)=orbit p (r d) := rfl

lemma card_orbit_relabel (r p : Perm (Dart n)) :
    Nat.card (Orbit (relabelPerm r p))=Nat.card (Orbit p) := Nat.card_congr (relabelOrbit r p)

def relabelEdges (r a : Perm (Dart n)) (A : Finset (Orbit a)) : Finset (Orbit (relabelPerm r a)) :=
  A.map (relabelOrbit r a).symm.toEmbedding

@[simp] lemma mem_relabelEdges (r a : Perm (Dart n)) (A : Finset (Orbit a))
    (e : Orbit (relabelPerm r a)) : e∈relabelEdges r a A ↔ relabelOrbit r a e∈A := by
  simp [relabelEdges]

@[simp] lemma card_relabelEdges (r a : Perm (Dart n)) (A : Finset (Orbit a)) :
    (relabelEdges r a A).card=A.card := Finset.card_map _

lemma relabelEdges_compl (r a : Perm (Dart n)) (A : Finset (Orbit a)) :
    relabelEdges r a Aᶜ=(relabelEdges r a A)ᶜ := by ext e; simp

lemma partialReversal_relabel (r a : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) :
    partialReversal (relabelPerm r a) (relabelPerm_involutive r a ha) (relabelEdges r a A)=
      relabelPerm r (partialReversal a ha A) := by
  apply Equiv.ext
  intro d
  simp only [partialReversal_apply,mem_relabelEdges,relabelOrbit_apply,relabelPerm_apply]
  split_ifs <;> simp

lemma tourNumbering_relabel (p : Perm (Dart n)) (hp : ∀ d e,p.SameCycle d e) :
    relabelPerm (tourNumbering p hp) p=finRotate (2*(n+1)) := by
  apply Equiv.ext
  intro i
  apply (tourNumbering p hp).injective
  simpa only [relabelPerm_apply,Equiv.apply_symm_apply] using (tourNumbering_successor p hp i).symm

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Inventory
variable {n : ℕ}

lemma formPerm_finRange_eq_rotate :
    (List.finRange (2*(n+1))).formPerm=finRotate (2*(n+1)) := by
  apply Equiv.ext
  intro i
  have hh := List.formPerm_apply_getElem (List.finRange (2*(n+1))) (List.nodup_finRange _) i.val
    (by simp)
  simpa [finRotate_apply,Fin.ext_iff,Fin.val_add] using hh

/-- Every genuine rooted planar map/tree tour has a successful identified
inventory word. Its stack inverse is root-isomorphic to the initial map,
with both permutation identities (and hence the cyclic seam) literal. -/
theorem map_tour_identified_word (M : LabelledMap n) (A : Finset (Orbit M.val.1))
    (ht : ∀ d e,(M.val.2*partialReversal M.val.1 M.property.1 A).SameCycle d e) :
    ∃ (r : Perm (Dart n)) (w : Dart n→TypedLetter) (E F : List (Dart n×Dart n)),
      r 0=0 ∧ stackTypedRun ((List.finRange (2*(n+1))).map w) []=some [] ∧
      Arches (List.finRange (2*(n+1))) E ∧ Arches (List.finRange (2*(n+1))) F ∧
      (endpoints (E++F)).Perm (List.finRange (2*(n+1))) ∧
      (∀ e∈E,w e.1=.burger true ∧ w e.2=.order true) ∧
      (∀ e∈F,w e.1=.burger false ∧ w e.2=.order false) ∧
      (∀ d,M.val.1 (r d)=r (turns (E++F) d)) ∧
      (∀ d,M.val.2 (r d)=r (((List.finRange (2*(n+1))).formPerm*turns E) d)) := by
  let a := M.val.1
  let s := M.val.2
  let t := s*partialReversal a M.property.1 A
  let r := tourNumbering t ht
  let a' := relabelPerm r a
  let A' := relabelEdges r a A
  have ha' := relabelPerm_involutive r a M.property.1
  have hf' := relabelPerm_no_fixed r a M.property.2.1
  have ht' : relabelPerm r t=(List.finRange (2*(n+1))).formPerm := by
    rw [formPerm_finRange_eq_rotate]
    exact tourNumbering_relabel t ht
  have hpart : partialReversal a' ha' A'=relabelPerm r (partialReversal a M.property.1 A) :=
    partialReversal_relabel r a M.property.1 A
  have hpartc : partialReversal a' ha' A'ᶜ=relabelPerm r (partialReversal a M.property.1 Aᶜ) := by
    change partialReversal (relabelPerm r a) ha' (relabelEdges r a A)ᶜ=_
    rw [← relabelEdges_compl,partialReversal_relabel]
  have hct : Nat.card (Orbit t)=1 := (card_orbit_eq_one_iff _).mpr ht
  have he : Nat.card (Orbit (partialReversal a' ha' A'*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+A'.card := by
    rw [hpart,← ht',← relabelPerm_mul,card_orbit_relabel,card_orbit_relabel,card_relabelEdges]
    rw [card_orbit_mul_comm]
    change Nat.card (Orbit ((s*partialReversal a M.property.1 A)*partialReversal a M.property.1 A))=_
    rw [reconstructed_tour,hct]
    exact (tour_edge_card M A ht).trans (Nat.add_comm _ _)
  have hf : Nat.card (Orbit (partialReversal a' ha' A'ᶜ*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+A'ᶜ.card := by
    rw [hpartc,← ht',← relabelPerm_mul,card_orbit_relabel,card_orbit_relabel,
      ← relabelEdges_compl,card_relabelEdges]
    rw [card_orbit_mul_comm]
    have hc := planar_tour_compl_card M A ht
    have hface := reconstructed_face a t M.property.1 A
    have hrec : t*partialReversal a M.property.1 A=s := reconstructed_tour a s M.property.1 A
    rw [hrec] at hface
    rw [← hface,hct]
    exact hc.trans (Nat.add_comm _ _)
  obtain ⟨hw,E,F,hE,hF,hcov,hwE,hwF,hpair,hpart'⟩ := maximal_matching_word a' ha' hf' A' he hf
  refine ⟨r,matchingWord a' A',E,F,tourNumbering_zero t ht,hw,hE,hF,hcov,hwE,hwF,?_,?_⟩
  · intro d
    rw [hpair]
    exact (r.apply_symm_apply _).symm
  · intro d
    rw [hpart',hpart,← ht',← relabelPerm_mul]
    have hrec : t*partialReversal a M.property.1 A=s := reconstructed_tour a s M.property.1 A
    rw [hrec]
    exact (r.apply_symm_apply _).symm

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Chords Inventory
variable {n : ℕ}

lemma opener_orbit_surjective (a : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) : Function.Surjective (fun x : Opener a => orbit a x.val) := by
  intro e
  by_cases h : e.out < a e.out
  · exact ⟨⟨e.out,h⟩,Quotient.out_eq e⟩
  · refine ⟨⟨a e.out,?_⟩,?_⟩
    · rw [ha]
      exact lt_of_le_of_ne (le_of_not_gt h) (hf e.out)
    · change orbit a (a e.out)=e
      rw [orbit_perm]
      exact Quotient.out_eq e

def openerOrbitEquiv (a : Perm (Dart n)) (ha : Function.Involutive a) (hf : ∀ d,a d≠d) :
    Opener a ≃ Orbit a := Equiv.ofBijective _ ⟨orbit_opener_injective a ha,opener_orbit_surjective a ha hf⟩

lemma canonical_tourNumbering (p : Perm (Dart n)) (hp : ∀ d e,p.SameCycle d e)
    (he : p=(List.finRange (2*(n+1))).formPerm) : tourNumbering p hp=1 := by
  apply (tourNumbering_unique p hp 1 rfl ?_).symm
  intro i
  rw [he,formPerm_finRange_eq_rotate]
  rfl

lemma edgeFirst_canonical (a p : Perm (Dart n)) (ha : Function.Involutive a)
    (hp : ∀ d e,p.SameCycle d e) (he : p=(List.finRange (2*(n+1))).formPerm)
    (x : Opener a) : edgeFirst a p hp (orbit a x.val)=x.val.val := by
  rw [edgeFirst,canonical_tourNumbering p hp he]
  have hh := (MapFinite.mk_eq_iff_involution a ha x.val (orbit a x.val)).mp rfl
  have hx := x.property
  rcases hh with hh|hh
  · conv_rhs => rw [hh]
    rw [hh] at hx
    exact min_eq_left hx.le
  · conv_rhs => rw [hh]
    rw [hh,ha] at hx
    exact min_eq_right hx.le

/-- The ordered fundamental activity of any edge is precisely the absence
of a later-first chord crossing. -/
theorem orderedActive_chord (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (T : Finset (Orbit a)) (hT : Multiforest a s T)
    (hp : ∀ d e,(s*partialReversal a ha T).SameCycle d e)
    (ht : s*partialReversal a ha T=(List.finRange (2*(n+1))).formPerm)
    (hdual : Nat.card (Orbit (partialReversal a ha Tᶜ*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+Tᶜ.card)
    (x : Opener a) :
    OrderedActive a s T (edgeFirst a (s*partialReversal a ha T) hp) (orbit a x.val) ↔
      ¬∃ j : Dart n,x.val < j ∧ j < a x.val ∧ a x.val < a j := by
  constructor
  · intro h ⟨j,hxj,hjx,haxj⟩
    let y : Opener a := ⟨j,(hjx.trans haxj)⟩
    have hne : x≠y := fun h => (ne_of_lt hxj) (congrArg Subtype.val h)
    apply h (orbit a y.val)
    · rw [edgeFirst_canonical a _ ha hp ht x,edgeFirst_canonical a _ ha hp ht y]
      exact hxj
    · exact (fundamentalCross_iff_chord a s ha T hT ht hdual x y hne).mpr (Or.inl ⟨hxj,hjx,haxj⟩)
  · intro h f hxf hcross
    obtain ⟨y,rfl⟩ := opener_orbit_surjective a ha hf f
    rw [edgeFirst_canonical a _ ha hp ht x,edgeFirst_canonical a _ ha hp ht y] at hxf
    have hxy : x.val < y.val := hxf
    have hne : x≠y := fun he => (ne_of_lt hxy) (congrArg Subtype.val he)
    rcases (fundamentalCross_iff_chord a s ha T hT ht hdual x y hne).mp hcross with hh|hh
    · exact h ⟨y.val,hh⟩
    · exact (not_lt_of_ge hxy.le) hh.1

/-- Counting openers or their matching closers gives the identical activity
exponent, including deterministic one-edge cases. -/
lemma sum_closers_eq_openers (a : Perm (Dart n)) (ha : Function.Involutive a) :
    (∑ i : Dart n,if a i < i ∧ ¬∃ j : Dart n,a i < j ∧ j < i ∧ i < a j then 1 else 0)=
      ∑ x : Opener a,if ¬∃ j : Dart n,x.val < j ∧ j < a x.val ∧ a x.val < a j then 1 else 0 := by
  have hswap := Equiv.sum_comp a (fun i : Dart n =>
    if a i < i ∧ ¬∃ j : Dart n,a i < j ∧ j < i ∧ i < a j then (1:ℕ) else 0)
  rw [← hswap]
  trans ∑ i : Dart n,if i < a i then
    (if ¬∃ j : Dart n,i < j ∧ j < a i ∧ a i < a j then (1:ℕ) else 0) else 0
  · apply Finset.sum_congr rfl
    intro i _
    rw [ha]
    by_cases hi : i < a i <;> simp [hi]
  · rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Chords Inventory
variable {n : ℕ}

lemma canonical_tour_maximal (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (ht : M.val.2*partialReversal M.val.1 M.property.1 T=(List.finRange (2*(n+1))).formPerm) :
    Nat.card (Orbit (partialReversal M.val.1 M.property.1 T*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+T.card ∧
    Nat.card (Orbit (partialReversal M.val.1 M.property.1 Tᶜ*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+Tᶜ.card := by
  let a := M.val.1
  let s := M.val.2
  let t := s*partialReversal a M.property.1 T
  have hp : ∀ d e,t.SameCycle d e := by
    rw [show t=(List.finRange (2*(n+1))).formPerm from ht]
    intro d e
    exact sameCycle_of_list _ (List.nodup_finRange _) (fun _ _ => rfl) (List.mem_finRange d) (List.mem_finRange e)
  have hct : Nat.card (Orbit t)=1 := (card_orbit_eq_one_iff _).mpr hp
  constructor
  · rw [← ht,card_orbit_mul_comm,reconstructed_tour,hct]
    exact (tour_edge_card M T hp).trans (Nat.add_comm _ _)
  · rw [← ht,card_orbit_mul_comm,hct]
    have hc := planar_tour_compl_card M T hp
    have hface := reconstructed_face a t M.property.1 T
    have hrec : t*partialReversal a M.property.1 T=s := reconstructed_tour a s M.property.1 T
    rw [hrec] at hface
    rw [← hface]
    exact hc.trans (Nat.add_comm _ _)

/-- The actual adaptive FK expansion exponent is the number of flexible
closing positions in the true identified word. No weight identity is assumed. -/
theorem canonical_activity_eq_flexible (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ)
    (ht : M.val.2*partialReversal M.val.1 M.property.1 T=(List.finRange (2*(n+1))).formPerm) :
    explorationActivity M.val.1 M.val.2 (tourSelector M.val.1 M.val.2 M.property.1)
      ∅ Finset.univ T (Fintype.card (Orbit M.val.1))=
      flexibleCount (List.ofFn (matchingWord M.val.1 T)) [] := by
  let a := M.val.1
  let s := M.val.2
  let ha := M.property.1
  let hf := M.property.2.1
  have hp := treeExtension_tour a s ha ∅ Finset.univ T hT
  have hforest : Multiforest a s T := (mem_treeExtensions a s ∅ Finset.univ T).mp hT |>.2.2.1
  obtain ⟨hmax,hdual⟩ := canonical_tour_maximal M T ht
  have hnc : ∀ x y : Dart n,decide (orbit a x∈T)=decide (orbit a y∈T) →
      x < y → y < a x → a x < a y → False := by
    intro x y hh hxy hyx haxy
    have hh' : (orbit a x∈T) ↔ (orbit a y∈T) := by simpa only [decide_eq_decide] using hh
    by_cases hx : orbit a x∈T
    · exact ordered_no_crossing a ha _ (List.pairwise_lt_finRange _) List.mem_finRange T hmax x y hx (hh'.mp hx) hxy hyx haxy
    · have hy : orbit a y∉T := fun h => hx (hh'.mpr h)
      exact ordered_no_crossing a ha _ (List.pairwise_lt_finRange _) List.mem_finRange Tᶜ hdual x y
        (Finset.mem_compl.mpr hx) (Finset.mem_compl.mpr hy) hxy hyx haxy
  have hw := matching_flexibleCount a ha hf (fun i => decide (orbit a i∈T))
    (fun i => by rw [orbit_perm]) hnc
  change flexibleCount (List.ofFn (matchingWord a T)) []=_ at hw
  rw [tourActivity_eq_card M.val.1 M.val.2 M.property.1 T hT,hw,sum_closers_eq_openers a ha]
  have he := Equiv.sum_comp (openerOrbitEquiv a ha hf)
    (fun e : Orbit a => if OrderedActive a s T (edgeFirst a (s*partialReversal a ha T) hp) e then (1:ℕ) else 0)
  rw [Finset.card_filter]
  rw [← he]
  apply Finset.sum_congr rfl
  intro x _
  have hh := orderedActive_chord a s ha hf T hforest hp ht hdual x
  change (if OrderedActive a s T (edgeFirst a (s*partialReversal a ha T) hp) (orbit a x.val) then 1 else 0)=_
  rw [hh]
  split_ifs <;> rfl

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
open MapCycles Inventory
variable {n : ℕ}

/-- Literal rooted-tour normal form, not a map with an assumed word inverse. -/
structure CanonicalTreeMap (n : ℕ) where
  a : Perm (Dart n)
  s : Perm (Dart n)
  A : Finset (Orbit a)
  valid : MapConditions (a,s)
  tour : s*partialReversal a valid.1 A=(List.finRange (2*(n+1))).formPerm

abbrev SuccessfulWord (n : ℕ) := {w : Dart n→TypedLetter //
  stackTypedRun ((List.finRange (2*(n+1))).map w) []=some []}

def CanonicalTreeMap.word (X : CanonicalTreeMap n) : SuccessfulWord n :=
  ⟨matchingWord X.a X.A,by
    have hh := canonical_tour_maximal ⟨(X.a,X.s),X.valid⟩ X.A X.tour
    exact (maximal_matching_word X.a X.valid.1 X.valid.2.1 X.A hh.1 hh.2).1⟩

lemma matchingWord_color (a : Perm (Dart n)) (A : Finset (Orbit a)) (i : Dart n) :
    (matchingWord a A i).color=decide (orbit a i∈A) := by
  unfold matchingWord
  split_ifs <;> rfl

lemma matchingWord_set_injective (a : Perm (Dart n)) :
    Function.Injective (matchingWord a) := by
  intro A B h
  apply Finset.ext
  intro e
  induction e using Quotient.inductionOn with
  | _ i =>
    have hh := congrArg (fun w => (w i).color) h
    change orbit a i∈A ↔ orbit a i∈B
    simpa only [matchingWord_color,decide_eq_decide] using hh

lemma CanonicalTreeMap.word_injective : Function.Injective (@CanonicalTreeMap.word n) := by
  intro X Y h
  have hw : matchingWord X.a X.A=matchingWord Y.a Y.A := congrArg Subtype.val h
  have hX := canonical_tour_maximal ⟨(X.a,X.s),X.valid⟩ X.A X.tour
  have hY := canonical_tour_maximal ⟨(Y.a,Y.s),Y.valid⟩ Y.A Y.tour
  obtain ⟨_,E,F,he,hf,hc,htE,htF,ha,hp⟩ :=
    maximal_matching_word X.a X.valid.1 X.valid.2.1 X.A hX.1 hX.2
  obtain ⟨_,E',F',he',hf',hc',htE',htF',ha',hp'⟩ :=
    maximal_matching_word Y.a Y.valid.1 Y.valid.2.1 Y.A hY.1 hY.2
  rw [← hw] at htE' htF'
  have hu := typed_map_unique (matchingWord X.a X.A) _ (List.nodup_finRange _) E F E' F'
    he hf he' hf' hc hc' htE htF htE' htF'
  have haeq : X.a=Y.a := ha.symm.trans (hu.1.trans ha')
  cases X with
  | mk a s A hv ht =>
    cases Y with
    | mk a' s' A' hv' ht' =>
      dsimp only at haeq hw
      subst a'
      have hA : A=A' := matchingWord_set_injective a hw
      subst A'
      have hs : s=s' := mul_right_cancel (ht.trans ht'.symm)
      subst s'
      rfl

lemma matchingWord_of_matchings (w : Dart n→TypedLetter)
    (E F : List (Dart n×Dart n))
    (hE : Arches (List.finRange (2*(n+1))) E)
    (hF : Arches (List.finRange (2*(n+1))) F)
    (hc : (endpoints (E++F)).Perm (List.finRange (2*(n+1))))
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false) :
    matchingWord (turns (E++F)) (matchingEdges E F)=w := by
  have hn : (endpoints (E++F)).Nodup := hc.nodup_iff.mpr (List.nodup_finRange _)
  have hdis : List.Disjoint (endpoints E) (endpoints F) := by
    rw [endpoints_append,List.nodup_append] at hn
    exact fun d hd hd' => hn.2.2 d hd d hd' rfl
  funext i
  obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp (hc.mem_iff.mpr (List.mem_finRange i))
  · simp only [matchingWord,(turns_pair hn e he).1,mem_matchingEdges E F hn]
    rcases List.mem_append.mp he with he|he
    · rw [ite_eq_left (hE.increasing (List.pairwise_lt_finRange _) e he),
        decide_eq_true (mem_endpoints.mpr ⟨e,he,Or.inl rfl⟩), (htE e he).1]
    · rw [ite_eq_left (hF.increasing (List.pairwise_lt_finRange _) e he),
        decide_eq_false (fun hx => hdis hx (mem_endpoints.mpr ⟨e,he,Or.inl rfl⟩)),(htF e he).1]
  · simp only [matchingWord,(turns_pair hn e he).2,mem_matchingEdges E F hn]
    rcases List.mem_append.mp he with he|he
    · rw [ite_eq_right (not_lt_of_ge (hE.increasing (List.pairwise_lt_finRange _) e he).le),
        decide_eq_true (mem_endpoints.mpr ⟨e,he,Or.inr rfl⟩),(htE e he).2]
    · rw [ite_eq_right (not_lt_of_ge (hF.increasing (List.pairwise_lt_finRange _) e he).le),
        decide_eq_false (fun hx => hdis hx (mem_endpoints.mpr ⟨e,he,Or.inr rfl⟩)),(htF e he).2]

lemma CanonicalTreeMap.word_surjective : Function.Surjective (@CanonicalTreeMap.word n) := by
  intro w
  obtain ⟨E,F,hE,hF,hc,htE,htF⟩ := identified_matchings w.val w.property
  have hv := matching_map_conditions E F hE hF hc
  have hn : (endpoints (E++F)).Nodup := hc.nodup_iff.mpr (List.nodup_finRange _)
  have ht : ((List.finRange (2*(n+1))).formPerm*turns E)*
      partialReversal (turns (E++F)) hv.1 (matchingEdges E F)=
      (List.finRange (2*(n+1))).formPerm := by
    rw [partialReversal_matchingEdges E F hn,mul_assoc,
      turns_self (by rw [endpoints_append] at hn; exact hn.of_append_left),mul_one]
  refine ⟨⟨_,_,_,hv,ht⟩,Subtype.ext ?_⟩
  exact matchingWord_of_matchings w.val E F hE hF hc htE htF

/-- Exact finite bimapping of the genuine canonical rooted planar tree maps
and successful typed words; no symmetry divisor and no assumed inverse. -/
def canonicalWordEquiv (n : ℕ) : CanonicalTreeMap n ≃ SuccessfulWord n :=
  Equiv.ofBijective CanonicalTreeMap.word
    ⟨CanonicalTreeMap.word_injective,CanonicalTreeMap.word_surjective⟩

end FKCRT
end

end OAI
