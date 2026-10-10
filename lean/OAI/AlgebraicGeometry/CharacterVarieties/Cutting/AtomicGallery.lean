import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.AtomicFrames

namespace OAI

/-!
# Atom-conserving galleries associated with a common refinement of two flags.

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type} {A : Type*}

/-- The occupancy of a specified old simultaneous basis atom in a facet. -/
def atomWeight (s : F → Set A) (t : A) (f : F) : ℕ := if t∈s f then 1 else 0

namespace Decoration
variable {k : Kind} (d : Decoration k F) (s : F → Set A)

/-- Occurrence-sensitive atom conservation, stronger than dimension conservation. -/
def AtomConservative : Prop := ∀ t, d.Conservative (atomWeight s t)

lemma atom_sum (h : d.AtomConservative s) (p : k.table.Port) (t : A) :
    (if t∈s (d.color ⟨p,none⟩) then 1 else 0 : ℕ) =
      Fintype.card {c : k.table.Child p // t∈s (d.color ⟨p,some c⟩)} := by
  have H := (d.conservative_iff (atomWeight s t)).mp (h t) p
  simpa [atomWeight,Finset.sum_boole,Fintype.card_subtype] using H

/-- A checked literal partition, derived from atom conservation at all ports.
No coverage hypothesis about solution varieties is introduced here. -/
def atomicData (h : d.AtomConservative s) : AtomicData k A where
  atoms z := s (d.color z)
  corner z := congrArg s (d.corner z)
  child_subset p c t ht := by
    by_contra hn
    have H : Fintype.card {j : k.table.Child p // t∈s (d.color ⟨p,some j⟩)}=0 := by
      simpa only [ite_eq_right hn] using (d.atom_sum s h p t).symm
    have : IsEmpty {j : k.table.Child p // t∈s (d.color ⟨p,some j⟩)} :=
      Fintype.card_eq_zero_iff.mp H
    exact isEmptyElim (⟨c,ht⟩ : {j : k.table.Child p // t∈s (d.color ⟨p,some j⟩)})
  partition p t ht := by
    have H : Fintype.card {j : k.table.Child p // t∈s (d.color ⟨p,some j⟩)}=1 := by
      simpa only [ite_eq_left ht] using (d.atom_sum s h p t).symm
    obtain ⟨c,hc⟩ := Fintype.card_eq_one_iff.mp H
    exact ⟨c.val,c.property,fun j hj => congrArg Subtype.val (hc ⟨j,hj⟩)⟩

end Decoration

namespace RankedChain
variable {F : Type} {r : F → ℕ} {parent : F}

/-- Additional conservation on the same concrete ranked program. -/
def ForRank (q : F → ℕ) : {a b : List F} → RankedChain r parent a b → Prop
  | _,_,.refl _ => True
  | _,_,.step s _ p => s.decoration.Conservative q ∧ p.ForRank q

lemma forRank_trans {a b c : List F} (p : RankedChain r parent a b)
    (z : RankedChain r parent b c) (q : F → ℕ)
    (hp : p.ForRank q) (hz : z.ForRank q) : (p.trans z).ForRank q := by
  induction p with
  | refl a => exact hz
  | step s hs p ih => exact ⟨hp.1,ih z hp.2 hz⟩

lemma forRank_single {a b : List F} (s : OrderedStep parent a b)
    (hs : s.decoration.Conservative r) (q : F → ℕ)
    (hq : s.decoration.Conservative q) : (single s hs).ForRank q := ⟨hq,trivial⟩

lemma forRank_walk {a b : List F} (p : RankedChain r parent a b) (q : F → ℕ)
    (h : p.ForRank q) : p.forget.walk.Conservative (r:=q) := by
  induction p with
  | refl a => intro j; exact Fin.elim0 j
  | step s hs p ih => exact OrderedWalk.conservative_cons s p.forget.walk h.1 (ih h.2)

lemma forRank_reindex {F : Type} {N : ℕ} {r : F → ℕ}
    {a b a' b' : List (Option F)} (p : RankedChain (freshRank N r) none a b)
    (ha : a=a') (hb : b=b') (q : Option F → ℕ) (h : p.ForRank q) :
    (p.reindex ha hb).ForRank q := by
  subst a'; subst b'; exact h

end RankedChain
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
end

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F I : Type}

/-- The same fresh, crossing-free gallery conserves every labeled weight.
Weights are instantiated below by atom occupancies; hence this records actual
partitions and not only the numerical rank equation. -/
def WeightedCleanGallery (N : ℕ) (r : F → ℕ) (M : I → ℕ) (w : I → F → ℕ)
    (a b : List F) : Prop :=
  ∃ p : RankedChain (freshRank N r) none (a.map some) (b.map some),
    p.Fresh ∧ p.crossings=[] ∧ ∀ i, p.ForRank (freshRank (M i) (w i))
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F I : Type} {N : ℕ} {r : F → ℕ} {M : I → ℕ} {w : I → F → ℕ}

namespace WeightedCleanGallery
lemma refl (a : List F) : WeightedCleanGallery N r M w a a := ⟨.refl _,trivial,rfl,fun _ => trivial⟩
lemma trans {a b c : List F} (p : WeightedCleanGallery N r M w a b) (q : WeightedCleanGallery N r M w b c) :
    WeightedCleanGallery N r M w a c := by
  obtain ⟨p,hp,hpc,hpw⟩ := p
  obtain ⟨q,hq,hqc,hqw⟩ := q
  exact ⟨p.trans q,p.fresh_trans q hp hq,by rw [RankedChain.crossings_trans,hpc,hqc]; rfl,
    fun i => p.forRank_trans q _ (hpw i) (hqw i)⟩

lemma split (big : F) (left mid right : List F)
    (hp : N = listRank r (left ++ big :: right)) (hm : r big = listRank r mid)
    (hwp : ∀ i, M i = listRank (w i) (left ++ big :: right))
    (hwm : ∀ i, w i big = listRank (w i) mid) :
    WeightedCleanGallery N r M w (left ++ big :: right) (left ++ (mid ++ right)) := by
  have hp' : freshRank N r none = listRank (freshRank N r)
      (left.map some ++ some big :: right.map some) := by
    simpa only [← List.map_cons, ← List.map_append, listRank_some, freshRank] using hp
  have hm' : freshRank N r (some big) = listRank (freshRank N r) (mid.map some) := by
    simpa only [listRank_some, freshRank] using hm
  let c := RankedChain.split (some big) (left.map some) (mid.map some) (right.map some) hp' hm'
  have h : c.Fresh := by
    refine RankedChain.fresh_single _ _ ?_
    refine ⟨(big, (fun j => left.get (Fin.cast (List.length_map ..) j)),
      (fun j => mid.get (Fin.cast (List.length_map ..) j)),
      (fun j => right.get (Fin.cast (List.length_map ..) j))), ?_⟩
    simp only [OrderedStep.split, splitLists, Kind.freshDecoration]
    congr 1 <;> funext j <;> simp [List.get_eq_getElem]
  let p : RankedChain (freshRank N r) none ((left ++ big :: right).map some)
      ((left ++ (mid ++ right)).map some) := c.reindex (by simp only [List.map_append,List.map_cons])
    (by simp only [List.map_append])
  refine ⟨p,c.reindex_fresh _ _ h,by rw [RankedChain.reindex_crossings]; rfl,?_⟩
  intro i
  apply c.forRank_reindex
  apply RankedChain.forRank_single
  apply splitLists_conservative
  · simpa only [← List.map_cons,← List.map_append,listRank_some,freshRank] using hwp i
  · simpa only [listRank_some,freshRank] using hwm i

lemma merge (big : F) (left mid right : List F)
    (hp : N = listRank r (left ++ big :: right)) (hm : r big = listRank r mid)
    (hwp : ∀ i, M i = listRank (w i) (left ++ big :: right))
    (hwm : ∀ i, w i big = listRank (w i) mid) :
    WeightedCleanGallery N r M w (left ++ (mid ++ right)) (left ++ big :: right) := by
  have hp' : freshRank N r none = listRank (freshRank N r)
      (left.map some ++ some big :: right.map some) := by
    simpa only [← List.map_cons, ← List.map_append, listRank_some, freshRank] using hp
  have hm' : freshRank N r (some big) = listRank (freshRank N r) (mid.map some) := by
    simpa only [listRank_some, freshRank] using hm
  let c := RankedChain.merge (some big) (left.map some) (mid.map some) (right.map some) hp' hm'
  have h : c.Fresh := by
    refine RankedChain.fresh_single _ _ ?_
    refine ⟨(big, (fun j => left.get (Fin.cast (List.length_map ..) j)),
      (fun j => mid.get (Fin.cast (List.length_map ..) j)),
      (fun j => right.get (Fin.cast (List.length_map ..) j))), ?_⟩
    simp only [OrderedStep.merge, splitLists, Kind.freshDecoration]
    congr 1 <;> funext j <;> simp [List.get_eq_getElem]
  let p : RankedChain (freshRank N r) none ((left ++ (mid ++ right)).map some)
      ((left ++ big :: right).map some) := c.reindex (by simp only [List.map_append])
    (by simp only [List.map_append,List.map_cons])
  refine ⟨p,c.reindex_fresh _ _ h,by rw [RankedChain.reindex_crossings]; rfl,?_⟩
  intro i
  apply c.forRank_reindex
  apply RankedChain.forRank_single
  apply splitLists_conservative
  · simpa only [← List.map_cons,← List.map_append,listRank_some,freshRank] using hwp i
  · simpa only [listRank_some,freshRank] using hwm i

end WeightedCleanGallery
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F I : Type} {N : ℕ} {r : F → ℕ} {M : I → ℕ} {w : I → F → ℕ}
namespace WeightedCleanGallery

lemma refine_rows (rows : List (F × List F)) (left right : List F)
    (hp : N=listRank r (left++(rows.map Prod.fst++right)))
    (hr : ∀ x∈rows,r x.1=listRank r x.2)
    (hwp : ∀ i,M i=listRank (w i) (left++(rows.map Prod.fst++right)))
    (hwr : ∀ i x,x∈rows → w i x.1=listRank (w i) x.2) :
    WeightedCleanGallery N r M w (left++(rows.map Prod.fst++right))
      (left++(rows.flatMap Prod.snd++right)) ∧
    WeightedCleanGallery N r M w (left++(rows.flatMap Prod.snd++right))
      (left++(rows.map Prod.fst++right)) := by
  induction rows generalizing left with
  | nil => exact ⟨refl _,refl _⟩
  | cons x rows ih =>
    have hx := hr x (by simp)
    have ht : ∀ y∈rows,r y.1=listRank r y.2 := fun y hy => hr y (by simp [hy])
    have hp' : N=listRank r ((left++x.2)++(rows.map Prod.fst++right)) := by
      simpa only [List.map_cons,listRank_append,listRank_cons,hx,add_assoc] using hp
    have hwx : ∀ i,w i x.1=listRank (w i) x.2 := fun i => hwr i x (by simp)
    have hwt : ∀ i y,y∈rows → w i y.1=listRank (w i) y.2 :=
      fun i y hy => hwr i y (by simp [hy])
    have hwp' : ∀ i,M i=listRank (w i) ((left++x.2)++(rows.map Prod.fst++right)) := by
      intro i
      simpa only [List.map_cons,listRank_append,listRank_cons,hwx i,add_assoc] using hwp i
    obtain ⟨p,q⟩ := ih (left++x.2) hp' ht hwp' hwt
    constructor
    · have h := (split x.1 left x.2 (rows.map Prod.fst++right) hp hx hwp hwx).trans
        (by simpa only [List.append_assoc] using p)
      simpa only [List.map_cons,List.flatMap_cons,List.cons_append,List.append_assoc] using h
    · have h := q.trans (by simpa only [List.append_assoc] using
        (merge x.1 left x.2 (rows.map Prod.fst++right) hp hx hwp hwx))
      simpa only [List.map_cons,List.flatMap_cons,List.cons_append,List.append_assoc] using h

end WeightedCleanGallery
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.DirectedSort.Program
open scoped Classical
open OccurrenceIncidence.VertexTable
variable {α F : Type} [LinearOrder α] {a b : List α} {N : ℕ} {r : F → ℕ}

/-- The original no-recrossing program conserves each atom on the very same
literal passage, not on a separately chosen permutation word. -/
lemma ranked_forRank (f : α → F) (p : Program a b) (hp : N=listRank r (a.map f))
    (M : ℕ) (w : F → ℕ) (hw : M=listRank w (a.map f)) :
    (p.ranked f hp).ForRank (freshRank M w) := by
  induction p with
  | refl a => trivial
  | step l x y rt hyx p ih =>
    change (OrderedStep.adjacent none ((l.map f).map some) (some (f x)) (some (f y))
      ((rt.map f).map some)).decoration.Conservative (freshRank M w) ∧ _
    constructor
    · apply OrderedStep.adjacent_conservative
      simpa only [←List.map_cons,←List.map_append,listRank_some,freshRank] using hw
    · apply ih
      simpa only [List.map_append,List.map_cons,listRank_append,listRank_cons,
        add_comm,add_left_comm,add_assoc] using hw
end IntegralCharacterVarieties.DirectedSort.Program

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F I : Type} {N : ℕ} {r : F → ℕ} {M : I → ℕ} {w : I → F → ℕ}

/-- A fresh, directed/no-recrossing family-conserving gallery. -/
def WeightedReducedGallery (N : ℕ) (r : F → ℕ) (M : I → ℕ) (w : I → F → ℕ)
    (a b : List F) : Prop :=
  ∃ p : RankedChain (freshRank N r) none (a.map some) (b.map some),
    p.Fresh ∧ p.crossings.Nodup ∧ ∀ i,p.ForRank (freshRank (M i) (w i))

namespace WeightedReducedGallery
lemma clean_left {a b c : List F} (p : WeightedCleanGallery N r M w a b)
    (q : WeightedReducedGallery N r M w b c) : WeightedReducedGallery N r M w a c := by
  obtain ⟨p,hp,hpc,hpw⟩ := p
  obtain ⟨q,hq,hqc,hqw⟩ := q
  refine ⟨p.trans q,p.fresh_trans q hp hq,?_,fun i => p.forRank_trans q _ (hpw i) (hqw i)⟩
  rw [RankedChain.crossings_trans,hpc]
  exact hqc

lemma clean_right {a b c : List F} (p : WeightedReducedGallery N r M w a b)
    (q : WeightedCleanGallery N r M w b c) : WeightedReducedGallery N r M w a c := by
  obtain ⟨p,hp,hpc,hpw⟩ := p
  obtain ⟨q,hq,hqc,hqw⟩ := q
  refine ⟨p.trans q,p.fresh_trans q hp hq,?_,fun i => p.forRank_trans q _ (hpw i) (hqw i)⟩
  rw [RankedChain.crossings_trans,hqc,List.append_nil]
  exact hpc

end WeightedReducedGallery
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F I : Type} {N : ℕ} {r : F → ℕ} {M : I → ℕ} {w : I → F → ℕ}
namespace WeightedReducedGallery
lemma rectangular {m n : ℕ} (f : Fin m → Fin n → F)
    (hinj : Function.Injective (fun p : Fin m × Fin n => f p.1 p.2))
    (hf : N = listRank r ((List.ofFn fun i => List.ofFn (f i)).flatten))
    (hw : ∀ t,M t=listRank (w t) ((List.ofFn fun i => List.ofFn (f i)).flatten)) :
    WeightedReducedGallery N r M w ((List.ofFn fun i => List.ofFn (f i)).flatten)
      ((List.ofFn fun j => List.ofFn fun i => f i j).flatten) := by
  let e := gridTranspose m n
  let g : Fin (n*m) → F := fun k => f (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
  have hg : Function.Injective g := by
    intro x y h
    have hxy := @hinj ((finProdFinEquiv.symm x).2,(finProdFinEquiv.symm x).1)
      ((finProdFinEquiv.symm y).2,(finProdFinEquiv.symm y).1) h
    apply finProdFinEquiv.symm.injective
    exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
  have ha : (List.ofFn e).map g = (List.ofFn fun i => List.ofFn (f i)).flatten := by
    rw [List.map_ofFn]
    have H : (fun k : Fin (m*n) => g (e k)) =
        (fun k : Fin (m*n) => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
      funext k
      change f (finProdFinEquiv.symm (finProdFinEquiv
        ((finProdFinEquiv.symm k).2,(finProdFinEquiv.symm k).1))).2
        (finProdFinEquiv.symm (finProdFinEquiv
        ((finProdFinEquiv.symm k).2,(finProdFinEquiv.symm k).1))).1 = _
      rw [Equiv.symm_apply_apply]
    change List.ofFn (fun k => g (e k)) = _
    rw [H,matrix_list]
  have hb : (List.finRange (n*m)).map g =
      (List.ofFn fun j => List.ofFn fun i => f i j).flatten := by
    rw [← List.ofFn_id,List.map_ofFn]
    exact matrix_list (fun j i => f i j)
  obtain ⟨p,hp⟩ := DirectedSort.Program.sort_equiv e
  have hrank : N = listRank r ((List.ofFn e).map g) := ha.symm ▸ hf
  let q := p.ranked g hrank
  let q' : RankedChain (freshRank N r) none
      (((List.ofFn fun i => List.ofFn (f i)).flatten).map some)
      (((List.ofFn fun j => List.ofFn fun i => f i j).flatten).map some) :=
    q.reindex (congrArg (List.map some) ha) (congrArg (List.map some) hb)
  refine ⟨q',q.reindex_fresh _ _ (p.ranked_fresh g hrank),?_,?_⟩
  · rw [RankedChain.reindex_crossings]
    exact p.ranked_no_recrossing g hg hrank hp
  · intro t
    apply q.forRank_reindex
    exact p.ranked_forRank g hrank (M t) (w t) (ha.symm ▸ hw t)

end WeightedReducedGallery
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F I : Type} {N : ℕ} {r : F → ℕ} {M : I → ℕ} {w : I → F → ℕ}
namespace WeightedReducedGallery

/-- The lower gallery is produced with both ordinary ranks and every atom
occupancy conserved, while retaining the literal fresh/no-recrossing program. -/
theorem two_flag_gallery {m n : ℕ} (row : Fin m → F) (col : Fin n → F)
    (grid : Fin m → Fin n → F)
    (hinj : Function.Injective (fun p : Fin m × Fin n => grid p.1 p.2))
    (hp : N=∑ i,r (row i))
    (hr : ∀ i,r (row i)=∑ j,r (grid i j))
    (hc : ∀ j,r (col j)=∑ i,r (grid i j))
    (hwp : ∀ t,M t=∑ i,w t (row i))
    (hwr : ∀ t i,w t (row i)=∑ j,w t (grid i j))
    (hwc : ∀ t j,w t (col j)=∑ i,w t (grid i j)) :
    WeightedReducedGallery N r M w (List.ofFn row) (List.ofFn col) := by
  have hpc : N=∑ j,r (col j) := by
    rw [hp]
    simp_rw [hr,hc]
    exact Finset.sum_comm
  have hwpc : ∀ t,M t=∑ j,w t (col j) := by
    intro t
    rw [hwp t]
    simp_rw [hwr t,hwc t]
    exact Finset.sum_comm
  have Hrows : ∀ x∈(List.ofFn fun i => (row i,List.ofFn (grid i))),
      r x.1=listRank r x.2 := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    simpa only [listRank_ofFn] using hr i
  have Hcols : ∀ x∈(List.ofFn fun j => (col j,List.ofFn fun i => grid i j)),
      r x.1=listRank r x.2 := by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    simpa only [listRank_ofFn] using hc j
  have HWrows : ∀ t x,x∈(List.ofFn fun i => (row i,List.ofFn (grid i))) →
      w t x.1=listRank (w t) x.2 := by
    intro t x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    simpa only [listRank_ofFn] using hwr t i
  have HWcols : ∀ t x,x∈(List.ofFn fun j => (col j,List.ofFn fun i => grid i j)) →
      w t x.1=listRank (w t) x.2 := by
    intro t x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    simpa only [listRank_ofFn] using hwc t j
  have hrow := (WeightedCleanGallery.refine_rows
    (List.ofFn fun i => (row i,List.ofFn (grid i))) [] []
    (by simpa only [List.nil_append,List.append_nil,List.map_ofFn,Function.comp_apply,listRank_ofFn] using hp)
    Hrows
    (by simpa only [List.nil_append,List.append_nil,List.map_ofFn,Function.comp_apply,listRank_ofFn] using hwp)
    HWrows).1
  have hcol := (WeightedCleanGallery.refine_rows
    (List.ofFn fun j => (col j,List.ofFn fun i => grid i j)) [] []
    (by simpa only [List.nil_append,List.append_nil,List.map_ofFn,Function.comp_apply,listRank_ofFn] using hpc)
    Hcols
    (by simpa only [List.nil_append,List.append_nil,List.map_ofFn,Function.comp_apply,listRank_ofFn] using hwpc)
    HWcols).2
  simp only [List.nil_append,List.append_nil,List.flatMap_def,List.map_ofFn] at hrow hcol
  have hgrid : N=listRank r ((List.ofFn fun i => List.ofFn (grid i)).flatten) := by
    simp only [listRank_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_apply,listRank_ofFn]
    simpa only [hr] using hp
  have hwgrid : ∀ t,M t=listRank (w t) ((List.ofFn fun i => List.ofFn (grid i)).flatten) := by
    intro t
    simp only [listRank_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_apply,listRank_ofFn]
    simpa only [hwr t] using hwp t
  exact clean_left hrow (clean_right (rectangular grid hinj hgrid hwgrid) hcol)

end WeightedReducedGallery
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.TwoFlagBand
open scoped Classical
open OccurrenceIncidence.VertexTable

/-- Occurrence labels for the lower strips; the maximal parent is deliberately
not a constructor. Equal ranks or isomorphic modules do not identify labels. -/
inductive Secondary (n m : ℕ)
  | row : Fin n → Secondary n m
  | col : Fin m → Secondary n m
  | cell : Fin n → Fin m → Secondary n m
  deriving DecidableEq, Fintype

namespace RankShape
variable {n m r : ℕ} (d : RankShape n m r)
def secondaryRank : Secondary n m → ℕ
  | .row i => ∑ j, (d.val (i,j)).val
  | .col j => ∑ i, (d.val (i,j)).val
  | .cell i j => (d.val (i,j)).val

lemma fresh_parent_row_rank : r = ∑ i, d.secondaryRank (.row i) :=
  d.property.symm.trans (Fintype.sum_prod_type (fun p : Fin n × Fin m => (d.val p).val))


/-- Actual names of the common-graded basis vectors, including empty cells. -/
abbrev Atom := (p : Fin n × Fin m) × Fin (d.val p).val

def secondaryAtoms : Secondary n m → Set d.Atom
  | .row i => {t | t.1.1=i}
  | .col j => {t | t.1.2=j}
  | .cell i j => {t | t.1=(i,j)}

def facetAtoms : Option (Secondary n m) → Set d.Atom
  | none => Set.univ
  | some s => d.secondaryAtoms s

end RankShape
end IntegralCharacterVarieties.TwoFlagBand

namespace IntegralCharacterVarieties.TwoFlagBand
open scoped Classical
open OccurrenceIncidence.VertexTable
namespace RankShape
variable {n m r : ℕ} (d : RankShape n m r)

lemma atom_parent_sum (t : d.Atom) :
    (1 : ℕ)=∑ i, atomWeight d.secondaryAtoms t (.row i) := by
  simp [atomWeight,secondaryAtoms,eq_comm]

lemma atom_row_sum (t : d.Atom) (i : Fin n) :
    atomWeight d.secondaryAtoms t (.row i)=∑ j, atomWeight d.secondaryAtoms t (.cell i j) := by
  by_cases h : t.1.1=i
  · simp [atomWeight,secondaryAtoms,Prod.ext_iff,h]
  · simp [atomWeight,secondaryAtoms,Prod.ext_iff,h]

lemma atom_col_sum (t : d.Atom) (j : Fin m) :
    atomWeight d.secondaryAtoms t (.col j)=∑ i, atomWeight d.secondaryAtoms t (.cell i j) := by
  by_cases h : t.1.2=j
  · simp [atomWeight,secondaryAtoms,Prod.ext_iff,h]
  · simp [atomWeight,secondaryAtoms,Prod.ext_iff,h]

lemma cell_injective : Function.Injective (fun p : Fin n × Fin m => Secondary.cell p.1 p.2) := by
  intro p q h
  exact Prod.ext (Secondary.cell.inj h).1 (Secondary.cell.inj h).2

lemma weighted_band : WeightedReducedGallery r d.secondaryRank (fun _ : d.Atom => 1)
    (atomWeight d.secondaryAtoms) (List.ofFn Secondary.row) (List.ofFn Secondary.col) :=
  WeightedReducedGallery.two_flag_gallery Secondary.row Secondary.col Secondary.cell
    cell_injective d.fresh_parent_row_rank (fun _ => rfl) (fun _ => rfl)
    d.atom_parent_sum d.atom_row_sum d.atom_col_sum

end RankShape
end IntegralCharacterVarieties.TwoFlagBand

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type} {r : F → ℕ} {parent : F}

namespace OrderedWalk
variable {a b c : List F}
def crossings (w : OrderedWalk parent a b) : List (F × F) :=
  (List.ofFn fun j => (w.vertex j).decoration.crossings).flatten
lemma crossings_cons (s : OrderedStep parent a b) (w : OrderedWalk parent b c) :
    (w.cons s).crossings = s.decoration.crossings ++ w.crossings := by
  rcases w with ⟨l,state,vertex,first,last⟩
  subst b
  simp only [crossings,cons,List.ofFn_succ,Fin.cases_zero,Fin.cases_succ,List.flatten_cons]
  rfl
lemma crossings_refl (a : List F) : (refl (parent:=parent) a).crossings=[] := rfl
lemma crossings_headIdentity (w : OrderedWalk parent a b) : w.headIdentity.crossings=w.crossings := by
  rw [headIdentity,crossings_cons]
  rfl
end OrderedWalk

namespace RankedChain
lemma walk_crossings {a b : List F} (p : RankedChain r parent a b) :
    p.forget.walk.crossings=p.crossings := by
  induction p with
  | refl a => rfl
  | step s hs p ih =>
    exact (OrderedWalk.crossings_cons s p.forget.walk).trans
      (congrArg (s.decoration.crossings ++ ·) ih)
end RankedChain

namespace RealizedBand
variable {a b : List F}
def crossings (B : RealizedBand parent a b) : List (F × F) :=
  (List.ofFn fun j => (B.decoration j).crossings).flatten
lemma realize_crossings (w : OrderedWalk parent a b) :
    w.realize.crossings=w.crossings := w.crossings_headIdentity
end RealizedBand

variable {N : ℕ} {rank : F → ℕ}
lemma RealizedBand.exists_reduced_congr {a b a' b' : List (Option F)}
    (ha : a=a') (hb : b=b')
    (H : ∃ B : RealizedBand none a b,
      (∀ v, (B.decoration v).Conservative (freshRank N rank)) ∧
      (∀ v, ∃ d : (B.kind v).SecondaryNames F,
        B.decoration v = (B.kind v).freshDecoration d) ∧ B.crossings.Nodup) :
    ∃ B : RealizedBand none a' b',
      (∀ v, (B.decoration v).Conservative (freshRank N rank)) ∧
      (∀ v, ∃ d : (B.kind v).SecondaryNames F,
        B.decoration v = (B.kind v).freshDecoration d) ∧ B.crossings.Nodup := by
  subst a'; subst b'; exact H

/-- A finite band with rank conservation, exhaustion of the fresh parent germs,
and no repeated crossing. -/
theorem reduced_ranked_two_flag_band {m n : ℕ} (row : Fin m → F) (col : Fin n → F)
    (grid : Fin m → Fin n → F)
    (hinj : Function.Injective (fun p : Fin m × Fin n => grid p.1 p.2))
    (hp : N = ∑ i, rank (row i))
    (hr : ∀ i, rank (row i) = ∑ j, rank (grid i j))
    (hc : ∀ j, rank (col j) = ∑ i, rank (grid i j)) :
    ∃ B : RealizedBand none (List.ofFn (some ∘ row)) (List.ofFn (some ∘ col)),
      (∀ v, (B.decoration v).Conservative (freshRank N rank)) ∧
      (∀ v, ∃ d : (B.kind v).SecondaryNames F,
        B.decoration v = (B.kind v).freshDecoration d) ∧ B.crossings.Nodup := by
  obtain ⟨p,hfresh,hred⟩ := ReducedGallery.two_flag_gallery row col grid hinj hp hr hc
  have h : freshRank N rank none = listRank (freshRank N rank) ((List.ofFn row).map some) := by
    simpa only [listRank_some,listRank_ofFn,freshRank] using hp
  have H : ∃ B : RealizedBand none ((List.ofFn row).map some) ((List.ofFn col).map some),
      (∀ v, (B.decoration v).Conservative (freshRank N rank)) ∧
      (∀ v, ∃ d : (B.kind v).SecondaryNames F,
        B.decoration v = (B.kind v).freshDecoration d) ∧ B.crossings.Nodup := by
    refine ⟨p.forget.walk.realize,p.forget.walk.realize_conservative p.walk_conservative h,
      p.forget.walk.realize_fresh (List.ofFn row) (p.walk_fresh hfresh),?_⟩
    rwa [RealizedBand.realize_crossings,RankedChain.walk_crossings]
  exact RealizedBand.exists_reduced_congr (List.map_ofFn ..) (List.map_ofFn ..) H
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

noncomputable section
namespace IntegralCharacterVarieties.TwoFlagBand
open scoped Classical
open OccurrenceIncidence.VertexTable
namespace RankShape
variable {n m r : ℕ} (d : RankShape n m r)

def atomicChain : RankedChain (freshRank r d.secondaryRank) none
    ((List.ofFn Secondary.row).map some) ((List.ofFn Secondary.col).map some) :=
  d.weighted_band.choose

def atomicBand : RealizedBand (F:=Option (Secondary n m)) none ((List.ofFn Secondary.row).map some)
    ((List.ofFn Secondary.col).map some) := d.atomicChain.forget.walk.realize

lemma atomicBand_conservative (v) :
    (d.atomicBand.decoration v).Conservative (freshRank r d.secondaryRank) := by
  apply d.atomicChain.forget.walk.realize_conservative d.atomicChain.walk_conservative
  simpa only [listRank_some,listRank_ofFn,freshRank] using d.fresh_parent_row_rank

lemma atomicBand_fresh (v) : ∃ s : (d.atomicBand.kind v).SecondaryNames (Secondary n m),
    d.atomicBand.decoration v=(d.atomicBand.kind v).freshDecoration s :=
  d.atomicChain.forget.walk.realize_fresh (List.ofFn Secondary.row)
    (d.atomicChain.walk_fresh d.weighted_band.choose_spec.1) v

lemma atomicBand_nodup : d.atomicBand.crossings.Nodup := by
  rw [atomicBand,RealizedBand.realize_crossings,RankedChain.walk_crossings]
  exact d.weighted_band.choose_spec.2.1

lemma facet_atomWeight (t : d.Atom) : atomWeight d.facetAtoms t=
    freshRank 1 (atomWeight d.secondaryAtoms t) := by
  funext f
  cases f <;> simp only [atomWeight,facetAtoms,freshRank,Set.mem_univ,ite_true]
  rfl

lemma atomicBand_atoms (v) : (d.atomicBand.decoration v).AtomConservative d.facetAtoms := by
  intro t
  rw [d.facet_atomWeight t]
  apply d.atomicChain.forget.walk.realize_conservative
    (d.atomicChain.forRank_walk _ (d.weighted_band.choose_spec.2.2 t))
  simpa only [listRank_some,listRank_ofFn,freshRank] using d.atom_parent_sum t

def vertexAtoms (v) : AtomicData (d.atomicBand.kind v) d.Atom :=
  (d.atomicBand.decoration v).atomicData d.facetAtoms (d.atomicBand_atoms v)

lemma atomicBand_comparison {R : Type*} [CommRing R] (v) :
    (LocalRanks.comparison (d.atomicBand.kind v) (d.vertexAtoms v).localRanks
      ((d.vertexAtoms v).frame (R:=R))).Holds := (d.vertexAtoms v).comparison_holds

end RankShape
end IntegralCharacterVarieties.TwoFlagBand
end

noncomputable section
namespace IntegralCharacterVarieties.TwoFlagBand
open scoped Classical
open OccurrenceIncidence.VertexTable
namespace RankShape
variable {n m r : ℕ} (d : RankShape n m r)

def rowAtomsEquiv (i : Fin n) :
    ((j : Fin m) × Fin (d.val (i,j)).val) ≃ {t : d.Atom // t∈d.secondaryAtoms (.row i)} :=
  Equiv.ofBijective (fun t => ⟨⟨(i,t.1),t.2⟩,rfl⟩) (by
    constructor
    · rintro ⟨j,k⟩ ⟨l,p⟩ h
      have e := congrArg Subtype.val h
      have e' : j=l := congrArg (fun t : d.Atom => t.1.2) e
      subst l
      have e'' : k=p := eq_of_heq (Sigma.mk.inj_iff.mp e).2
      subst p
      rfl
    · rintro ⟨⟨⟨i',j⟩,k⟩,h⟩
      change i'=i at h
      subst i'
      exact ⟨⟨j,k⟩,rfl⟩)

def colAtomsEquiv (j : Fin m) :
    ((i : Fin n) × Fin (d.val (i,j)).val) ≃ {t : d.Atom // t∈d.secondaryAtoms (.col j)} :=
  Equiv.ofBijective (fun t => ⟨⟨(t.1,j),t.2⟩,rfl⟩) (by
    constructor
    · rintro ⟨i,k⟩ ⟨l,p⟩ h
      have e := congrArg Subtype.val h
      have e' : i=l := congrArg (fun t : d.Atom => t.1.1) e
      subst l
      have e'' : k=p := eq_of_heq (Sigma.mk.inj_iff.mp e).2
      subst p
      rfl
    · rintro ⟨⟨⟨i,j'⟩,k⟩,h⟩
      change j'=j at h
      subst j'
      exact ⟨⟨i,k⟩,rfl⟩)

def cellAtomsEquiv (i : Fin n) (j : Fin m) :
    Fin (d.val (i,j)).val ≃ {t : d.Atom // t∈d.secondaryAtoms (.cell i j)} :=
  Equiv.ofBijective (fun k => ⟨⟨(i,j),k⟩,rfl⟩) (by
    constructor
    · intro k l h
      exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2
    · rintro ⟨⟨p,k⟩,h⟩
      change p=(i,j) at h
      subst p
      exact ⟨k,rfl⟩)

lemma card_secondaryAtoms (s : Secondary n m) :
    Fintype.card {t : d.Atom // t∈d.secondaryAtoms s}=d.secondaryRank s := by
  cases s with
  | row i =>
    simpa [secondaryRank,Fintype.card_sigma] using (Fintype.card_congr (d.rowAtomsEquiv i)).symm
  | col j =>
    simpa [secondaryRank,Fintype.card_sigma] using (Fintype.card_congr (d.colAtomsEquiv j)).symm
  | cell i j =>
    simpa [secondaryRank] using (Fintype.card_congr (d.cellAtomsEquiv i j)).symm

lemma card_atoms : Fintype.card d.Atom=r := by
  simpa only [Fintype.card_sigma,Fintype.card_fin] using d.property

lemma card_facetAtoms (f : Option (Secondary n m)) :
    Fintype.card {t : d.Atom // t∈d.facetAtoms f}=freshRank r d.secondaryRank f := by
  cases f with
  | none => simpa [facetAtoms,freshRank] using d.card_atoms
  | some s => exact d.card_secondaryAtoms s

lemma vertexAtoms_rank (v) (z) :
    (d.vertexAtoms v).rank z=freshRank r d.secondaryRank ((d.atomicBand.decoration v).color z) :=
  d.card_facetAtoms _

end RankShape
end IntegralCharacterVarieties.TwoFlagBand
end

end OAI
