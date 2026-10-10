import Mathlib
import OAI.Combinatorics.StripMass.ColumnSew
import OAI.Combinatorics.StripMass.PhysicalStationarity

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset Matrix

 

def northInjectionWeights {K : Type*} [One K] [Zero K] : Weights K := ⟨1,1,0,0,0⟩

def sourceFullSplit (n : ℕ) : Pairing n ⊕ SourcePairing n ≃ Pairing (n+1) where
  toFun := Sum.elim Pairing.padTop Subtype.val
  invFun p := if h : p.Occupied (Fin.last n) then Sum.inr ⟨p,h⟩ else
    Sum.inl (p.restrict Fin.castSuccOrderEmb)
  left_inv p := by
    cases p with
    | inl p =>
      change (if h : p.padTop.Occupied (Fin.last n) then Sum.inr (⟨p.padTop,h⟩ : SourcePairing n) else
        Sum.inl (Pairing.restrict Fin.castSuccOrderEmb p.padTop))=Sum.inl p
      rw [dite_eq_right (Pairing.padTop_not_occupied_last p)]
      exact congrArg Sum.inl (Pairing.restrict_map _ _)
    | inr p =>
      change (if h : p.val.Occupied (Fin.last n) then Sum.inr ⟨p.val,h⟩ else
        Sum.inl (Pairing.restrict Fin.castSuccOrderEmb p.val))=Sum.inr p
      rw [dite_eq_left p.property]
  right_inv p := by
    change Sum.elim Pairing.padTop Subtype.val
      (if h : p.Occupied (Fin.last n) then Sum.inr ⟨p,h⟩ else
        Sum.inl (Pairing.restrict Fin.castSuccOrderEmb p))=p
    split_ifs with h
    · rfl
    · exact Pairing.padTop_restrict p h

@[simp] lemma sourceFullSplit_inl {n : ℕ} (p : Pairing n) :
    sourceFullSplit n (.inl p)=p.padTop := rfl
@[simp] lemma sourceFullSplit_inr {n : ℕ} (p : SourcePairing n) :
    sourceFullSplit n (.inr p)=p.val := rfl

def augmentVector {K : Type*} {n : ℕ} (v : Pairing n → K) (z : SourcePairing n → K) :
    Pairing (n+1) → K := fun p=>Sum.elim v z ((sourceFullSplit n).symm p)

@[simp] lemma augmentVector_split {K : Type*} {n : ℕ} (v : Pairing n → K) (z : SourcePairing n → K)
    (p : Pairing n ⊕ SourcePairing n) :
    augmentVector v z (sourceFullSplit n p)=Sum.elim v z p := by
  simp only [augmentVector,Equiv.symm_apply_apply]

@[simp] lemma augmentVector_padTop {K : Type*} {n : ℕ} (v : Pairing n → K) (z : SourcePairing n → K)
    (p : Pairing n) : augmentVector v z p.padTop=v p := augmentVector_split v z (.inl p)

@[simp] lemma augmentVector_source {K : Type*} {n : ℕ} (v : Pairing n → K) (z : SourcePairing n → K)
    (p : SourcePairing n) : augmentVector v z p.val=z p := augmentVector_split v z (.inr p)

@[simp] lemma augmentVector_empty {K : Type*} {n : ℕ} (v : Pairing n → K) (z : SourcePairing n → K) :
    augmentVector v z (empty (n+1))=v (empty n) := by
  rw [←Pairing.padTop_empty,augmentVector_padTop]

lemma column_last_factor {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Weights K) (z : Weights K) (q p : Pairing (n+1)) :
    column (Fin.snoc w z) q p = lastCoefficient (fun i=>(w i).tile) q p * z.tile (lastTile p q) := by
  have hw : (fun i=>((Fin.snoc w z : Fin (n+1) → Weights K) i).tile)=
      Fin.snoc (fun i=>(w i).tile) z.tile := by
    funext i
    refine Fin.lastCases ?_ (fun i=>?_) i <;> simp
  change rawColumn _ q p=_
  rw [hw,rawColumn_last_factor]

lemma northInjection_column_blocks {K : Type*} [CommRing K] {n : ℕ} (w : Fin n → Weights K) :
    (column (Fin.snoc w northInjectionWeights)).submatrix (sourceFullSplit n) (sourceFullSplit n)=
      Matrix.fromBlocks (column w) 0 (northSource (fun i=>(w i).tile))
        (sourceTransfer (fun i=>(w i).tile)) := by
  ext q p
  change column _ _ _=_
  rw [column_last_factor]
  cases q with
  | inl q =>
    cases p with
    | inl p => simp [lastCoefficient_padTop,lastTile,Weights.tile]; rfl
    | inr p => simp [lastTile,p.property,northInjectionWeights,Weights.tile]
  | inr q =>
    cases p with
    | inl p => simp [lastTile,q.property,northInjectionWeights,Weights.tile,northSource]
    | inr p => simp [lastTile,q.property,p.property,northInjectionWeights,Weights.tile,sourceTransfer]

lemma augmentVector_stationary {K : Type*} [CommRing K] {n : ℕ} (w : Fin n → Weights K)
    (v : Pairing n → K) (z : SourcePairing n → K)
    (hv : (column w).mulVec v=v)
    (hz : (sourceTransfer (fun i=>(w i).tile)).mulVec z+
      (northSource (fun i=>(w i).tile)).mulVec v=z) :
    (column (Fin.snoc w northInjectionWeights)).mulVec (augmentVector v z)=augmentVector v z := by
  funext q
  obtain ⟨q,rfl⟩:=(sourceFullSplit n).surjective q
  have he : (column (Fin.snoc w northInjectionWeights)).mulVec (augmentVector v z) (sourceFullSplit n q)=
      (Matrix.fromBlocks (column w) 0 (northSource (fun i=>(w i).tile))
        (sourceTransfer (fun i=>(w i).tile))).mulVec (Sum.elim v z) q := by
    rw [Matrix.mulVec,dotProduct,←(sourceFullSplit n).sum_comp]
    simp_rw [augmentVector_split]
    change (∑ p,((column (Fin.snoc w northInjectionWeights)).submatrix
      (sourceFullSplit n) (sourceFullSplit n)) q p * Sum.elim v z p)=_
    rw [northInjection_column_blocks]
    rfl
  rw [he,augmentVector_split]
  cases q with
  | inl q => simpa [Matrix.mulVec,dotProduct,Fintype.sum_sum_type] using congrFun hv q
  | inr q =>
    have hh:=congrFun hz q
    simp only [Pi.add_apply,Matrix.mulVec,dotProduct] at hh
    simpa only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂,Sum.elim_inl,Sum.elim_inr,add_comm] using hh

 
def angleAugmented {n : ℕ} (u : Fin n → ℝ) : Pairing (n+1) → ℝ :=
  augmentVector (angleVacuum u) (angleNorthSource u)

lemma angleAugmented_restricted_stationary {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (h : angleScalar u≠0) :
    (restrictedColumn (Fin.snoc (fun i=>physicalWeights (3*lambda-u i)) northInjectionWeights)).mulVec
        (fun p=>angleAugmented u p.val)+
      injectionColumn (Fin.snoc (fun i=>physicalWeights (3*lambda-u i)) northInjectionWeights)=
      fun p=>angleAugmented u p.val := by
  have hh:=augmentVector_stationary (fun i=>physicalWeights (3*lambda-u i))
    (angleVacuum u) (angleNorthSource u) (angleVacuum_stationary u hL) (angleNorthSource_stationary u hL)
  funext p
  have hp:=congrFun hh p.val
  rw [column_mulVec_nonempty,augmentVector_empty,angleVacuum_empty u h,mul_one] at hp
  simpa only [Pi.add_apply,add_comm,angleAugmented] using hp

lemma continuousOn_angleAugmented {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : ∀u∈S,angleScalar u≠0) : ContinuousOn (fun u=>angleAugmented u) S := by
  apply continuousOn_pi.mpr
  intro p
  obtain ⟨q,rfl⟩:=(sourceFullSplit n).surjective p
  have he : (fun u=>angleAugmented u (sourceFullSplit n q))=
      fun u=>Sum.elim (angleVacuum u) (angleNorthSource u) q := by
    funext u
    exact augmentVector_split _ _ _
  rw [he]
  cases q with
  | inl q => exact (continuousOn_pi.mp (continuousOn_angleVacuum h)) q
  | inr q => exact (continuousOn_pi.mp (continuousOn_angleNorthSource h)) q

end

 

 

noncomputable section
open scoped BigOperators Classical
namespace ColumnChain
section RingCoefficients
variable {K : Type*} [CommRing K] {n : ℕ}

def weight (w : Fin n → Weights K) : List (Configuration n) → K
  | [] => 1
  | t::ts => (∏ i,(w i).tile (t i))*weight w ts

lemma weighted_runs_cons (w : Fin n → Weights K) (p q : Pairing n)
    (t : Configuration n) (ts : List (Configuration n)) :
    (if Runs p (t::ts) q then weight w (t::ts) else 0)=
      ∑ r : Pairing n, (if Realizes r q t then ∏i,(w i).tile (t i) else 0)*
        (if Runs p ts r then weight w ts else 0) := by
  by_cases hh : ∃r,Runs p ts r
  · obtain ⟨r,hr⟩:=hh
    rw [Finset.sum_eq_single r]
    · have he : Runs p (t::ts) q ↔ Realizes r q t := by
        constructor
        · rintro ⟨r',hr',ht⟩
          exact runs_unique hr' hr ▸ ht
        · exact fun ht=>⟨r,hr,ht⟩
      simp only [he,hr,ite_true,weight]
      split_ifs <;> simp
    · intro s _ hsr
      have hs : ¬Runs p ts s := fun hs=>hsr (runs_unique hs hr)
      simp [hs]
    · simp
  · have hs : ∀r,¬Runs p ts r := fun r hr=>hh ⟨r,hr⟩
    have hq : ¬Runs p (t::ts) q := fun ⟨r,hr,_⟩=>hs r hr
    simp [hq,hs]

def mass (w : Fin n → Weights K) (m : ℕ) (q p : Pairing n) : K :=
  ∑ h : Fin m → Configuration n, if Runs p (List.ofFn h) q then weight w (List.ofFn h) else 0

lemma mass_zero (w : Fin n → Weights K) (q p : Pairing n) :
    mass w 0 q p=if q=p then 1 else 0 := by
  simp [mass,Runs,weight,eq_comm]

lemma mass_succ (w : Fin n → Weights K) (m : ℕ) (q p : Pairing n) :
    mass w (m+1) q p=∑r,column w q r*mass w m r p := by
  unfold mass
  rw [←(Fin.consEquiv (fun _ : Fin (m+1)=>Configuration n)).sum_comp]
  simp only [Fintype.sum_prod_type]
  simp only [Fin.consEquiv,Equiv.coe_fn_mk,List.ofFn_cons]
  simp_rw [weighted_runs_cons]
  conv_lhs =>
    arg 2
    ext t
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [column,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]

 

lemma mass_eq_pow (w : Fin n → Weights K) (m : ℕ) (q p : Pairing n) :
    mass w m q p=(column w ^ m) q p := by
  induction m generalizing q p with
  | zero => simp [mass_zero,Matrix.one_apply]
  | succ m ih =>
    rw [mass_succ,pow_succ']
    simp only [Matrix.mul_apply,ih]

end RingCoefficients

 

 


variable {n : ℕ}

lemma weight_head_ne_zero (w : Fin n → Weights ℝ) (t : Configuration n)
    (ts : List (Configuration n)) (h : weight w (t::ts)≠0) (i : Fin n) :
    (w i).tile (t i)≠0 := by
  have hh := (mul_ne_zero_iff.mp h).1
  exact (Finset.prod_ne_zero_iff.mp hh) i (Finset.mem_univ i)

lemma weight_tail_ne_zero (w : Fin n → Weights ℝ) (t : Configuration n)
    (ts : List (Configuration n)) (h : weight w (t::ts)≠0) : weight w ts≠0 :=
  (mul_ne_zero_iff.mp h).2

 

theorem north_shape (w : Fin n → Weights ℝ) (ts : List (Configuration (n+1)))
    (q : Pairing (n+1)) (hr : Runs (empty (n+1)) ts q)
    (hw : weight (Fin.snoc w northInjectionWeights) ts≠0) :
    (q.Occupied (Fin.last n) → ∃ k l : ℕ,
      ts.map (fun t=>t (Fin.last n))=
        List.replicate k Tile.diagonal₁ ++ Tile.vertical₀ :: List.replicate l Tile.vacant) ∧
    (¬q.Occupied (Fin.last n) →
      ts.map (fun t=>t (Fin.last n))=List.replicate ts.length Tile.vacant) := by
  induction ts generalizing q with
  | nil =>
    have he : empty (n+1)=q := hr
    subst q
    refine ⟨fun h=>(empty_not_occupied _ h).elim,fun _=>rfl⟩
  | cons t ts ih =>
    obtain ⟨p,hp,ht⟩:=hr
    have hf := weight_head_ne_zero (Fin.snoc w northInjectionWeights) t ts hw (Fin.last n)
    rw [Fin.snoc_last] at hf
    obtain ⟨h₁,h₀⟩ := ih p hp (weight_tail_ne_zero _ t ts hw)
    have he:=ht.last_eq
    by_cases hp : p.Occupied (Fin.last n)
    · by_cases hq : q.Occupied (Fin.last n)
      · have he' : t (Fin.last n)=.diagonal₁ := by simpa only [lastTile,hp,hq,ite_true] using he
        obtain ⟨k,l,hshape⟩:=h₁ hp
        refine ⟨fun _=>⟨k+1,l,?_⟩,fun h=>(h hq).elim⟩
        simp only [List.map_cons,he',hshape,List.replicate_succ,List.cons_append]
      · have he' : t (Fin.last n)=.cap := by simpa only [lastTile,hp,hq,ite_true,ite_false] using he
        simp only [he',northInjectionWeights,Weights.tile,ne_eq,not_true_eq_false] at hf
    · by_cases hq : q.Occupied (Fin.last n)
      · have he' : t (Fin.last n)=.vertical₀ := by simpa only [lastTile,hp,hq,ite_true,ite_false] using he
        refine ⟨fun _=>⟨0,ts.length,?_⟩,fun h=>(h hq).elim⟩
        simp only [List.map_cons,he',h₀ hp,List.replicate_zero,List.nil_append]
      · have he' : t (Fin.last n)=.vacant := by simpa only [lastTile,hp,hq,ite_false] using he
        refine ⟨fun h=>(hq h).elim,fun _=>?_⟩
        simp only [List.map_cons,he',h₀ hp,List.length_cons,List.replicate_succ]

lemma north_birth_unique_shape (k l k' l' : ℕ)
    (h : List.replicate k Tile.diagonal₁ ++ Tile.vertical₀ :: List.replicate l Tile.vacant =
      List.replicate k' Tile.diagonal₁ ++ Tile.vertical₀ :: List.replicate l' Tile.vacant) :
    k=k' ∧ l=l' := by
  induction k generalizing k' with
  | zero =>
    cases k' with
    | zero =>
      have he : List.replicate l Tile.vacant=List.replicate l' Tile.vacant := List.cons.inj h |>.2
      exact ⟨rfl,by simpa only [List.length_replicate] using congrArg List.length he⟩
    | succ k' => simp [List.replicate_succ] at h
  | succ k ih =>
    cases k' with
    | zero => simp [List.replicate_succ] at h
    | succ k' =>
      simp only [List.replicate_succ,List.cons_append,List.cons.injEq,true_and] at h
      obtain ⟨rfl,rfl⟩:=ih k' h
      exact ⟨rfl,rfl⟩

 
theorem north_birth_exists_unique (w : Fin n → Weights ℝ)
    (ts : List (Configuration (n+1))) (q : SourcePairing n)
    (hr : Runs (empty (n+1)) ts q.val)
    (hw : weight (Fin.snoc w northInjectionWeights) ts≠0) :
    ∃! kl : ℕ×ℕ,
      ts.map (fun t=>t (Fin.last n))=
        List.replicate kl.1 Tile.diagonal₁ ++ Tile.vertical₀ :: List.replicate kl.2 Tile.vacant := by
  obtain ⟨k,l,hkl⟩:=(north_shape w ts q hr hw).1 q.property
  refine ⟨(k,l),hkl,?_⟩
  rintro ⟨k',l'⟩ he
  obtain ⟨rfl,rfl⟩:=north_birth_unique_shape k' l' k l (he.symm.trans hkl)
  rfl

end ColumnChain
end

 

 

noncomputable section
open scoped Classical
namespace ColumnChain
variable {n : ℕ}

 

def read (ts : List (Configuration n)) (k : ℕ) : Configuration n :=
  (ts[k]?).getD (fun _=>.vacant)

@[simp] lemma read_nil (k : ℕ) : read ([] : List (Configuration n)) k=fun _=>.vacant := by
  simp [read]
@[simp] lemma read_cons_zero (t : Configuration n) (ts : List (Configuration n)) :
    read (t::ts) 0=t := rfl
@[simp] lemma read_cons_succ (t : Configuration n) (ts : List (Configuration n)) (k : ℕ) :
    read (t::ts) (k+1)=read ts k := rfl

lemma read_ge (ts : List (Configuration n)) (k : ℕ) (hk : ts.length≤k) :
    read ts k=fun _=>.vacant := by
  simp only [read,List.getElem?_eq_none hk,Option.getD_none]

lemma read_entries (ts : List (Configuration n)) (k : Fin ts.length) :
    read ts k=ColumnRectangle.entries ts k := by
  induction ts with
  | nil => exact Fin.elim0 k
  | cons t ts ih =>
    induction k using Fin.cases with
    | zero => rfl
    | succ k => exact ih k

lemma support_empty_read (ts : List (Configuration n)) (i : Fin n) :
    support (empty n) ts i ↔ (read ts 0 i).Occupied 2 := by
  cases ts with
  | nil => simp only [support,read_nil]; exact ⟨fun h=>(empty_not_occupied i h).elim,
      fun h=>(Tile.vacant_not_occupied 2 h).elim⟩
  | cons => rfl

 
structure LocallyCompatible (ts : List (Configuration n)) : Prop where
  horizontal : ∀ k i, (read ts (k+1) i).Occupied 2 ↔ (read ts k i).Occupied 1
  south : ∀ k i, i.val=0 → ¬(read ts k i).Occupied 0
  north : ∀ k i, i.val+1=n → ¬(read ts k i).Occupied 3
  vertical : ∀ k i j, i.val+1=j.val →
    ((read ts k i).Occupied 3 ↔ (read ts k j).Occupied 0)

lemma compatible_empty_iff (ts : List (Configuration n)) :
    Compatible (empty n) ts ↔ LocallyCompatible ts := by
  induction ts with
  | nil =>
    refine ⟨fun _=>⟨?_,?_,?_,?_⟩,fun _=>trivial⟩ <;> simp [Tile.vacant_not_occupied]
  | cons t ts ih =>
    constructor
    · rintro ⟨hc,ht⟩
      obtain ⟨hh,hs,hn,hv⟩ := ih.mp hc
      refine ⟨?_,?_,?_,?_⟩
      · intro k i
        cases k with
        | zero => exact (support_empty_read ts i).symm.trans (ht.west i).symm
        | succ k => exact hh k i
      · intro k i hi
        cases k with
        | zero => exact ht.south i hi
        | succ k => exact hs k i hi
      · intro k i hi
        cases k with
        | zero => exact ht.north i hi
        | succ k => exact hn k i hi
      · intro k i j hij
        cases k with
        | zero => exact ht.glued i j hij
        | succ k => exact hv k i j hij
    · intro h
      refine ⟨ih.mpr ⟨fun k i=>h.horizontal (k+1) i,fun k i=>h.south (k+1) i,
        fun k i=>h.north (k+1) i,fun k i j=>h.vertical (k+1) i j⟩,?_,?_,?_,?_⟩
      · intro i
        exact (h.horizontal 0 i).symm.trans (support_empty_read ts i).symm
      · exact h.south 0
      · exact h.north 0
      · exact h.vertical 0

lemma read_tile_ne_zero {w : Fin n → Weights ℝ} {ts : List (Configuration n)}
    (h : weight w ts ≠ 0) (k : ℕ) (i : Fin n) : (w i).tile (read ts k i)≠0 := by
  induction ts generalizing k with
  | nil => simp [Weights.tile]
  | cons t ts ih =>
    cases k with
    | zero => exact weight_head_ne_zero w t ts h i
    | succ k => exact ih (weight_tail_ne_zero w t ts h) k

end ColumnChain
end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip.PositiveMatrix
noncomputable section
open Matrix
open scoped BigOperators Classical

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma submatrix_pow_equiv (Q : Matrix ι ι ℝ) (e : κ ≃ ι) (k : ℕ) :
    (Q.submatrix e e)^k=(Q^k).submatrix e e := by
  induction k with
  | zero => simp only [pow_zero,Matrix.submatrix_one_equiv]
  | succ k ih => rw [pow_succ,pow_succ,ih,Matrix.submatrix_mul_equiv]

lemma SummablePowers.reindex {Q : Matrix ι ι ℝ} (hs : SummablePowers Q) (e : κ ≃ ι) :
    SummablePowers (Q.submatrix e e) := by
  intro i j
  simpa only [submatrix_pow_equiv,Matrix.submatrix_apply] using hs (e i) (e j)

lemma summablePowers_reindex_iff (Q : Matrix ι ι ℝ) (e : κ ≃ ι) :
    SummablePowers (Q.submatrix e e) ↔ SummablePowers Q := by
  refine ⟨fun h=>?_,fun h=>h.reindex e⟩
  have hh:=h.reindex e.symm
  have he : (Q.submatrix e e).submatrix e.symm e.symm=Q := by
    ext i j; simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
  rw [he] at hh
  exact hh

 

lemma SummablePowers.fromBlocks_zero_right {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    (hQ : Nonnegative Q) (B : Matrix κ ι ℝ) (hB : ∀i j,0≤B i j) :
    SummablePowers (Matrix.fromBlocks Q 0 B 0) := by
  obtain ⟨z,hz,he⟩:=hs.hasSupervector hQ
  have hBz : ∀i,0≤B.mulVec z i := fun i=>Finset.sum_nonneg fun j _=>mul_nonneg (hB i j) (hz j).le
  apply HasSupervector.summablePowers
  · refine ⟨Sum.elim z (fun i=>B.mulVec z i+1),?_,?_⟩
    · intro i
      cases i with
      | inl i => exact hz i
      | inr i => exact lt_of_le_of_lt (hBz i) (lt_add_one _)
    · intro i
      cases i with
      | inl i => simpa only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
          Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Sum.elim_inl,Sum.elim_inr,
          Matrix.zero_apply,zero_mul,Finset.sum_const_zero,add_zero] using he i
      | inr i =>
        simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
          Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Sum.elim_inl,Sum.elim_inr,
          Matrix.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]
        exact lt_add_one _
  · intro i j
    cases i <;> cases j <;> simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply]
    · exact hQ _ _
    · exact le_rfl
    · exact hB _ _
    · exact le_rfl

 

lemma summablePowers_of_zero_cols (M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hM : Nonnegative M) (hs : SummablePowers M.toBlocks₁₁)
    (hz : ∀i j,M i (.inr j)=0) : SummablePowers M := by
  have hblock : M=Matrix.fromBlocks M.toBlocks₁₁ 0 M.toBlocks₂₁ 0 := by
    ext i j
    cases i <;> cases j <;> simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,Matrix.toBlocks₁₁,Matrix.toBlocks₂₁,Matrix.of_apply,hz]
  rw [hblock]
  exact hs.fromBlocks_zero_right (fun i j=>hM (.inl i) (.inl j)) M.toBlocks₂₁
    (fun i j=>hM (.inr i) (.inl j))

end
end CriticalStrip.PositiveMatrix

end OAI
