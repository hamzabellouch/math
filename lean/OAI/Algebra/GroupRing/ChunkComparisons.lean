import Mathlib
import OAI.Algebra.GroupRing.ListPassages
import OAI.Algebra.GroupRing.AffineIntervals

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChunkComparisons
open scoped Classical
open ComparedBlocks
variable {P T U C : Type*} {lp : P → ℕ} {lt : T → ℕ}

def positionEquiv (r : U ≃ T) (lu : U → ℕ) (hlen : ∀ u,lu u=lt (r u)) :
    Position lu ≃ Position lt :=
  Equiv.sigmaCongr r (fun u => (Equiv.refl ℤ).subtypeEquiv (by
    intro q
    change q∈BlockAlignment.positions 0 (lu u) ↔ q∈BlockAlignment.positions 0 (lt (r u))
    rw [hlen]))

lemma positionEquiv_source (r : U ≃ T) (lu : U → ℕ) (hlen : ∀ u,lu u=lt (r u)) (x : Position lu) :
    (positionEquiv r lu hlen x).1=r x.1 := rfl

lemma positionEquiv_coordinate (r : U ≃ T) (lu : U → ℕ) (hlen : ∀ u,lu u=lt (r u)) (x : Position lu) :
    (positionEquiv r lu hlen x).2.val=x.2.val := rfl

namespace Chunking
/-- Re-enumerating occurrence chunks does not change their geometric partition. -/
def reindex (K : Chunking lp lt) (r : U ≃ T) (lu : U → ℕ) (hlen : ∀ u,lu u=lt (r u)) : Chunking lp lu where
  equiv := (positionEquiv r lu hlen).trans K.equiv
  path u := K.path (r u)
  reverse u := K.reverse (r u)
  offset u := K.offset (r u)
  source x := K.source (positionEquiv r lu hlen x)
  coordinate x := K.coordinate (positionEquiv r lu hlen x)
end Chunking

variable [Fintype T] (color : T → C)
def multiplicity (c : C) : ℕ := Fintype.card {t // color t=c}

/-- Exact color-fibre enumeration, identifying the literal path traversals
with the multiplicity-indexed traversal type used in every stage estimate. -/
def enumeration : ((c : C) × Fin (multiplicity color c)) ≃ T :=
  (Equiv.sigmaCongrRight (fun c => (Fintype.equivFin {t // color t=c}).symm)).trans
    (Equiv.sigmaFiberEquiv color)

lemma enumeration_color (o : (c : C) × Fin (multiplicity color c)) : color (enumeration color o)=o.1 :=
  ((Fintype.equivFin {t // color t=o.1}).symm o.2).property

lemma enumeration_length (len : C → ℕ) (hl : ∀ t,lt t=len (color t))
    (o : (c : C) × Fin (multiplicity color c)) : len o.1=lt (enumeration color o) := by
  rw [hl (enumeration color o),enumeration_color color o]

/-- The complete finite reindexing into underlying chain and occurrence number. -/
def repeated (K : Chunking lp lt) (len : C → ℕ) (hl : ∀ t,lt t=len (color t)) :
    Chunking lp (fun o : (c : C) × Fin (multiplicity color c) => len o.1) :=
  K.reindex (enumeration color) _ (enumeration_length color len hl)

end TorsionFreeZeroDivisors.ChunkComparisons

namespace TorsionFreeZeroDivisors.ListChunkCoordinates
open scoped Classical BigOperators
open FiniteChunking
variable {A D : Type*} (ds : List A) (word : A → List D)

abbrev lengths (i : Fin ds.length) : ℕ := (word (ds.get i)).length

lemma ofFn_lengths : List.ofFn (lengths ds word)=ds.map (fun a => (word a).length) := by
  change List.ofFn (fun i : Fin ds.length => (word ds[i.val]).length) = _
  exact List.ofFn_getElem_eq_map ds (fun a => (word a).length)

lemma total_length : (∑ i,lengths ds word i)=(ds.flatMap word).length := by
  rw [← List.sum_ofFn,ofFn_lengths,List.length_flatMap]

lemma start_eq (i : Fin ds.length) :
    start (lengths ds word) i = ((ds.take i.val).flatMap word).length := by
  rw [List.length_flatMap,List.map_take,← ofFn_lengths,List.sum_take_ofFn]
  simp only [start,before,Fin.lt_def]

/-- Literal indexing through a list concatenation, including repeated chunks. -/
lemma get_flatMap (i : Fin ds.length) (q : Fin (lengths ds word i)) :
    (ds.flatMap word)[start (lengths ds word) i+q.val]? = some ((word (ds.get i)).get q) := by
  rw [start_eq]
  have hdec : ds.take i.val ++ ds.get i :: ds.drop (i.val+1)=ds := by
    simpa only [List.drop_eq_getElem_cons i.isLt,List.get_eq_getElem] using List.take_append_drop i.val ds
  have hflat := congrArg (List.flatMap word) hdec
  simp only [List.flatMap_append,List.flatMap_cons] at hflat
  calc
    _ = (((ds.take i.val).flatMap word) ++
        (word (ds.get i) ++ (ds.drop (i.val+1)).flatMap word))[
          ((ds.take i.val).flatMap word).length+q.val]? := by rw [hflat]
    _ = (word (ds.get i) ++ (ds.drop (i.val+1)).flatMap word)[q.val]? := by
      rw [List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
    _ = some ((word (ds.get i)).get q) := by
      rw [List.getElem?_append_left q.isLt,List.getElem?_eq_getElem q.isLt]
      rfl

end TorsionFreeZeroDivisors.ListChunkCoordinates

namespace TorsionFreeZeroDivisors.ChainChunkTransport
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChunkComparisons FiniteChunking ComparedBlocks
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "len" => chainLength Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "w" => word Γ mark h2

def orientation : R × Bool ≃ B := InvolutionOrientation.equiv (S).reverse (S).reverse_reverse (S).reverse_ne

def representative (b : B) : R := ((orientation Γ mark h2).symm b).1
def reversed (b : B) : Bool := ((orientation Γ mark h2).symm b).2

lemma oriented (b : B) : b=if reversed Γ mark h2 b then (S).reverse (representative Γ mark h2 b).val
    else (representative Γ mark h2 b).val := (orientation Γ mark h2).apply_symm_apply b |>.symm

lemma oriented_length (b : B) : len b=len (representative Γ mark h2 b).val := by
  have h := oriented Γ mark h2 b
  conv_lhs => rw [h]
  split_ifs <;> simp only [chainLength_reverse]

lemma word_get (b : B) (i : ℕ) (hi : i < len b) : (w b)[i]?=some (F^[i] b.val) := by
  simp [word_eq_range,hi]

lemma reverse_iter (b : B) (i : ℕ) (hi : i < len b) :
    F^[len b-i-1] ((S).reverse b).val=Γ.reverse (F^[i] b.val) := by
  let k := len b
  have hf := endpoint_reverse Γ.reverse τ Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2) (x:=b) (i:=k-i) (by change k-i ≤ k; omega)
  have he : k-(k-i)=i := by dsimp [k]; omega
  have hs : k-i=(k-i-1)+1 := by dsimp [k]; omega
  change F^[k-i] ((S).reverse b).val = τ (F^[k-(k-i)] b.val) at hf
  rw [he,hs,iterate_succ_apply'] at hf
  have h := congrArg τ hf
  change τ (τ (Γ.reverse (F^[k-i-1] ((S).reverse b).val))) = τ (τ (F^[i] b.val)) at h
  rw [turn_involutive Γ.origin mark h2,turn_involutive Γ.origin mark h2] at h
  have hh := congrArg Γ.reverse h
  rwa [Γ.reverse_reverse] at hh

lemma listDart (b : B) (q : ℤ) (hq : q∈BlockAlignment.positions 0 (len b)) :
    (w b)[(localIndex (reversed Γ mark h2 b) (len b) q).toNat]? =
      some (if reversed Γ mark h2 b then Γ.reverse (F^[q.toNat] (representative Γ mark h2 b).val.val)
        else F^[q.toNat] (representative Γ mark h2 b).val.val) := by
  have hz : 0 ≤ q ∧ q < len b := by simpa only [AffineIntervals.nat_positions,Finset.mem_Ico] using hq
  have hqcast : (q.toNat : ℤ)=q := Int.toNat_of_nonneg hz.1
  have hqn : q.toNat < len b := by omega
  have h := oriented Γ mark h2 b
  cases hr : reversed Γ mark h2 b
  · simp only [hr,Bool.false_eq_true,ite_false] at h ⊢
    simp only [localIndex,BlockAlignment.affine,Bool.false_eq_true,ite_false,add_zero]
    rw [word_get Γ mark h2 b q.toNat hqn,show b.val=(representative Γ mark h2 b).val.val from congrArg Subtype.val h]
  · simp only [hr,ite_true] at h ⊢
    have he : (localIndex true (len b) q).toNat=len b-q.toNat-1 := by
      simp only [localIndex,BlockAlignment.affine,ite_true]
      omega
    have hi : len b-q.toNat-1 < len b := by omega
    rw [he,word_get Γ mark h2 b _ hi]
    apply congrArg some
    rw [oriented_length Γ mark h2 b,show b.val=((S).reverse (representative Γ mark h2 b).val).val from congrArg Subtype.val h]
    apply reverse_iter
    rwa [←oriented_length Γ mark h2 b]

variable {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})

def chunks (p : P) : ℕ := (paths p).length
def chunkLength (p : P) (i : Fin (chunks Γ mark h2 paths p)) : ℕ := (w ((paths p).get i)).length
def chunkReverse (p : P) (i : Fin (chunks Γ mark h2 paths p)) : Bool := reversed Γ mark h2 ((paths p).get i)
def color (t : Traversal (chunks Γ mark h2 paths)) : R := representative Γ mark h2 ((paths t.1).get t.2)

def splitChunks := FiniteChunking.chunking (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths) (chunkReverse Γ mark h2 paths)

omit [Fintype P] in
lemma chunkLength_eq (t : Traversal (chunks Γ mark h2 paths)) :
    traversalLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths) t=repLength Γ mark h2 (color Γ mark h2 paths t) := by
  exact (word_length Γ mark h2 _).trans (oriented_length Γ mark h2 _)

omit [Fintype P] in
lemma pathLength_eq (p : P) :
    pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths) p=((paths p).flatMap w).length :=
  ListChunkCoordinates.total_length (paths p) w

/-- The original path's actual dart at the signed chunk image. -/
lemma chunk_dart (x : Position (traversalLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths))) :
    ((paths x.1.1).flatMap w)[((splitChunks Γ mark h2 paths).equiv x).2.val.toNat]? =
      some (if (splitChunks Γ mark h2 paths).reverse x.1 then
        Γ.reverse (F^[x.2.val.toNat] (color Γ mark h2 paths x.1).val.val)
        else F^[x.2.val.toNat] (color Γ mark h2 paths x.1).val.val) := by
  let b := (paths x.1.1).get x.1.2
  let q := localIndex (reversed Γ mark h2 b) (len b) x.2.val
  have hlen : chunkLength Γ mark h2 paths x.1.1 x.1.2=len b := word_length Γ mark h2 b
  have hq : x.2.val∈BlockAlignment.positions 0 (len b) := by
    have h := x.2.property
    change x.2.val∈BlockAlignment.positions 0 (chunkLength Γ mark h2 paths x.1.1 x.1.2) at h
    rwa [hlen] at h
  have hqb := local_bounds (reversed Γ mark h2 b) (len b) hq
  have hn : q.toNat < chunkLength Γ mark h2 paths x.1.1 x.1.2 := by
    rw [hlen]
    dsimp [q]
    omega
  have hflat := ListChunkCoordinates.get_flatMap (paths x.1.1) w x.1.2 ⟨q.toNat,hn⟩
  have him : ((splitChunks Γ mark h2 paths).equiv x).2.val.toNat=
      start (chunkLength Γ mark h2 paths x.1.1) x.1.2+q.toNat := by
    change (FiniteChunking.image _ _ _ x).2.val.toNat = _
    rw [FiniteChunking.image_val]
    change ((start (chunkLength Γ mark h2 paths x.1.1) x.1.2:ℤ)+
      localIndex (reversed Γ mark h2 b) (chunkLength Γ mark h2 paths x.1.1 x.1.2) x.2.val).toNat = _
    rw [hlen]
    omega
  change ((paths x.1.1).flatMap w)[start (chunkLength Γ mark h2 paths x.1.1) x.1.2+q.toNat]? =
    some ((w b).get ⟨q.toNat,hn⟩) at hflat
  rw [him,hflat]
  have hd := listDart Γ mark h2 b x.2.val hq
  rw [List.getElem?_eq_getElem hn] at hd
  exact hd

/-- Literal darts at all original path positions. -/
def originalDart (x : Position (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths))) : D :=
  ((paths x.1).flatMap w).get ⟨x.2.val.toNat,by
    have hx := x.2.property
    have hz : 0≤x.2.val ∧ x.2.val < pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths) x.1 := by
      simpa only [AffineIntervals.nat_positions,Finset.mem_Ico] using hx
    rw [←pathLength_eq Γ mark h2 paths]
    omega⟩

omit [Fintype P] in
lemma originalDart_get (x : Position (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths))) :
    ((paths x.1).flatMap w)[x.2.val.toNat]?=some (originalDart Γ mark h2 paths x) :=
  List.getElem?_eq_getElem _

lemma chunk_original (x : Position (traversalLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths))) :
    originalDart Γ mark h2 paths ((splitChunks Γ mark h2 paths).equiv x)=
      if (splitChunks Γ mark h2 paths).reverse x.1 then
        Γ.reverse (F^[x.2.val.toNat] (color Γ mark h2 paths x.1).val.val)
      else F^[x.2.val.toNat] (color Γ mark h2 paths x.1).val.val := by
  apply Option.some.inj
  rw [←originalDart_get]
  exact chunk_dart Γ mark h2 paths x

def repeatedChunks := ChunkComparisons.repeated (color Γ mark h2 paths)
  (splitChunks Γ mark h2 paths) (repLength Γ mark h2) (chunkLength_eq Γ mark h2 paths)

lemma repeated_original (x : Position (fun o : (c : R) × Fin (multiplicity (color Γ mark h2 paths) c) => repLength Γ mark h2 o.1)) :
    originalDart Γ mark h2 paths ((repeatedChunks Γ mark h2 paths).equiv x)=
      if (repeatedChunks Γ mark h2 paths).reverse x.1 then
        Γ.reverse (F^[x.2.val.toNat] x.1.1.val.val)
      else F^[x.2.val.toNat] x.1.1.val.val := by
  unfold repeatedChunks ChunkComparisons.repeated Chunking.reindex
  change originalDart Γ mark h2 paths ((splitChunks Γ mark h2 paths).equiv _)=_
  rw [chunk_original]
  simp only [positionEquiv_source,positionEquiv_coordinate,enumeration_color]

omit [Fintype D] in
lemma signed_eq_or_reverse (r s : Bool) (d : D) :
    (if r then Γ.reverse d else d) = (if s then Γ.reverse d else d) ∨
    (if r then Γ.reverse d else d) = Γ.reverse (if s then Γ.reverse d else d) := by
  cases r <;> cases s <;> simp

variable {E : Type*}
    (cmp : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (lo hi : E → ℤ) (hlo : ∀ e,cmp.lo e=(lo e:ℝ)) (hhi : ∀ e,cmp.hi e=(hi e:ℝ))

/-- Reduction survives signed normalization: neither orientation of an actual
paired undirected edge can become the same chain-coordinate position. -/
lemma normalized_reduced
    (hred : ∀ x e,cmp.side x=some e →
      originalDart Γ mark h2 paths x≠originalDart Γ mark h2 paths (cmp.pairing.partner x) ∧
      originalDart Γ mark h2 paths x≠Γ.reverse (originalDart Γ mark h2 paths (cmp.pairing.partner x))) :
    ∀ x a,((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).side x=some a →
      (x.1.1,x.2.val)≠
      ((((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).pairing.partner x).1.1,
       (((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).pairing.partner x).2.val) := by
  intro x a ha heq
  let K := repeatedChunks Γ mark h2 paths
  have he := ((K.side_iff cmp x a.1 a.2.1 a.2.2).mp ha).1
  have hbad := hred (K.equiv x) a.1 he
  rw [←K.partner_image, repeated_original, repeated_original] at hbad
  have hd : F^[x.2.val.toNat] x.1.1.val.val =
      F^[((K.pairing cmp).partner x).2.val.toNat] ((K.pairing cmp).partner x).1.1.val.val := by
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    change x.1.1=((K.pairing cmp).partner x).1.1 at h1
    change x.2.val=((K.pairing cmp).partner x).2.val at h2
    rw [h1,h2]
  rw [hd] at hbad
  exact (signed_eq_or_reverse Γ (K.reverse x.1) (K.reverse ((K.pairing cmp).partner x).1) _).elim hbad.1 hbad.2

/-- Actual graph labels, including reversal, induce precisely the literal
compatibility constraints used by the repeated-block entropy estimates. -/
lemma normalized_compatible {A : Type*} (bar : A → A) (hb : Function.Involutive bar)
    (label : D → A) (hl : ∀ d,label (Γ.reverse d)=bar (label d))
    (hc : ∀ x e,cmp.side x=some e → label (originalDart Γ mark h2 paths x)=
      if cmp.reverse e then bar (label (originalDart Γ mark h2 paths (cmp.pairing.partner x)))
      else label (originalDart Γ mark h2 paths (cmp.pairing.partner x))) :
    ∀ x a,((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).side x=some a →
      label (F^[x.2.val.toNat] x.1.1.val.val)=
      if ((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).reverse a then
        bar (label (F^[(((repeatedChunks Γ mark h2 paths).pairing cmp).partner x).2.val.toNat]
          (((repeatedChunks Γ mark h2 paths).pairing cmp).partner x).1.1.val.val))
      else label (F^[(((repeatedChunks Γ mark h2 paths).pairing cmp).partner x).2.val.toNat]
          (((repeatedChunks Γ mark h2 paths).pairing cmp).partner x).1.1.val.val) := by
  apply (repeatedChunks Γ mark h2 paths).compatible cmp lo hi hlo hhi bar hb
    (fun x => label (originalDart Γ mark h2 paths x))
    (fun x => label (F^[x.2.val.toNat] x.1.1.val.val)) _ hc
  intro x
  rw [repeated_original]
  split_ifs <;> simp only [hl]

/-- A step strictly inside a suppressed chain is an actual reduced graph
passage, with both outgoing ports at precisely the same original vertex. -/
lemma internal_step (d : B) (i : ℕ) (hi : i+1 < len d) :
    Γ.origin (F^[i+1] d.val)=Γ.origin (Γ.reverse (F^[i] d.val)) ∧
      F^[i+1] d.val≠Γ.reverse (F^[i] d.val) := by
  constructor
  · rw [iterate_succ_apply']
    exact turn_origin Γ.origin mark h2 _
  · intro he
    have hn := ChainSuppression.no_internal_mark Γ.reverse τ Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) d.val d.property (by omega : 0 < i+1) hi
    apply hn
    conv_lhs => rw [iterate_succ_apply']
    change τ (τ (Γ.reverse (F^[i] d.val)))=F^[i+1] d.val
    rw [turn_involutive Γ.origin mark h2,he]

/-- Immersion of the literal labelled graph gives the reduced signed chain
words required by every reflection and squared-word argument. -/
lemma normalized_immersed {A : Type*} (bar : A → A) (label : D → A)
    (hl : ∀ d,label (Γ.reverse d)=bar (label d))
    (hinj : ∀ d e,Γ.origin d=Γ.origin e → label d=label e → d=e)
    (c : R) (q : ℤ) (hq : 0≤q) (hq' : q+1<repLength Γ mark h2 c) :
    label (F^[(q+1).toNat] c.val.val)≠bar (label (F^[q.toNat] c.val.val)) := by
  have hn : (q+1).toNat=q.toNat+1 := by omega
  have hi : q.toNat+1<len c.val := by change q+1<len c.val at hq'; omega
  have hs := internal_step Γ mark h2 c.val q.toNat hi
  intro he
  rw [hn,←hl] at he
  exact hs.2 (hinj _ _ hs.1 he)

end TorsionFreeZeroDivisors.ChainChunkTransport

namespace TorsionFreeZeroDivisors.ChainMultiplicity
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2

lemma representative_val (c : R) : representative Γ mark h2 c.val=c := by
  change ((orientation Γ mark h2).symm ((orientation Γ mark h2) (c,false))).1=c
  rw [Equiv.symm_apply_apply]

lemma reverse_oriented (b : B) :
    (S).reverse b=(orientation Γ mark h2) (representative Γ mark h2 b,!(reversed Γ mark h2 b)) := by
  have h := oriented Γ mark h2 b
  cases hr : reversed Γ mark h2 b
  · simp only [hr,Bool.false_eq_true,ite_false] at h
    change (S).reverse b=(S).reverse (representative Γ mark h2 b).val
    exact congrArg (S).reverse h
  · simp only [hr,ite_true] at h
    change (S).reverse b=(representative Γ mark h2 b).val
    calc
      _ = (S).reverse ((S).reverse (representative Γ mark h2 b).val) := congrArg (S).reverse h
      _ = _ := (S).reverse_reverse _

lemma representative_reverse (b : B) : representative Γ mark h2 ((S).reverse b)=representative Γ mark h2 b := by
  rw [reverse_oriented]
  change ((orientation Γ mark h2).symm ((orientation Γ mark h2) _)).1=_
  rw [Equiv.symm_apply_apply]

lemma unsigned (b : B) :
    (if reversed Γ mark h2 b then (S).reverse b else b)=(representative Γ mark h2 b).val := by
  have h := oriented Γ mark h2 b
  cases hr : reversed Γ mark h2 b
  · simpa only [hr,Bool.false_eq_true,ite_false] using h
  · simp only [hr,ite_true] at h ⊢
    calc
      _ = (S).reverse ((S).reverse (representative Γ mark h2 b).val) := congrArg (S).reverse h
      _ = _ := (S).reverse_reverse _

lemma signed_representative (b : B) (r : Bool) :
    representative Γ mark h2 (if r then (S).reverse b else b)=representative Γ mark h2 b := by
  cases r <;> simp only [Bool.false_eq_true,ite_false,ite_true,representative_reverse]

lemma representative_iff (b : B) (c : R) :
    representative Γ mark h2 b=c ↔ b=c.val ∨ b=(S).reverse c.val := by
  constructor
  · intro h
    have hb := oriented Γ mark h2 b
    rw [h] at hb
    cases hr : reversed Γ mark h2 b
    · left; simpa only [hr,Bool.false_eq_true,ite_false] using hb
    · right; simpa only [hr,ite_true] using hb
  · rintro (rfl|rfl)
    · exact representative_val Γ mark h2 c
    · rw [representative_reverse,representative_val]

lemma sign_injective (b : B) : Function.Injective (fun r : Bool => if r then (S).reverse b else b) := by
  intro r t h
  cases r <;> cases t <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h ⊢
  · exact ((S).reverse_ne b h.symm).elim
  · exact ((S).reverse_ne b h).elim

variable {P : Type*} [Fintype P]
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d})

local notation "col" => color Γ mark h2 paths
local notation "tp" => Traversal (chunks Γ mark h2 paths)
local notation "e" => ListStageExponents.edge paths

/-- The incidence fibre used in the Euler-exponent proof is the exact colour
fibre used in the chain/block first moment. Both chain orientations count once. -/
def incidenceEquiv (c : R) :
    {o : (p : P) × (Fin (paths p).length × Bool) // PathIncidences.familyPort (S).reverse e o=c.val} ≃
      {t : tp // col t=c} where
  toFun o := ⟨⟨o.val.1,o.val.2.1⟩,by
    have h := congrArg (representative Γ mark h2) o.property
    change representative Γ mark h2 (if o.val.2.2 then (S).reverse ((paths o.val.1).get o.val.2.1)
      else (paths o.val.1).get o.val.2.1)=representative Γ mark h2 c.val at h
    rw [signed_representative,representative_val] at h
    exact h⟩
  invFun t := ⟨⟨t.val.1,t.val.2,reversed Γ mark h2 ((paths t.val.1).get t.val.2)⟩,by
    change (if reversed Γ mark h2 ((paths t.val.1).get t.val.2) then
      (S).reverse ((paths t.val.1).get t.val.2) else (paths t.val.1).get t.val.2)=c.val
    rw [unsigned]
    exact congrArg Subtype.val t.property⟩
  left_inv := by
    rintro ⟨⟨p,i,r⟩,ho⟩
    apply Subtype.ext
    change (⟨p,i,reversed Γ mark h2 ((paths p).get i)⟩ : (p : P) × (Fin (paths p).length × Bool))=⟨p,i,r⟩
    have hr : reversed Γ mark h2 ((paths p).get i)=r := by
      apply sign_injective Γ mark h2 ((paths p).get i)
      dsimp only
      rw [unsigned]
      have h := congrArg (representative Γ mark h2) ho
      change representative Γ mark h2 (if r then (S).reverse ((paths p).get i)
        else (paths p).get i)=representative Γ mark h2 c.val at h
      rw [signed_representative,representative_val] at h
      rw [h]
      exact ho.symm
    rw [hr]
  right_inv _ := rfl

lemma multiplicity_eq (c : R) :
    StageSubgraphs.multiplicity (S) e c.val=ChunkComparisons.multiplicity col c := by
  classical
  unfold StageSubgraphs.multiplicity IncidenceStages.Passages.multiplicity ChunkComparisons.multiplicity
  simp only [Fintype.card_eq_nat_card]
  exact Nat.card_congr (incidenceEquiv Γ mark h2 paths c)

lemma multiplicity_at (b : B) :
    StageSubgraphs.multiplicity (S) e b=
      ChunkComparisons.multiplicity col (representative Γ mark h2 b) := by
  have h := oriented Γ mark h2 b
  conv_lhs => rw [h]
  split_ifs
  · rw [StageSubgraphs.multiplicity_reverse,multiplicity_eq]
  · exact multiplicity_eq Γ mark h2 paths _

end TorsionFreeZeroDivisors.ChainMultiplicity

end

end OAI
