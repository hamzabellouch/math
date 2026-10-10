import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureSum
import OAI.Geometry.HyperbolicGroups.PictureMirror
import OAI.Geometry.HyperbolicGroups.WordPictureLiteral
import OAI.Geometry.HyperbolicGroups.ElementaryCover
import OAI.Geometry.HyperbolicGroups.VoltagePrismGluing
import OAI.Geometry.HyperbolicGroups.HSpaceFundamental
import OAI.Geometry.HyperbolicGroups.Polygons
import OAI.Geometry.HyperbolicGroups.PolygonTriangleCochains
import OAI.Geometry.HyperbolicGroups.PolygonContraction
import OAI.Geometry.HyperbolicGroups.IndexedPictureClosed
import OAI.Geometry.HyperbolicGroups.IndexedDiskUniqueness
import OAI.Geometry.HyperbolicGroups.IndexedPictureExistence
import OAI.Geometry.HyperbolicGroups.IndexedPictureBasic

namespace OAI

noncomputable section

namespace HyperbolicObstruction

/-! The integral filling value of a literal nullword. This is a consequence
of constructed disks and sphere vanishing, not a replacement hypothesis. -/

namespace IndexedFilling
open HyperbolicObstruction.WordPictures HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  (B : PolygonTarget.Boundary C (E × Bool) V) (weight : C → A)

def SphereZero : Prop := ∀ (P : WordPicture (Set.range B.attachingWord) [])
  (I : Indexing B P), I.chain weight = 0

def HasChain (w : Word E) (z : A) : Prop :=
  ∃ P : WordPicture (Set.range B.attachingWord) w, ∃ I : Indexing B P,
    I.chain weight = -z

def Null (w : Word E) : Prop :=
  PresentedGroup.mk (FreeGroup.mk '' Set.range B.attachingWord) (FreeGroup.mk w) = 1

variable {B weight}
namespace HasChain
lemma empty : HasChain B weight [] 0 := by
  refine ⟨WordPicture.empty _,Indexing.empty B _,?_⟩
  rw [Indexing.empty_chain,neg_zero]

lemma exists_of_null (hrev : B.rev = invLetter) {w : Word E} (h : Null B w) :
    ∃ z, HasChain B weight w z := by
  obtain ⟨P⟩ := literal_picture_existence w h
  obtain ⟨I⟩ := indexing_exists B hrev P
  exact ⟨-I.chain weight,P,I,by rw [neg_neg]⟩

lemma unique (hrev : B.rev = invLetter) (hz : SphereZero B weight)
    {w : Word E} {a b : A} (ha : HasChain B weight w a) (hb : HasChain B weight w b) : a = b := by
  obtain ⟨P,I,hI⟩ := ha
  obtain ⟨Q,J,hJ⟩ := hb
  have hh := Indexing.chain_unique hrev weight hz P Q I J
  rw [hI,hJ] at hh
  exact neg_injective hh

lemma free_unique (hrev : B.rev = invLetter) (hz : SphereZero B weight)
    {u v : Word E} {a b : A} (ha : HasChain B weight u a) (hb : HasChain B weight v b)
    (he : FreeGroup.mk u = FreeGroup.mk v) : a = b := by
  obtain ⟨P,I,hI⟩ := ha
  obtain ⟨Q,J,hJ⟩ := hb
  have hh := Indexing.chain_free_eq hrev weight hz P Q I J he
  rw [hI,hJ] at hh
  exact neg_injective hh

lemma add (hz : SphereZero B weight) {u v : Word E} {a b : A}
    (ha : HasChain B weight u a) (hb : HasChain B weight v b) :
    HasChain B weight (u++v) (a+b) := by
  obtain ⟨P,I,hI⟩ := ha
  obtain ⟨Q,J,hJ⟩ := hb
  by_cases hu : u = []
  · subst u
    have ha : a = 0 := neg_eq_zero.mp (hI.symm.trans (hz P I))
    simpa only [List.nil_append,ha,zero_add] using (show HasChain B weight v b from ⟨Q,J,hJ⟩)
  by_cases hv : v = []
  · subst v
    have hb : b = 0 := neg_eq_zero.mp (hJ.symm.trans (hz Q J))
    simpa only [List.append_nil,hb,add_zero] using (show HasChain B weight u a from ⟨P,I,hI⟩)
  have hp : P.outside ≠ [] := fun h => hu (by rw [←P.word,h]; rfl)
  have hq : Q.outside ≠ [] := fun h => hv (by rw [←Q.word,h]; rfl)
  refine ⟨P.appendNonempty Q hp hq,I.appendNonempty J hp hq,?_⟩
  rw [Indexing.append_chain,hI,hJ,neg_add]

lemma mirror (hrev : B.rev = invLetter) {w : Word E} {a : A}
    (h : HasChain B weight w a) : HasChain B weight (FreeGroup.invRev w) (-a) := by
  obtain ⟨P,I,hI⟩ := h
  exact ⟨P.mirror,I.mirror hrev,by rw [Indexing.mirror_chain,hI]⟩

lemma rotate {w : Word E} {a : A} (h : HasChain B weight w a) (k : ℕ) :
    HasChain B weight (w.rotate k) a := by
  obtain ⟨P,I,hI⟩ := h
  exact ⟨P.rotate k,I.rotate k,hI⟩

lemma freePair (e : E × Bool) : HasChain B weight [e,invLetter e] 0 :=
  ⟨WordPicture.freePair _ e,Indexing.freePair B _ e,by rw [Indexing.freePair_chain,neg_zero]⟩

lemma conjugateLetter (hz : SphereZero B weight) {w : Word E} {a : A}
    (h : HasChain B weight w a) (e : E × Bool) :
    HasChain B weight (e::(w++[invLetter e])) a := by
  have hh := ((h.add hz (freePair (B := B) (weight := weight) (invLetter e))).rotate (w.length+1))
  have he : (w++[invLetter e,invLetter (invLetter e)]).rotate (w.length+1) = e::(w++[invLetter e]) := by
    rw [invLetter_invLetter]
    simpa only [List.append_assoc,List.singleton_append,List.length_append,List.length_singleton]
      using (List.rotate_append_length_eq (w++[invLetter e]) [e])
  simpa only [he,add_zero] using hh

lemma conjugate (hz : SphereZero B weight) {w : Word E} {a : A}
    (h : HasChain B weight w a) (q : Word E) :
    HasChain B weight (q++w++FreeGroup.invRev q) a := by
  induction q with
  | nil => simpa using h
  | cons e q ih =>
    have hh := ih.conjugateLetter hz e
    rw [FreeGroup.invRev_cons,show FreeGroup.invRev [e] = [invLetter e] from rfl]
    simpa only [List.cons_append,List.append_assoc] using hh

lemma cell (hrev : B.rev = invLetter) (c : C) :
    HasChain B weight (B.attachingWord c) (weight c) :=
  ⟨cellDisk B c,cellDiskIndex B hrev c,cellDisk_chain B hrev c weight⟩
end HasChain

/-- Chosen only from genuine, exactly marked genus-zero disks. -/
def value (w : Word E) : A :=
  if h : ∃ z, HasChain B weight w z then h.choose else 0

lemma value_spec (hrev : B.rev = invLetter) {w : Word E} (hw : Null B w) :
    HasChain B weight w (value (B := B) (weight := weight) w) := by
  have h := HasChain.exists_of_null (weight := weight) hrev hw
  simp only [value,dite_eq_left h]
  exact h.choose_spec

lemma value_of_has (hrev : B.rev = invLetter) (hz : SphereZero B weight)
    {w : Word E} {a : A} (h : HasChain B weight w a) : value (B := B) (weight := weight) w = a := by
  have he : ∃ z, HasChain B weight w z := ⟨a,h⟩
  simp only [value,dite_eq_left he]
  exact he.choose_spec.unique hrev hz h

lemma value_cell (hrev : B.rev = invLetter) (hz : SphereZero B weight) (c : C) :
    value (B := B) (weight := weight) (B.attachingWord c) = weight c :=
  value_of_has hrev hz (HasChain.cell hrev c)

end IndexedFilling

/-! Literal walks in a signed incidence graph, with componentwise root paths.
No connectedness or universal-cover assertion is assumed. -/

namespace SignedWalks

section
open HyperbolicObstruction.WordPictures
variable {E V : Type*} (start : E × Bool → V)

inductive Walk : V → V → Word E → Prop
  | nil (x) : Walk x x []
  | cons (e : E × Bool) {y : V} {w : Word E} :
      Walk (start (invLetter e)) y w → Walk (start e) y (e::w)

namespace Walk
variable {start} {x y z : V} {u v : Word E}
lemma nil_iff : Walk start x y [] ↔ x = y := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil _

lemma cons_iff {e : E × Bool} : Walk start x y (e::u) ↔
    x = start e ∧ Walk start (start (invLetter e)) y u := by
  constructor
  · intro h; cases h with | cons e h => exact ⟨rfl,h⟩
  · rintro ⟨rfl,h⟩; exact .cons e h

lemma single (e : E × Bool) : Walk start (start e) (start (invLetter e)) [e] :=
  .cons e (.nil _)

lemma append (hu : Walk start x y u) (hv : Walk start y z v) : Walk start x z (u++v) := by
  induction hu with
  | nil => exact hv
  | cons e h ih => exact .cons e (ih hv)

lemma reverse (h : Walk start x y u) : Walk start y x (FreeGroup.invRev u) := by
  induction h with
  | nil x => exact .nil x
  | cons e h ih =>
    rw [FreeGroup.invRev_cons]
    have hs := single (start := start) (invLetter e)
    rw [invLetter_invLetter] at hs
    exact ih.append hs

lemma head (h : Walk start x y u) {e : E × Bool} {t : Word E} (he : u = e::t) :
    x = start e := (cons_iff.mp (he ▸ h)).1

lemma take_drop (h : Walk start x y u) (n : ℕ) :
    ∃ z, Walk start x z (u.take n) ∧ Walk start z y (u.drop n) := by
  induction h generalizing n with
  | nil x => exact ⟨x,by simpa using (Walk.nil (start := start) x),by simpa using (Walk.nil (start := start) x)⟩
  | cons e h ih =>
    cases n with
    | zero => exact ⟨start e,.nil _,.cons e h⟩
    | succ n =>
      obtain ⟨z,hz,hz'⟩ := ih n
      exact ⟨z,.cons e hz,hz'⟩

lemma get_start (h : Walk start x y u) (i : ℕ) (hi : i < u.length) :
    Walk start x (start u[i]) (u.take i) ∧
      Walk start (start (invLetter u[i])) y (u.drop (i+1)) := by
  obtain ⟨z,hz,hz'⟩ := h.take_drop i
  have he : u.drop i = u[i] :: u.drop (i+1) := List.drop_eq_getElem_cons hi
  rw [he,cons_iff] at hz'
  exact ⟨hz'.1 ▸ hz,hz'.2⟩

lemma adjacent (h : Walk start x y u) (i : ℕ) (hi : i+1 < u.length) :
    start u[i+1] = start (invLetter u[i]) := by
  obtain ⟨hpre,htail⟩ := h.get_start i (by omega)
  have he := List.drop_eq_getElem_cons hi
  rw [he,cons_iff] at htail
  exact htail.1.symm

lemma first (h : Walk start x y u) (hu : 0 < u.length) : start u[0] = x := by
  obtain ⟨hp,ht⟩ := h.get_start 0 hu
  exact (nil_iff.mp hp).symm

lemma last (h : Walk start x y u) (hu : 0 < u.length) :
    start (invLetter u[u.length-1]) = y := by
  obtain ⟨hp,ht⟩ := h.get_start (u.length-1) (by omega)
  have he : u.length-1+1 = u.length := by omega
  rw [he,List.drop_length,nil_iff] at ht
  exact ht

lemma closed_rotate (h : Walk start x x u) (hu : 0 < u.length) (i : Fin u.length) :
    start u[(finRotate u.length i).val] = start (invLetter u[i.val]) := by
  let : NeZero u.length := ⟨by omega⟩
  by_cases hi : i.val+1 < u.length
  · have he : (finRotate u.length i).val = i.val+1 := by
      rw [finRotate_apply]
      simp only [Fin.val_add,Fin.val_one']
      rw [Nat.add_mod_mod,Nat.mod_eq_of_lt hi]
    simpa only [he] using h.adjacent i.val hi
  · have hl : i.val = u.length-1 := by omega
    have he : (finRotate u.length i).val = 0 := by
      rw [finRotate_apply]
      simp only [Fin.val_add,Fin.val_one']
      rw [Nat.add_mod_mod]
      have hh : i.val+1 = u.length := by omega
      rw [hh,Nat.mod_self]
    simpa only [he,hl,h.first hu] using (h.last hu).symm
end Walk

/-- Reachability in the actual signed graph, not equality of word images. -/
def reach : Setoid V where
  r x y := ∃ w, Walk start x y w
  iseqv := ⟨fun x => ⟨[],.nil x⟩,
    fun ⟨w,h⟩ => ⟨FreeGroup.invRev w,h.reverse⟩,
    fun ⟨u,hu⟩ ⟨v,hv⟩ => ⟨u++v,hu.append hv⟩⟩

def root (x : V) : V := Quotient.out (Quotient.mk (reach start) x)
lemma root_reach (x : V) : (reach start).r (root start x) x :=
  Quotient.exact (Quotient.out_eq _)

def rootWord (x : V) : Word E := (root_reach start x).choose
lemma rootWord_walk (x : V) : Walk start (root start x) x (rootWord start x) :=
  (root_reach start x).choose_spec

lemma root_eq {x y : V} (h : (reach start).r x y) : root start x = root start y :=
  congrArg Quotient.out (Quotient.sound h)

lemma edge_root (e : E × Bool) : root start (start e) = root start (start (invLetter e)) :=
  root_eq start ⟨[e],Walk.single e⟩

def correction (e : E × Bool) : Word E :=
  rootWord start (start e) ++ [e] ++ FreeGroup.invRev (rootWord start (start (invLetter e)))

lemma correction_walk (e : E × Bool) :
    Walk start (root start (start e)) (root start (start e)) (correction start e) := by
  have h := ((rootWord_walk start (start e)).append (Walk.single e)).append
    (rootWord_walk start (start (invLetter e))).reverse
  rw [←edge_root start e] at h
  exact h

end

open HyperbolicObstruction.WordPictures
variable {E V : Type*} {start : E × Bool → V}

lemma Walk.ofFn_vertices (n : ℕ) (f : Fin n → E × Bool) (vs : ℕ → V)
    (hs : ∀ i, start (f i) = vs i.val)
    (ht : ∀ i, start (invLetter (f i)) = vs (i.val+1)) :
    Walk start (vs 0) (vs n) (List.ofFn f) := by
  induction n generalizing vs with
  | zero => exact .nil _
  | succ n ih =>
    have hh := ih (fun i => f i.succ) (fun k => vs (k+1))
      (fun i => hs i.succ) (fun i => by simpa only [Fin.val_succ] using ht i.succ)
    have ht0 := ht (0 : Fin (n+1))
    have hs0 := hs (0 : Fin (n+1))
    simp only [Fin.val_zero,zero_add] at ht0 hs0
    rw [←ht0] at hh
    have hc := Walk.cons (f 0) hh
    rw [hs0] at hc
    simpa only [List.ofFn_succ] using hc

lemma Walk.ofFn_closed {n : ℕ} (hn : 0 < n) (f : Fin n → E × Bool)
    (hc : ∀ i, start (f (finRotate n i)) = start (invLetter (f i))) :
    Walk start (start (f ⟨0,hn⟩)) (start (f ⟨0,hn⟩)) (List.ofFn f) := by
  let : NeZero n := ⟨by omega⟩
  let vs : ℕ → V := fun k => start (f ⟨k%n,Nat.mod_lt _ hn⟩)
  have hs : ∀ i, start (f i) = vs i.val := by
    intro i
    dsimp [vs]
    congr 2
    exact (Fin.ext (Nat.mod_eq_of_lt i.isLt)).symm
  have ht : ∀ i, start (invLetter (f i)) = vs (i.val+1) := by
    intro i
    rw [←hc]
    dsimp [vs]
    congr 2
    rw [finRotate_apply]
    apply Fin.ext
    simp only [Fin.val_add,Fin.val_one',Nat.add_mod_mod]
  simpa only [vs,Nat.zero_mod,Nat.mod_self] using Walk.ofFn_vertices n f vs hs ht

/-- Product of rooted edge corrections is exactly the rooted original path;
all intermediate paths cancel in the free group, before taking any quotient. -/
lemma correction_telescope (root : V → Word E) {x y : V} {u : Word E}
    (h : Walk start x y u) :
    FreeGroup.mk (u.flatMap (fun e => root (start e) ++ [e] ++ FreeGroup.invRev (root (start (invLetter e))))) =
      FreeGroup.mk (root x ++ u ++ FreeGroup.invRev (root y)) := by
  induction h with
  | nil x =>
    simp only [List.flatMap_nil,List.append_nil]
    rw [←FreeGroup.mul_mk,←FreeGroup.inv_mk,mul_inv_cancel]
    rfl
  | cons e h ih =>
    simp only [List.flatMap_cons]
    rw [←FreeGroup.mul_mk,ih]
    simp only [←FreeGroup.mul_mk,←FreeGroup.inv_mk]
    change (FreeGroup.mk (root (start e)) * FreeGroup.mk [e] * (FreeGroup.mk (root (start (invLetter e))))⁻¹) *
      (FreeGroup.mk (root (start (invLetter e))) * FreeGroup.mk _ * (FreeGroup.mk (root _))⁻¹) =
      FreeGroup.mk (root (start e)) * (FreeGroup.mk [e] * FreeGroup.mk _) * (FreeGroup.mk (root _))⁻¹
    group

lemma correction_reverse (root : V → Word E) (e : E × Bool) :
    FreeGroup.mk (root (start (invLetter e)) ++ [invLetter e] ++ FreeGroup.invRev (root (start (invLetter (invLetter e))))) =
      (FreeGroup.mk (root (start e) ++ [e] ++ FreeGroup.invRev (root (start (invLetter e)))))⁻¹ := by
  simp only [invLetter_invLetter,←FreeGroup.mul_mk,←FreeGroup.inv_mk,mul_inv_rev,inv_inv]
  have he : FreeGroup.mk [invLetter e] = (FreeGroup.mk [e])⁻¹ := by
    change FreeGroup.mk (FreeGroup.invRev [e]) = _
    exact FreeGroup.inv_mk.symm
  rw [he]
  group

end SignedWalks

/-! A literal disk-chain left inverse for the integral cell boundary. The
rooted-edge construction avoids assuming an arbitrary-cycle sphere producer. -/

namespace IndexedFilling
open HyperbolicObstruction.WordPictures HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch SignedWalks
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  (B : PolygonTarget.Boundary C (E × Bool) V) (weight : C → A)

def letterChain (e : E × Bool) : E →₀ ℤ :=
  if e.2 then Finsupp.single e.1 1 else -Finsupp.single e.1 1

def cellBoundary (c : C) : E →₀ ℤ := ∑ i, letterChain (B.label c i)
def boundary : (C →₀ ℤ) →ₗ[ℤ] (E →₀ ℤ) := Finsupp.linearCombination ℤ (cellBoundary B)

variable (hrev : B.rev = invLetter) (hz : SphereZero B weight)
  (hloop : ∀ x w, Walk B.start x x w → Null B w)

include hloop in
lemma correction_null (e : E × Bool) : Null B (correction B.start e) :=
  hloop _ _ (correction_walk B.start e)

variable {B weight}
lemma HasChain.words {ws : List (Word E)} {a : Word E → A}
    (hz : SphereZero B weight) (h : ∀ w ∈ ws, HasChain B weight w (a w)) :
    HasChain B weight ws.flatten (ws.map a).sum := by
  induction ws with
  | nil => exact HasChain.empty
  | cons w ws ih =>
    simpa only [List.flatten_cons,List.map_cons,List.sum_cons] using
      (h w (by simp)).add hz (ih (fun v hv => h v (by simp [hv])))

lemma HasChain.flatMap {T : Type*} {xs : List T} {f : T → Word E} {a : T → A}
    (hz : SphereZero B weight) (h : ∀ x ∈ xs, HasChain B weight (f x) (a x)) :
    HasChain B weight (xs.flatMap f) (xs.map a).sum := by
  induction xs with
  | nil => exact HasChain.empty
  | cons x xs ih =>
    simpa only [List.flatMap_cons,List.map_cons,List.sum_cons] using
      (h x (by simp)).add hz (ih (fun y hy => h y (by simp [hy])))

variable (B weight)
def edgeValue (e : E) : A := value (B := B) (weight := weight) (correction B.start (e,true))
def leftInverse : (E →₀ ℤ) →ₗ[ℤ] A := Finsupp.linearCombination ℤ (edgeValue B weight)

include hrev hz hloop in
lemma correction_value_reverse (e : E × Bool) :
    value (B := B) (weight := weight) (correction B.start (invLetter e)) =
      -value (B := B) (weight := weight) (correction B.start e) := by
  have hp := value_spec (weight := weight) hrev (correction_null B hloop e)
  have hn := value_spec (weight := weight) hrev (correction_null B hloop (invLetter e))
  apply hn.free_unique hrev hz (hp.mirror hrev)
  exact (correction_reverse (rootWord B.start) e).trans FreeGroup.inv_mk

include hrev hz hloop in
lemma leftInverse_letter (e : E × Bool) :
    leftInverse B weight (letterChain e) = value (B := B) (weight := weight) (correction B.start e) := by
  rcases e with ⟨e,b⟩
  cases b with
  | true => simp [leftInverse,letterChain,edgeValue]
  | false =>
    have hh := correction_value_reverse B weight hrev hz hloop (e,true)
    simpa only [leftInverse,letterChain,Bool.false_eq_true,ite_false,map_neg,
      Finsupp.linearCombination_single,one_smul,edgeValue,invLetter,Bool.not_true] using hh.symm

include hrev hz hloop in
lemma leftInverse_cell (c : C) : leftInverse B weight (cellBoundary B c) = weight c := by
  have hc : Walk B.start (B.start (B.label c ⟨0,B.positive c⟩))
      (B.start (B.label c ⟨0,B.positive c⟩)) (B.attachingWord c) :=
    Walk.ofFn_closed (B.positive c) (B.label c) (by simpa only [hrev] using B.closed c)
  have hsum := HasChain.flatMap (xs := B.attachingWord c) hz
    (fun e _ => value_spec (weight := weight) hrev (correction_null B hloop e))
  have hcell := (HasChain.cell (weight := weight) hrev c).conjugate hz
    (rootWord B.start (B.start (B.label c ⟨0,B.positive c⟩)))
  have he := hsum.free_unique hrev hz hcell (correction_telescope (rootWord B.start) hc)
  simp only [cellBoundary,map_sum,leftInverse_letter B weight hrev hz hloop]
  simpa only [PolygonTarget.Boundary.attachingWord,List.map_ofFn,List.sum_ofFn,Function.comp_def] using he

include hrev hz hloop in
lemma leftInverse_boundary (z : C →₀ ℤ) :
    leftInverse B weight (boundary B z) = Finsupp.linearCombination ℤ weight z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single c a =>
    simp only [boundary,Finsupp.linearCombination_single,map_smul,
      leftInverse_cell B weight hrev hz hloop]

/-- Exact d₂ injectivity, once closed graph loops have actual disks and every
closed genus-zero diagram has zero full independent-cell chain. -/
theorem boundary_injective (hrev : B.rev = invLetter)
    (hz : SphereZero B (fun c => Finsupp.single c (1 : ℤ)))
    (hloop : ∀ x w, Walk B.start x x w → Null B w) :
    Function.Injective (boundary B) := by
  have hh (z : C →₀ ℤ) := leftInverse_boundary B (fun c => Finsupp.single c (1 : ℤ)) hrev hz hloop z
  have hid : Finsupp.linearCombination ℤ (fun c => Finsupp.single c (1 : ℤ)) = (LinearMap.id : (C →₀ ℤ) →ₗ[ℤ] (C →₀ ℤ)) := by
    ext c a
    simp
  rw [hid] at hh
  exact Function.LeftInverse.injective hh

end IndexedFilling

/-! Subdivision of permutation cycles, with exact orbit-count preservation. -/
namespace PictureSwitch

section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D] [DecidableEq D]

namespace PermInsertion
variable (f : Perm D) (p : D → Prop)

/-- Insert exactly one separately indexed point after every point satisfying p. -/
def perm : Perm (D ⊕ Subtype p) where
  toFun := fun x => match x with
    | .inl d => if h : p d then .inr ⟨d,h⟩ else .inl (f d)
    | .inr t => .inl (f t.val)
  invFun := fun x => match x with
    | .inl d => if h : p (f⁻¹ d) then .inr ⟨f⁻¹ d,h⟩ else .inl (f⁻¹ d)
    | .inr t => .inl t.val
  left_inv := by
    rintro (d|t)
    · by_cases h : p d <;> simp [h]
    · simp [t.property]
  right_inv := by
    rintro (d|t)
    · by_cases h : p (f.symm d) <;> simp [h]
    · simp [t.property]

def collapse : D ⊕ Subtype p → D := Sum.elim id Subtype.val

omit [Fintype D] [DecidableEq D] in
lemma collapse_step (x : D ⊕ Subtype p) :
    f.SameCycle (collapse p x) (collapse p (perm f p x)) := by
  rcases x with d|t
  · by_cases h : p d
    · simp only [perm,Equiv.coe_fn_mk,dite_eq_left h,collapse,Sum.elim_inl,Sum.elim_inr,id_eq]
      exact SameCycle.rfl
    · simp only [perm,Equiv.coe_fn_mk,dite_eq_right h,collapse,Sum.elim_inl,id_eq]
      exact SameCycle.rfl.apply_right
  · exact SameCycle.rfl.apply_right

omit [DecidableEq D] in
lemma collapse_sameCycle {x y : D ⊕ Subtype p} (h : (perm f p).SameCycle x y) :
    f.SameCycle (collapse p x) (collapse p y) :=
  (sameCycle_le_of_apply (s := (SameCycle.setoid f).comap (collapse p))
    (collapse_step f p)) h

omit [Fintype D] [DecidableEq D] in
lemma base_step (d : D) : (perm f p).SameCycle (.inl d) (.inl (f d)) := by
  by_cases h : p d
  · have he : perm f p (.inl d) = .inr ⟨d,h⟩ := by simp only [perm,Equiv.coe_fn_mk,dite_eq_left h]
    have he' : perm f p (.inr ⟨d,h⟩) = .inl (f d) := rfl
    have hh := (SameCycle.rfl (f := perm f p) (x := Sum.inl d)).apply_right.apply_right
    rwa [he,he'] at hh
  · have he : perm f p (.inl d) = .inl (f d) := by simp only [perm,Equiv.coe_fn_mk,dite_eq_right h]
    exact he ▸ (SameCycle.rfl (f := perm f p) (x := Sum.inl d)).apply_right

omit [DecidableEq D] in
lemma base_sameCycle {x y : D} (h : f.SameCycle x y) :
    (perm f p).SameCycle (.inl x) (.inl y) :=
  (sameCycle_le_of_apply (s := (SameCycle.setoid (perm f p)).comap Sum.inl)
    (base_step f p)) h

omit [Fintype D] [DecidableEq D] in
lemma collapse_base_cycle (x : D ⊕ Subtype p) :
    (perm f p).SameCycle (.inl (collapse p x)) x := by
  rcases x with d|t
  · exact SameCycle.rfl
  · have he : perm f p (.inl t.val) = .inr t := by simp only [perm,Equiv.coe_fn_mk,dite_eq_left t.property]
    have hh := (SameCycle.rfl (f := perm f p) (x := Sum.inl t.val)).apply_right
    rw [he] at hh
    exact hh

/-- Subdivision gives a genuine equivalence of orbit quotients, including
fixed points and the empty type. -/
def orbitEquiv : Quotient (SameCycle.setoid (perm f p)) ≃ Quotient (SameCycle.setoid f) where
  toFun := Quotient.map (collapse p) (fun _ _ => collapse_sameCycle f p)
  invFun := Quotient.map Sum.inl (fun _ _ => base_sameCycle f p)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h x => exact Quotient.sound (collapse_base_cycle f p x)
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h x => rfl

lemma cycles_eq : cycles (perm f p) = cycles f := by
  rw [cycles_eq_card_classes,cycles_eq_card_classes]
  exact_mod_cast Nat.card_congr (orbitEquiv f p)

end PermInsertion
end

/-! Literal radial triangulation of the free polygon faces of a finite map.
This section concerns genuine permutations; no topological genus assertion is
included in the input. -/
section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

lemma cycles_equiv (f : Perm D) (g : Perm E) (e : D ≃ E)
    (h : ∀ x, e (f x) = g (e x)) : cycles f = cycles g := by
  have hs : ∀ x, e.symm (g x) = f (e.symm x) := by
    intro x
    apply e.injective
    simp only [apply_symm_apply,h]
  let q : Quotient (SameCycle.setoid f) ≃ Quotient (SameCycle.setoid g) := {
    toFun := Quotient.map e (fun _ _ => semiconj_perm_sameCycle h)
    invFun := Quotient.map e.symm (fun _ _ => semiconj_perm_sameCycle hs)
    left_inv := by
      intro x; induction x using Quotient.inductionOn with
      | h x => simp only [Quotient.map_mk,symm_apply_apply]
    right_inv := by
      intro x; induction x using Quotient.inductionOn with
      | h x => simp only [Quotient.map_mk,apply_symm_apply] }
  rw [cycles_eq_card_classes,cycles_eq_card_classes]
  exact_mod_cast Nat.card_congr q

namespace ConeExpansion
variable (M : PictureMap D) (p : D → Prop) (hf : ∀ d, p (M.face d) ↔ p d)

abbrev Point := D ⊕ (Subtype p ⊕ Subtype p)
def freeFace : Perm (Subtype p) := M.face.subtypePerm hf

def face : Perm (Point p) where
  toFun := fun x => match x with
    | .inl d => if h : p d then .inr (.inl ⟨d,h⟩) else .inl (M.face d)
    | .inr (.inl t) => .inr (.inr t)
    | .inr (.inr t) => .inl t.val
  invFun := fun x => match x with
    | .inl d => if h : p d then .inr (.inr ⟨d,h⟩) else .inl (M.face.symm d)
    | .inr (.inl t) => .inl t.val
    | .inr (.inr t) => .inr (.inl t)
  left_inv := by
    rintro (d|(t|t))
    · by_cases h : p d
      · simp [h]
      · simp [h,(hf d).not.mpr h]
    · rfl
    · simp [t.property]
  right_inv := by
    rintro (d|(t|t))
    · by_cases h : p d
      · simp [h]
      · have h' : ¬ p (M.face.symm d) := by
          apply (hf (M.face.symm d)).not.mp
          simpa only [apply_symm_apply] using h
        simp [h,h']
    · simp [t.property]
    · rfl

def edge : Perm (Point p) where
  toFun := fun x => match x with
    | .inl d => .inl (M.edge d)
    | .inr (.inl t) => .inr (.inr (freeFace M p hf t))
    | .inr (.inr t) => .inr (.inl ((freeFace M p hf).symm t))
  invFun := fun x => match x with
    | .inl d => .inl (M.edge d)
    | .inr (.inl t) => .inr (.inr (freeFace M p hf t))
    | .inr (.inr t) => .inr (.inl ((freeFace M p hf).symm t))
  left_inv := by rintro (d|(t|t)) <;> simp [M.edge_edge]
  right_inv := by rintro (d|(t|t)) <;> simp [M.edge_edge]

def map : PictureMap (Point p) where
  face := face M p hf
  edge := edge M p hf
  edge_sq := by ext x; rcases x with d|(t|t) <;> simp [edge,M.edge_edge]
  edge_ne := by
    rintro (d|(t|t)) h
    · exact M.edge_ne d (Sum.inl.inj h)
    · exact Sum.inr_ne_inl (Sum.inr.inj h)
    · exact Sum.inl_ne_inr (Sum.inr.inj h)

/-- Arrange the old vertices, their inserted corners, and the new apices. -/
def vertexEquiv : ((D ⊕ {d // p (M.edge d)}) ⊕ Subtype p) ≃ Point p where
  toFun := fun x => match x with
    | .inl (.inl d) => .inl d
    | .inl (.inr t) => .inr (.inl ⟨M.edge t.val,t.property⟩)
    | .inr t => .inr (.inr t)
  invFun := fun x => match x with
    | .inl d => .inl (.inl d)
    | .inr (.inl t) => .inl (.inr ⟨M.edge t.val,by simpa only [M.edge_edge] using t.property⟩)
    | .inr (.inr t) => .inr t
  left_inv := by rintro ((d|t)|t) <;> simp [M.edge_edge]
  right_inv := by rintro (d|(t|t)) <;> simp [M.edge_edge]

omit [Fintype D] [DecidableEq D] in
lemma vertex_equiv (x : (D ⊕ {d // p (M.edge d)}) ⊕ Subtype p) :
    vertexEquiv M p (Equiv.sumCongr (PermInsertion.perm M.vertex (fun d => p (M.edge d)))
       (freeFace M p hf)⁻¹ x) = (map M p hf).vertex (vertexEquiv M p x) := by
  rcases x with (d|t)|t
  · by_cases h : p (M.edge d) <;> simp [vertexEquiv,PermInsertion.perm,map,PictureMap.vertex,face,edge,h]
  · simp [vertexEquiv,PermInsertion.perm,map,PictureMap.vertex,face,edge,freeFace]
  · rfl

lemma vertex_cycles : cycles (map M p hf).vertex = cycles M.vertex + cycles (freeFace M p hf) := by
  rw [← cycles_equiv _ _ (vertexEquiv M p) (vertex_equiv M p hf),cycles_sum,
    PermInsertion.cycles_eq,cycles_inverse]

def frozenFace : Perm {d // ¬ p d} := M.face.subtypePerm (fun d => (hf d).not)

def faceClass : Point p → Quotient (SameCycle.setoid (frozenFace M p hf)) ⊕ Subtype p
  | .inl d => if h : p d then .inr ⟨d,h⟩ else .inl (Quotient.mk _ ⟨d,h⟩)
  | .inr (.inl t) => .inr t
  | .inr (.inr t) => .inr t

omit [Fintype D] [DecidableEq D] in
lemma faceClass_step (x : Point p) : faceClass M p hf x = faceClass M p hf (face M p hf x) := by
  rcases x with d|(t|t)
  · by_cases h : p d
    · simp [face,faceClass,h]
    · simp only [face,Equiv.coe_fn_mk,dite_eq_right h,faceClass,dite_eq_right ((hf d).not.mpr h)]
      apply congrArg Sum.inl
      apply Quotient.sound
      exact (SameCycle.rfl (f := frozenFace M p hf) (x := ⟨d,h⟩)).apply_right
  · rfl
  · simp [face,faceClass,t.property]

omit [Fintype D] [DecidableEq D] in
lemma frozen_step (x : {d // ¬ p d}) :
    (Sum.inl ((frozenFace M p hf) x).val : Point p) = face M p hf (.inl x.val) := by
  simp [face,frozenFace,x.property]

/-- New triangular faces are indexed by the old free sides, not merely by
an unlabelled area count. All other face orbits are literally unchanged. -/
def faceOrbitEquiv : Quotient (SameCycle.setoid (face M p hf)) ≃
    (Quotient (SameCycle.setoid (frozenFace M p hf)) ⊕ Subtype p) where
  toFun := Quotient.lift (faceClass M p hf)
    (fun _ _ h => (sameCycle_le_of_apply (s := Setoid.ker (faceClass M p hf))
      (faceClass_step M p hf)) h)
  invFun := Sum.elim
    (Quotient.map (fun x : {d // ¬ p d} => (Sum.inl x.val : Point p))
      (fun a b h => (semiconj_perm_sameCycle (f := frozenFace M p hf)
        (t := face M p hf) (j := fun x => Sum.inl x.val) (frozen_step M p hf) h)) :
        Quotient (SameCycle.setoid (frozenFace M p hf)) → Quotient (SameCycle.setoid (face M p hf)))
    (fun t => Quotient.mk (SameCycle.setoid (face M p hf)) (.inl t.val))
  left_inv := by
    intro x; induction x using Quotient.inductionOn with
    | h x =>
      rcases x with d|(t|t)
      · by_cases h : p d <;> simp [faceClass,h]
      · change Quotient.mk (SameCycle.setoid (face M p hf)) (.inl t.val) = Quotient.mk _ (.inr (.inl t))
        apply Quotient.sound
        change (face M p hf).SameCycle _ _
        have h := (SameCycle.rfl (f := face M p hf) (x := Sum.inl t.val)).apply_right
        simpa [face,t.property] using h
      · change Quotient.mk (SameCycle.setoid (face M p hf)) (.inl t.val) = Quotient.mk _ (.inr (.inr t))
        apply Quotient.sound
        change (face M p hf).SameCycle _ _
        have h := (SameCycle.rfl (f := face M p hf) (x := Sum.inl t.val)).apply_right.apply_right
        simpa [face,t.property] using h
  right_inv := by
    rintro (x|t)
    · induction x using Quotient.inductionOn with
      | h x => simp [faceClass,x.property]
    · simp [faceClass,t.property]

lemma face_cycles : cycles (map M p hf).face = cycles (frozenFace M p hf) + Fintype.card (Subtype p) := by
  rw [cycles_eq_card_classes,cycles_eq_card_classes]
  change (Nat.card (Quotient (SameCycle.setoid (face M p hf))) : ℤ) = _
  rw [Nat.card_congr (faceOrbitEquiv M p hf),Nat.card_sum,Nat.cast_add,Nat.card_eq_fintype_card (α := Subtype p)]

lemma euler_eq : (map M p hf).euler = M.euler := by
  have hc := cycles_subtype_split M.face hf
  change cycles M.face = cycles (freeFace M p hf) + cycles (frozenFace M p hf) at hc
  rw [PictureMap.euler,vertex_cycles,face_cycles]
  change cycles M.vertex + cycles (freeFace M p hf) +
    (cycles (frozenFace M p hf) + Fintype.card (Subtype p)) -
    (Fintype.card (D ⊕ (Subtype p ⊕ Subtype p)) : ℤ) / 2 = _
  simp only [Fintype.card_sum,Nat.cast_add]
  unfold PictureMap.euler
  omega

def collapse : Point p → D := Sum.elim id (Sum.elim Subtype.val Subtype.val)

omit [DecidableEq D] in
lemma collapse_face (x : Point p) : M.components (collapse p x) (collapse p (face M p hf x)) := by
  rcases x with d|(t|t)
  · by_cases h : p d
    · simp only [face,Equiv.coe_fn_mk,dite_eq_left h,collapse,Sum.elim_inl,Sum.elim_inr,id_eq]
      exact M.components.refl _
    · simp only [face,Equiv.coe_fn_mk,dite_eq_right h,collapse,Sum.elim_inl,id_eq]
      exact M.face_le_components SameCycle.rfl.apply_right
  · exact M.components.refl _
  · exact M.components.refl _

omit [DecidableEq D] in
lemma collapse_edge (x : Point p) : M.components (collapse p x) (collapse p (edge M p hf x)) := by
  rcases x with d|(t|t)
  · exact M.edge_le_components SameCycle.rfl.apply_right
  · exact M.face_le_components SameCycle.rfl.apply_right
  · have h := (SameCycle.rfl (f := M.face) (x := M.face.symm t.val)).apply_right.symm
    simp only [apply_symm_apply] at h
    exact M.face_le_components h

omit [DecidableEq D] in
lemma components_bound : Nat.card (Quotient M.components) ≤ Nat.card (Quotient (map M p hf).components) := by
  have hh : (map M p hf).components ≤ M.components.comap (collapse p) :=
    (map M p hf).components_le (collapse_face M p hf) (collapse_edge M p hf)
  let q : Quotient (map M p hf).components → Quotient M.components :=
    Quotient.map (collapse p) (fun _ _ h => hh h)
  have hq : Function.Surjective q := by
    intro x; obtain ⟨d,rfl⟩ := Quotient.exists_rep x
    exact ⟨Quotient.mk _ (.inl d),rfl⟩
  exact Nat.card_le_card_of_surjective q hq

/-- Removing all radial stars from a genus-zero triangulated side-pairing
preserves genus zero. This is a consequence of the permutation counts. -/
theorem genusZero_of_expansion (h : (map M p hf).GenusZero) : M.GenusZero := by
  have h₁ := euler_eq M p hf
  have h₂ := components_bound M p hf
  have h₃ := M.euler_le
  unfold PictureMap.GenusZero at h ⊢
  omega

end ConeExpansion
end

section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
namespace PictureMap
variable (M : PictureMap D) (N : PictureMap E) (e : D ≃ E)
  (hf : ∀ x, e (M.face x) = N.face (e x)) (he : ∀ x, e (M.edge x) = N.edge (e x))

include hf he

lemma euler_equiv : M.euler = N.euler := by
  have hv : ∀ x, e (M.vertex x) = N.vertex (e x) := by
    intro x; simp only [vertex,mul_apply,hf,he]
  rw [euler,euler,cycles_equiv M.vertex N.vertex e hv,cycles_equiv M.face N.face e hf,
    Fintype.card_congr e]

omit [DecidableEq D] [DecidableEq E] in
lemma components_equiv (x y : D) : M.components x y ↔ N.components (e x) (e y) := by
  have h₁ : M.components ≤ N.components.comap e := by
    apply M.components_le
    · intro x; change N.components (e x) (e (M.face x)); rw [hf]
      exact N.face_le_components SameCycle.rfl.apply_right
    · intro x; change N.components (e x) (e (M.edge x)); rw [he]
      exact N.edge_le_components SameCycle.rfl.apply_right
  have hf' : ∀ x, e.symm (N.face x) = M.face (e.symm x) := by
    intro x; apply e.injective; simp only [apply_symm_apply,hf]
  have he' : ∀ x, e.symm (N.edge x) = M.edge (e.symm x) := by
    intro x; apply e.injective; simp only [apply_symm_apply,he]
  have h₂ : N.components ≤ M.components.comap e.symm := by
    apply N.components_le
    · intro x; change M.components (e.symm x) (e.symm (N.face x)); rw [hf']
      exact M.face_le_components SameCycle.rfl.apply_right
    · intro x; change M.components (e.symm x) (e.symm (N.edge x)); rw [he']
      exact M.edge_le_components SameCycle.rfl.apply_right
  exact ⟨fun h => h₁ h,fun h => by simpa only [Setoid.comap_rel,symm_apply_apply] using h₂ h⟩

omit [DecidableEq D] [DecidableEq E] in
lemma components_card_equiv : Nat.card (Quotient M.components) = Nat.card (Quotient N.components) := by
  let q : Quotient M.components ≃ Quotient N.components := {
    toFun := Quotient.map e (fun _ _ h => (components_equiv M N e hf he _ _).mp h)
    invFun := Quotient.map e.symm (by
      intro x y h
      apply (components_equiv M N e hf he _ _).mpr
      simpa only [apply_symm_apply] using h)
    left_inv := by
      intro x; induction x using Quotient.inductionOn with
      | h x => simp only [Quotient.map_mk,symm_apply_apply]
    right_inv := by
      intro x; induction x using Quotient.inductionOn with
      | h x => simp only [Quotient.map_mk,apply_symm_apply] }
  exact Nat.card_congr q

lemma genusZero_equiv : M.GenusZero ↔ N.GenusZero := by
  simp only [GenusZero,euler_equiv M N e hf he,components_card_equiv M N e hf he]

end PictureMap
end

/-! Exact contraction of radial triangle stars. -/
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The three roles are old side (0), incoming radial side (1), and outgoing
radial side (2). Frozen polygons have only old sides. These are local incidence
conditions on an existing side-pairing, not a genus or chain assumption. -/
structure TriangleMarking (M : PictureMap D) where
  top : D → Bool
  role : D → Fin 3
  top_face : ∀ x, top (M.face x) = top x
  frozen : ∀ x, top x = false → role x = 0
  turn : ∀ x, top x = true → role (M.face x) = finRotate 3 (role x)
  period : ∀ x, top x = true → M.face (M.face (M.face x)) = x
  edge0 : ∀ x, role x = 0 → role (M.edge x) = 0
  edge1 : ∀ x, role x = 1 → role (M.edge x) = 2
  edge2 : ∀ x, role x = 2 → role (M.edge x) = 1

namespace TriangleMarking
variable {M : PictureMap D} (H : TriangleMarking M)
abbrev Base := {x // H.role x = 0}

def free (x : H.Base) : Prop := H.top x.val = true

omit [Fintype D] [DecidableEq D] in
lemma top_of_role {x : D} (h : H.role x ≠ 0) : H.top x = true := by
  cases htop : H.top x with
  | false => exact False.elim (h (H.frozen x htop))
  | true => rfl

omit [Fintype D] [DecidableEq D] in
lemma top_prev (x : D) : H.top (M.face.symm x) = H.top x := by
  have h := H.top_face (M.face.symm x)
  simpa only [apply_symm_apply] using h.symm

omit [Fintype D] [DecidableEq D] in
lemma prev_eq {x : D} (h : H.top x = true) : M.face.symm x = M.face (M.face x) := by
  apply M.face.injective
  rw [apply_symm_apply,H.period x h]

omit [Fintype D] [DecidableEq D] in
lemma role_next0 {x : D} (ht : H.top x = true) (h : H.role x = 0) : H.role (M.face x) = 1 := by
  rw [H.turn x ht,h]; rfl
omit [Fintype D] [DecidableEq D] in
lemma role_next1 {x : D} (h : H.role x = 1) : H.role (M.face x) = 2 := by
  have ht := H.top_of_role (by rw [h]; decide)
  rw [H.turn x ht,h]; rfl
omit [Fintype D] [DecidableEq D] in
lemma role_next2 {x : D} (h : H.role x = 2) : H.role (M.face x) = 0 := by
  have ht := H.top_of_role (by rw [h]; decide)
  rw [H.turn x ht,h]; rfl
omit [Fintype D] [DecidableEq D] in
lemma role_prev0 {x : D} (ht : H.top x = true) (h : H.role x = 0) : H.role (M.face.symm x) = 2 := by
  rw [H.prev_eq ht]
  exact H.role_next1 (H.role_next0 ht h)
omit [Fintype D] [DecidableEq D] in
lemma role_prev1 {x : D} (h : H.role x = 1) : H.role (M.face.symm x) = 0 := by
  rw [H.prev_eq (H.top_of_role (by rw [h]; decide))]
  exact H.role_next2 (H.role_next1 h)
omit [Fintype D] [DecidableEq D] in
lemma role_prev2 {x : D} (h : H.role x = 2) : H.role (M.face.symm x) = 1 := by
  have ht := H.top_of_role (by rw [h]; decide)
  rw [H.prev_eq ht]
  exact H.role_next0 ((H.top_face x).trans ht) (H.role_next2 h)

def next (x : D) : D := if H.top x then M.face (M.edge (M.face x)) else M.face x
def prev (x : D) : D := if H.top x then M.face.symm (M.edge (M.face.symm x)) else M.face.symm x

omit [Fintype D] [DecidableEq D] in
lemma next_role (x : H.Base) : H.role (H.next x.val) = 0 := by
  by_cases ht : H.top x.val = true
  · simp only [next,ht,ite_true]
    exact H.role_next2 (H.edge1 _ (H.role_next0 ht x.property))
  · have hf : H.top x.val = false := Bool.eq_false_iff.mpr ht
    simp only [next,hf,Bool.false_eq_true,ite_false]
    exact H.frozen _ ((H.top_face _).trans hf)

omit [Fintype D] [DecidableEq D] in
lemma next_top (x : H.Base) : H.top (H.next x.val) = H.top x.val := by
  by_cases ht : H.top x.val = true
  · simp only [next,ht,ite_true,H.top_face]
    apply H.top_of_role
    rw [H.edge1 _ (H.role_next0 ht x.property)]; decide
  · have hf : H.top x.val = false := Bool.eq_false_iff.mpr ht
    simp only [next,hf,Bool.false_eq_true,ite_false,H.top_face]

omit [Fintype D] [DecidableEq D] in
lemma prev_role (x : H.Base) : H.role (H.prev x.val) = 0 := by
  by_cases ht : H.top x.val = true
  · simp only [prev,ht,ite_true]
    exact H.role_prev1 (H.edge2 _ (H.role_prev0 ht x.property))
  · have hf : H.top x.val = false := Bool.eq_false_iff.mpr ht
    simp only [prev,hf,Bool.false_eq_true,ite_false]
    exact H.frozen _ ((H.top_prev _).trans hf)

omit [Fintype D] [DecidableEq D] in
lemma prev_top (x : H.Base) : H.top (H.prev x.val) = H.top x.val := by
  by_cases ht : H.top x.val = true
  · simp only [prev,ht,ite_true,H.top_prev]
    apply H.top_of_role
    rw [H.edge2 _ (H.role_prev0 ht x.property)]; decide
  · have hf : H.top x.val = false := Bool.eq_false_iff.mpr ht
    simp only [prev,hf,Bool.false_eq_true,ite_false,H.top_prev]

omit [Fintype D] [DecidableEq D] in
lemma prev_next (x : H.Base) : H.prev (H.next x.val) = x.val := by
  unfold prev
  rw [H.next_top]
  by_cases ht : H.top x.val = true
  · simp only [ht,ite_true,next,symm_apply_apply,M.edge_edge]
  · have hf : H.top x.val = false := Bool.eq_false_iff.mpr ht
    simp only [hf,Bool.false_eq_true,ite_false,next,symm_apply_apply]

omit [Fintype D] [DecidableEq D] in
lemma next_prev (x : H.Base) : H.next (H.prev x.val) = x.val := by
  unfold next
  rw [H.prev_top]
  by_cases ht : H.top x.val = true
  · simp only [ht,ite_true,prev,apply_symm_apply,M.edge_edge]
  · have hf : H.top x.val = false := Bool.eq_false_iff.mpr ht
    simp only [hf,Bool.false_eq_true,ite_false,prev,apply_symm_apply]

/-- Each macro face walks through consecutive radial triangles around one
actual apex. Frozen face cycles are unchanged. -/
def face : Perm H.Base where
  toFun x := ⟨H.next x.val,H.next_role x⟩
  invFun x := ⟨H.prev x.val,H.prev_role x⟩
  left_inv x := Subtype.ext (H.prev_next x)
  right_inv x := Subtype.ext (H.next_prev x)

omit [Fintype D] [DecidableEq D] in
lemma edge_invariant (x : D) : H.role (M.edge x) = 0 ↔ H.role x = 0 :=
  ⟨fun h => by simpa only [M.edge_edge] using H.edge0 (M.edge x) h,H.edge0 x⟩

def contraction : PictureMap H.Base where
  face := H.face
  edge := M.edge.subtypePerm H.edge_invariant
  edge_sq := by ext x; exact M.edge_edge x.val
  edge_ne := by intro x h; exact M.edge_ne x.val (congrArg Subtype.val h)

omit [Fintype D] [DecidableEq D] in
lemma free_invariant (x : H.Base) : H.free (H.contraction.face x) ↔ H.free x := by
  change H.top (H.next x.val) = true ↔ H.top x.val = true
  rw [H.next_top]

/-- Each elementary dart has its own retained old side, with the two radial
copies kept separately until the final contraction. -/
def expand : ConeExpansion.Point H.free → D
  | .inl x => x.val
  | .inr (.inl x) => M.face x.val.val
  | .inr (.inr x) => M.face (M.face x.val.val)

omit [Fintype D] [DecidableEq D] in
lemma expand_injective : Function.Injective H.expand := by
  rintro (a|(a|a)) (b|(b|b)) h
  · exact congrArg Sum.inl (Subtype.ext h)
  · have hh := congrArg H.role h
    change H.role a.val = H.role (M.face b.val.val) at hh
    rw [a.property,H.role_next0 b.property b.val.property] at hh
    contradiction
  · have hh := congrArg H.role h
    change H.role a.val = H.role (M.face (M.face b.val.val)) at hh
    rw [a.property,H.role_next1 (H.role_next0 b.property b.val.property)] at hh
    contradiction
  · have hh := congrArg H.role h
    change H.role (M.face a.val.val) = H.role b.val at hh
    rw [b.property,H.role_next0 a.property a.val.property] at hh
    contradiction
  · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext (Subtype.ext (M.face.injective h)))
  · have hh := congrArg H.role h
    change H.role (M.face a.val.val) = H.role (M.face (M.face b.val.val)) at hh
    rw [H.role_next0 a.property a.val.property,H.role_next1 (H.role_next0 b.property b.val.property)] at hh
    contradiction
  · have hh := congrArg H.role h
    change H.role (M.face (M.face a.val.val)) = H.role b.val at hh
    rw [b.property,H.role_next1 (H.role_next0 a.property a.val.property)] at hh
    contradiction
  · have hh := congrArg H.role h
    change H.role (M.face (M.face a.val.val)) = H.role (M.face b.val.val) at hh
    rw [H.role_next1 (H.role_next0 a.property a.val.property),H.role_next0 b.property b.val.property] at hh
    contradiction
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext (Subtype.ext (M.face.injective (M.face.injective h))))

omit [Fintype D] [DecidableEq D] in
lemma expand_surjective : Function.Surjective H.expand := by
  intro x
  rcases (show H.role x = 0 ∨ H.role x = 1 ∨ H.role x = 2 by omega) with hr|hr|hr
  · exact ⟨.inl ⟨x,hr⟩,rfl⟩
  · have ht := H.top_of_role (by rw [hr]; decide)
    refine ⟨.inr (.inl ⟨⟨M.face.symm x,H.role_prev1 hr⟩,?_⟩),?_⟩
    · exact (H.top_prev x).trans ht
    · exact M.face.apply_symm_apply x
  · have ht := H.top_of_role (by rw [hr]; decide)
    refine ⟨.inr (.inr ⟨⟨M.face x,H.role_next2 hr⟩,?_⟩),?_⟩
    · exact (H.top_face x).trans ht
    · exact H.period x ht

def expandEquiv : ConeExpansion.Point H.free ≃ D :=
  Equiv.ofBijective H.expand ⟨H.expand_injective,H.expand_surjective⟩

omit [Fintype D] [DecidableEq D] in
lemma expand_face (x : ConeExpansion.Point H.free) :
    H.expandEquiv ((ConeExpansion.map H.contraction H.free H.free_invariant).face x) =
      M.face (H.expandEquiv x) := by
  change H.expand ((ConeExpansion.map H.contraction H.free H.free_invariant).face x) = M.face (H.expand x)
  rcases x with a|(a|a)
  · by_cases ht : H.free a
    · simp only [ConeExpansion.map,ConeExpansion.face,Equiv.coe_fn_mk,dite_eq_left ht,
        expand]
    · have hh : H.top a.val = false := Bool.eq_false_iff.mpr ht
      simp only [ConeExpansion.map,ConeExpansion.face,Equiv.coe_fn_mk,dite_eq_right ht,
        expand,contraction,face,next,hh,Bool.false_eq_true,ite_false]
  · rfl
  · exact (H.period a.val.val a.property).symm

omit [Fintype D] [DecidableEq D] in
lemma expand_edge (x : ConeExpansion.Point H.free) :
    H.expandEquiv ((ConeExpansion.map H.contraction H.free H.free_invariant).edge x) =
      M.edge (H.expandEquiv x) := by
  rcases x with a|(a|a)
  · rfl
  · change M.face (M.face (H.next a.val.val)) = M.edge (M.face a.val.val)
    have hr := H.edge1 _ (H.role_next0 a.property a.val.property)
    have ht : H.top (M.edge (M.face a.val.val)) = true := H.top_of_role (by rw [hr]; decide)
    have ha : H.top a.val.val = true := a.property
    simp only [next,ha,ite_true]
    exact H.period _ ht
  · change M.face (H.prev a.val.val) = M.edge (M.face (M.face a.val.val))
    have ha : H.top a.val.val = true := a.property
    simp only [prev,ha,ite_true,apply_symm_apply,H.prev_eq ha]

/-- The contraction is a genuine genus-zero map with all old sides retained.
No surface classification, drawing, or asserted Euler correction is used. -/
theorem contraction_genusZero (h : M.GenusZero) : H.contraction.GenusZero := by
  apply ConeExpansion.genusZero_of_expansion
  exact (PictureMap.genusZero_equiv _ _ H.expandEquiv H.expand_face H.expand_edge).mpr h

end TriangleMarking
end PictureSwitch

/-! Local elementary triangle incidence induces the exact radial contraction. -/
namespace ConeSkeleton

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

abbrev ElementaryLiftSide := (elementaryLiftedBoundary n w d v hv hcell).Side

def elementaryTop (s : ElementaryLiftSide n w d v hv hcell) : Bool :=
  match s.1.2 with
  | .inl _ => true
  | .inr _ => false

def elementaryRole : ElementaryDart n w → Fin 3
  | (.inl _,_) => 0
  | (.inr _,false) => 1
  | (.inr _,true) => 2

def elementarySideRole (s : ElementaryLiftSide n w d v hv hcell) : Fin 3 :=
  elementaryRole n w ((elementaryLiftedBoundary n w d v hv hcell).sideLabel s).2

lemma elementaryTop_next (s : ElementaryLiftSide n w d v hv hcell) :
    elementaryTop n w d v hv hcell ((elementaryLiftedBoundary n w d v hv hcell).next s) =
      elementaryTop n w d v hv hcell s := rfl

lemma elementaryRole_frozen (s : ElementaryLiftSide n w d v hv hcell)
    (h : elementaryTop n w d v hv hcell s = false) :
    elementarySideRole n w d v hv hcell s = 0 := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases h
  · cases b <;> rfl

lemma elementaryRole_turn (s : ElementaryLiftSide n w d v hv hcell)
    (h : elementaryTop n w d v hv hcell s = true) :
    elementarySideRole n w d v hv hcell ((elementaryLiftedBoundary n w d v hv hcell).next s) =
      finRotate 3 (elementarySideRole n w d v hv hcell s) := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases b <;> fin_cases i <;> rfl
  · cases h

lemma elementaryTop_period (s : ElementaryLiftSide n w d v hv hcell)
    (h : elementaryTop n w d v hv hcell s = true) :
    (elementaryLiftedBoundary n w d v hv hcell).next
      ((elementaryLiftedBoundary n w d v hv hcell).next
        ((elementaryLiftedBoundary n w d v hv hcell).next s)) = s := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases b <;> fin_cases i <;> rfl
  · cases h

lemma elementaryRole_rev0 (e : ElementaryDart n w) (h : elementaryRole n w e = 0) :
    elementaryRole n w (elementaryRev n w e) = 0 := by
  rcases e with ⟨e|e,b⟩
  · rfl
  · cases b <;> cases h
lemma elementaryRole_rev1 (e : ElementaryDart n w) (h : elementaryRole n w e = 1) :
    elementaryRole n w (elementaryRev n w e) = 2 := by
  rcases e with ⟨e|e,b⟩
  · cases h
  · cases b <;> first | rfl | cases h
lemma elementaryRole_rev2 (e : ElementaryDart n w) (h : elementaryRole n w e = 2) :
    elementaryRole n w (elementaryRev n w e) = 1 := by
  rcases e with ⟨e|e,b⟩
  · cases h
  · cases b <;> first | rfl | cases h

variable {A : Type*} [AddCommGroup A] (weight : G × ElementaryCell n w d → A)

/-- Raw cellular target: coefficients always identify actual lifted elementary
cells; the boolean used here only disables unrelated normalization machinery. -/
def elementaryRawTarget := (elementaryLiftedBoundary n w d v hv hcell).target
  weight (fun _ => false) (by intro l h; cases h)

variable (P : CellPicture (elementaryRawTarget n w d v hv hcell weight))

def elementaryMarking : TriangleMarking P.pairing where
  top x := elementaryTop n w d v hv hcell (P.index x)
  role x := elementarySideRole n w d v hv hcell (P.index x)
  top_face x := by rw [P.mapped.commute]; rfl
  frozen x h := elementaryRole_frozen n w d v hv hcell (P.index x) h
  turn x h := by rw [P.mapped.commute]; exact elementaryRole_turn n w d v hv hcell (P.index x) h
  period x h := by
    apply P.mapped.injective (SameCycle.rfl.apply_left.apply_left.apply_left)
    rw [P.mapped.commute,P.mapped.commute,P.mapped.commute]
    exact elementaryTop_period n w d v hv hcell (P.index x) h
  edge0 x h := by
    change elementaryRole n w (((elementaryLiftedBoundary n w d v hv hcell).sideLabel
      (P.index (P.pairing.edge x))).2) = 0
    have he := congrArg Prod.snd (P.respects.2 x)
    change ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index (P.pairing.edge x))).2 =
      elementaryRev n w ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index x)).2 at he
    rw [he]
    exact elementaryRole_rev0 n w _ h
  edge1 x h := by
    change elementaryRole n w (((elementaryLiftedBoundary n w d v hv hcell).sideLabel
      (P.index (P.pairing.edge x))).2) = 2
    have he := congrArg Prod.snd (P.respects.2 x)
    change ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index (P.pairing.edge x))).2 =
      elementaryRev n w ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index x)).2 at he
    rw [he]
    exact elementaryRole_rev1 n w _ h
  edge2 x h := by
    change elementaryRole n w (((elementaryLiftedBoundary n w d v hv hcell).sideLabel
      (P.index (P.pairing.edge x))).2) = 1
    have he := congrArg Prod.snd (P.respects.2 x)
    change ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index (P.pairing.edge x))).2 =
      elementaryRev n w ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index x)).2 at he
    rw [he]
    exact elementaryRole_rev2 n w _ h

lemma elementaryContraction_genusZero :
    (elementaryMarking n w d v hv hcell weight P).contraction.GenusZero :=
  TriangleMarking.contraction_genusZero _ P.genusZero

end

/-! Exact deck coordinates on the old and two radial sides of every triangle. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

def elementaryWalkIndex : ElementaryLiftSide n w d v hv hcell → G × WalkStep n w d
  | ⟨⟨g,.inl a⟩,b,_⟩ => (g,.inl (a.1,if b then macroCellDart a.2 else (macroCellDart a.2).symm))
  | ⟨⟨g,.inr a⟩,b,i⟩ => (g,.inr ⟨a,b,i⟩)

lemma elementaryTop_walk (s : ElementaryLiftSide n w d v hv hcell) :
    elementaryTop n w d v hv hcell s = walkFree n w d (walkKind n w d
      (elementaryWalkIndex n w d v hv hcell s).2) := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩ <;> rfl

lemma elementaryOld_injective : Function.Injective (elementaryOld n w) := by
  rintro ⟨e,b⟩ ⟨f,c⟩ h
  exact Prod.ext (Sum.inl.inj (congrArg (fun z : ElementaryDart n w => z.1) h))
    (congrArg (fun z : ElementaryDart n w => z.2) h)

lemma elementaryOffset_frozen (_ : G) (c : FrozenCell n w d)
    (i : Fin ((frozenBoundary n w d).size c)) :
    elementaryOffset n w d v (.inr c) i =
      (((List.ofFn ((frozenBoundary n w d).label c)).take i.val).map v).prod := by
  simp only [elementaryOffset,List.map_take,List.map_ofFn,Function.comp_def]
  rfl

lemma elementary_old_label (s : ElementaryLiftSide n w d v hv hcell)
    (h : elementarySideRole n w d v hv hcell s = 0) :
    (elementaryLiftedBoundary n w d v hv hcell).sideLabel s =
      ((elementaryWalkIndex n w d v hv hcell s).1 *
        coverOffset n w d v (elementaryWalkIndex n w d v hv hcell s).2,
        elementaryOld n w (walkLabel n w d (elementaryWalkIndex n w d v hv hcell s).2)) := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · have hi : i = (1 : Fin 3) := by
      cases b <;> fin_cases i <;> first | rfl | cases h
    subst i
    cases b with
    | false =>
      change (g * elementaryOffset n w d v (.inl c) (1 : Fin 3) *
        v (macroStep n w c.1 (macroCellDart c.2).adj),
        elementaryOld n w (rev n w (macroStep n w c.1 (macroCellDart c.2).adj))) =
        (g * macroPotential n w v c.1 (macroCellDart c.2).snd,
         elementaryOld n w (macroStep n w c.1 (macroCellDart c.2).symm.adj))
      apply Prod.ext
      · exact (congrArg (fun z => g * z * v (macroStep n w c.1 (macroCellDart c.2).adj))
          (elementaryOffset_triangle_one n w d v c.1 c.2)).trans
          ((mul_assoc _ _ _).trans (congrArg (g * ·)
            (macroPotential_edge n w d v hv hcell c.1 (macroCellDart c.2).adj)))
      · exact congrArg (elementaryOld n w)
          (macroStep_reverse n w c.1 (macroCellDart c.2).adj).symm
    | true =>
      change (g * elementaryOffset n w d v (.inl c) (1 : Fin 3),_) = (g * macroPotential n w v c.1 _,_)
      rw [elementaryOffset_triangle_one]
      rfl
  · change Fin ((frozenBoundary n w d).size c) at i
    cases b with
    | false =>
      change (g * elementaryOffset n w d v (.inr c) i * v ((frozenBoundary n w d).label c i),_) =
        (g * (_ * v ((frozenBoundary n w d).label c i)),_)
      rw [elementaryOffset_frozen n w d v g,mul_assoc]
      rfl
    | true =>
      change (g * elementaryOffset n w d v (.inr c) i,_) = (g * _,_)
      rw [elementaryOffset_frozen n w d v g]
      rfl

/-- Incoming radial dart after the old side, using the actual top basepoint. -/
lemma elementary_incoming (s : ElementaryLiftSide n w d v hv hcell)
    (h : elementarySideRole n w d v hv hcell s = 0)
    (g : G) (a : Top n w) (e : MacroGraph.graph.Dart)
    (he : elementaryWalkIndex n w d v hv hcell s = (g,.inl (a,e))) :
    (elementaryLiftedBoundary n w d v hv hcell).sideLabel
      ((elementaryLiftedBoundary n w d v hv hcell).next s) =
      (g * macroPotential n w v a e.snd, (.inr (a,e.snd),false)) := by
  rcases s with ⟨⟨k,c|c⟩,b,i⟩
  · have hi : i = (1 : Fin 3) := by
      cases b <;> fin_cases i <;> first | rfl | cases h
    subst i
    cases b with
    | false =>
      simp only [elementaryWalkIndex,Bool.false_eq_true,ite_false] at he
      cases he
      change (g * elementaryOffset n w d v (.inl c) (0 : Fin 3) * macroPotential n w v c.1 _,_) = _
      rw [elementaryOffset_triangle_zero,mul_one]
      rfl
    | true =>
      simp only [elementaryWalkIndex,ite_true] at he
      cases he
      change (g * elementaryOffset n w d v (.inl c) (2 : Fin 3),_) = _
      rw [elementaryOffset_triangle_two n w d v hv hcell]
      rfl
  · cases he

/-- Outgoing radial dart before the old side; its deck coordinate is EXACTLY
that of the independent lifted elementary-cell coordinate. -/
lemma elementary_outgoing (s : ElementaryLiftSide n w d v hv hcell)
    (h : elementarySideRole n w d v hv hcell s = 0)
    (g : G) (a : Top n w) (e : MacroGraph.graph.Dart)
    (he : elementaryWalkIndex n w d v hv hcell s = (g,.inl (a,e))) :
    (elementaryLiftedBoundary n w d v hv hcell).sideLabel
      ((elementaryLiftedBoundary n w d v hv hcell).next
        ((elementaryLiftedBoundary n w d v hv hcell).next s)) =
      (g, (.inr (a,e.fst),true)) := by
  rcases s with ⟨⟨k,c|c⟩,b,i⟩
  · have hi : i = (1 : Fin 3) := by
      cases b <;> fin_cases i <;> first | rfl | cases h
    subst i
    cases b with
    | false =>
      simp only [elementaryWalkIndex,Bool.false_eq_true,ite_false] at he
      cases he
      change (g * elementaryOffset n w d v (.inl c) (2 : Fin 3) * (macroPotential n w v c.1 _)⁻¹,_) = _
      rw [elementaryOffset_triangle_two n w d v hv hcell,mul_inv_cancel_right]
      rfl
    | true =>
      simp only [elementaryWalkIndex,ite_true] at he
      cases he
      change (g * elementaryOffset n w d v (.inl c) (0 : Fin 3),_) = _
      rw [elementaryOffset_triangle_zero,mul_one]
      rfl
  · cases he

end

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

lemma elementaryWalkIndex_frozen_injective
    {s t : ElementaryLiftSide n w d v hv hcell}
    (hs : elementaryTop n w d v hv hcell s = false)
    (h : elementaryWalkIndex n w d v hv hcell s = elementaryWalkIndex n w d v hv hcell t) : s = t := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases hs
  · rcases t with ⟨⟨k,a|a⟩,z,j⟩
    · cases h
    · change (g,Sum.inr (⟨c,b,i⟩ : (frozenBoundary n w d).Side)) =
        (k,Sum.inr (⟨a,z,j⟩ : (frozenBoundary n w d).Side)) at h
      obtain ⟨rfl,h⟩ := Prod.mk.inj h
      have h := Sum.inr.inj h
      cases h
      rfl

variable {A : Type*} [AddCommGroup A]
  (tc : G → Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ g a e, tc g a e.symm = -tc g a e) (fc : G → FrozenCell n w d → A)

lemma elementary_frozen_next (s : ElementaryLiftSide n w d v hv hcell)
    (hs : elementaryTop n w d v hv hcell s = false) :
    elementaryWalkIndex n w d v hv hcell ((elementaryLiftedBoundary n w d v hv hcell).next s) =
      (liftedFrozenTarget n w d v hv hcell tc hc fc).next (elementaryWalkIndex n w d v hv hcell s) := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases hs
  · rfl

lemma elementary_frozen_kind (s : ElementaryLiftSide n w d v hv hcell)
    (hs : elementaryTop n w d v hv hcell s = false) :
    (liftedWalkTarget n w d v hv hcell tc hc fc).kind
      (elementaryWalkIndex n w d v hv hcell ((elementaryLiftedBoundary n w d v hv hcell).next s)) =
      (liftedWalkTarget n w d v hv hcell tc hc fc).kind (elementaryWalkIndex n w d v hv hcell s) := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases hs
  · rfl

lemma elementary_frozen_closed (s : ElementaryLiftSide n w d v hv hcell)
    (hs : elementaryTop n w d v hv hcell s = false) :
    (liftedWalkTarget n w d v hv hcell tc hc fc).front
      (elementaryWalkIndex n w d v hv hcell ((elementaryLiftedBoundary n w d v hv hcell).next s)) =
      (liftedWalkTarget n w d v hv hcell tc hc fc).back (elementaryWalkIndex n w d v hv hcell s) := by
  let B := elementaryLiftedBoundary n w d v hv hcell
  have hh := B.next_start s
  rw [elementary_old_label n w d v hv hcell (B.next s)
    (elementaryRole_frozen n w d v hv hcell _ ((elementaryTop_next n w d v hv hcell s).trans hs)),
    elementary_old_label n w d v hv hcell s (elementaryRole_frozen n w d v hv hcell s hs)] at hh
  have hp := congrArg Prod.fst hh
  have hq := congrArg Prod.snd hh
  change _ = _ * elementaryVoltage n w v (elementaryOld n w
     (walkLabel n w d (elementaryWalkIndex n w d v hv hcell s).2)) at hp
  change _ = _ * v (walkLabel n w d (elementaryWalkIndex n w d v hv hcell s).2) at hp
  rw [mul_assoc, ← coverOffset_opposite n w d v hv hcell] at hp
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases hs
  · apply Prod.ext
    · exact hp
    · exact congrArg Sum.inr (Sum.inl.inj hq)

end

/-! Every genuine elementary genus-zero picture contracts to the unchanged
macro/frozen target, preserving the literal original-group deck coordinates. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)
variable {A : Type*} [AddCommGroup A] (weight : G × ElementaryCell n w d → A)
  (P : CellPicture (elementaryRawTarget n w d v hv hcell weight))

abbrev ElementaryBases := (elementaryMarking n w d v hv hcell weight P).Base

def elementaryContractIndex (x : ElementaryBases n w d v hv hcell weight P) : G × WalkStep n w d :=
  elementaryWalkIndex n w d v hv hcell (P.index x.val)

lemma elementaryContract_top_next (x : ElementaryBases n w d v hv hcell weight P)
    (ht : (elementaryMarking n w d v hv hcell weight P).free x) :
    ∃ (g : G) (a : Top n w) (e f : MacroGraph.graph.Dart),
      elementaryContractIndex n w d v hv hcell weight P x = (g,.inl (a,e)) ∧
      elementaryContractIndex n w d v hv hcell weight P
        ((elementaryMarking n w d v hv hcell weight P).contraction.face x) = (g,.inl (a,f)) ∧
      f.fst = e.snd := by
  let H := elementaryMarking n w d v hv hcell weight P
  let y := H.contraction.face x
  have hyt : H.free y := (H.free_invariant x).mpr ht
  rcases hx : elementaryContractIndex n w d v hv hcell weight P x with ⟨g,s|s⟩
  · rcases s with ⟨a,e⟩
    rcases hy : elementaryContractIndex n w d v hv hcell weight P y with ⟨k,t|t⟩
    · rcases t with ⟨b,f⟩
      have hf2 : P.pairing.face (P.pairing.face y.val) = P.pairing.edge (P.pairing.face x.val) :=
        H.expand_edge (.inr (.inl ⟨x,ht⟩))
      have hp := P.respects.2 (P.pairing.face x.val)
      change (elementaryLiftedBoundary n w d v hv hcell).sideLabel
        (P.index (P.pairing.edge (P.pairing.face x.val))) =
        (elementaryLiftedBoundary n w d v hv hcell).rev
          ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index (P.pairing.face x.val))) at hp
      rw [← hf2,P.mapped.commute,P.mapped.commute,P.mapped.commute] at hp
      change (elementaryLiftedBoundary n w d v hv hcell).sideLabel
        ((elementaryLiftedBoundary n w d v hv hcell).next
          ((elementaryLiftedBoundary n w d v hv hcell).next (P.index y.val))) =
        (elementaryLiftedBoundary n w d v hv hcell).rev
          ((elementaryLiftedBoundary n w d v hv hcell).sideLabel
            ((elementaryLiftedBoundary n w d v hv hcell).next (P.index x.val))) at hp
      rw [elementary_outgoing n w d v hv hcell (P.index y.val) y.property k b f hy,
        elementary_incoming n w d v hv hcell (P.index x.val) x.property g a e hx] at hp
      change (k,Sum.inr (b,f.fst),true) =
        (g * macroPotential n w v a e.snd * (macroPotential n w v a e.snd)⁻¹,Sum.inr (a,e.snd),true) at hp
      rw [mul_inv_cancel_right] at hp
      have hg : k = g := congrArg Prod.fst hp
      have hab : (b,f.fst) = (a,e.snd) := Sum.inr.inj (congrArg (fun z => z.2.1) hp)
      have ha : b = a := congrArg Prod.fst hab
      have hef : f.fst = e.snd := congrArg Prod.snd hab
      subst k; subst b
      exact ⟨g,a,e,f,rfl,rfl,hef⟩
    · have hh : elementaryTop n w d v hv hcell (P.index y.val) = true := hyt
      rw [elementaryTop_walk] at hh
      change walkFree n w d (walkKind n w d (elementaryContractIndex n w d v hv hcell weight P y).2) = true at hh
      rw [hy] at hh
      cases hh
  · have hh : elementaryTop n w d v hv hcell (P.index x.val) = true := ht
    rw [elementaryTop_walk] at hh
    change walkFree n w d (walkKind n w d (elementaryContractIndex n w d v hv hcell weight P x).2) = true at hh
    rw [hx] at hh
    cases hh

lemma elementaryContract_frozen_next (x : ElementaryBases n w d v hv hcell weight P)
    (ht : ¬ (elementaryMarking n w d v hv hcell weight P).free x) :
    ((elementaryMarking n w d v hv hcell weight P).contraction.face x).val = P.pairing.face x.val := by
  have ht' : (elementaryMarking n w d v hv hcell weight P).top x.val = false := Bool.eq_false_iff.mpr ht
  change TriangleMarking.next _ _ = _
  simp only [TriangleMarking.next,ht',Bool.false_eq_true,ite_false]

variable (tc : G → Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ g a e, tc g a e.symm = -tc g a e) (fc : G → FrozenCell n w d → A)

lemma elementaryContract_incidence (x : ElementaryBases n w d v hv hcell weight P) :
    (liftedWalkTarget n w d v hv hcell tc hc fc).kind
      (elementaryContractIndex n w d v hv hcell weight P
        ((elementaryMarking n w d v hv hcell weight P).contraction.face x)) =
      (liftedWalkTarget n w d v hv hcell tc hc fc).kind (elementaryContractIndex n w d v hv hcell weight P x) ∧
    (liftedWalkTarget n w d v hv hcell tc hc fc).front
      (elementaryContractIndex n w d v hv hcell weight P
        ((elementaryMarking n w d v hv hcell weight P).contraction.face x)) =
      (liftedWalkTarget n w d v hv hcell tc hc fc).back (elementaryContractIndex n w d v hv hcell weight P x) := by
  by_cases ht : (elementaryMarking n w d v hv hcell weight P).free x
  · obtain ⟨g,a,e,f,hx,hy,hf⟩ := elementaryContract_top_next n w d v hv hcell weight P x ht
    rw [hy,hx]
    constructor
    · rfl
    · change (g * macroPotential n w v a f.fst,Sum.inl (a,f.fst)) =
        (g * macroPotential n w v a e.snd,Sum.inl (a,e.snd))
      rw [hf]
  · have ht' : elementaryTop n w d v hv hcell (P.index x.val) = false := Bool.eq_false_iff.mpr ht
    have hf := elementaryContract_frozen_next n w d v hv hcell weight P x ht
    unfold elementaryContractIndex
    rw [hf,P.mapped.commute]
    exact ⟨elementary_frozen_kind n w d v hv hcell tc hc fc _ ht',
      elementary_frozen_closed n w d v hv hcell tc hc fc _ ht'⟩

lemma elementaryContract_paired (x : ElementaryBases n w d v hv hcell weight P) :
    (liftedWalkTarget n w d v hv hcell tc hc fc).label
      (elementaryContractIndex n w d v hv hcell weight P
        ((elementaryMarking n w d v hv hcell weight P).contraction.edge x)) =
      (liftedWalkTarget n w d v hv hcell tc hc fc).rev
        ((liftedWalkTarget n w d v hv hcell tc hc fc).label (elementaryContractIndex n w d v hv hcell weight P x)) := by
  let H := elementaryMarking n w d v hv hcell weight P
  have hp := P.respects.2 x.val
  change (elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index (P.pairing.edge x.val)) =
    (elementaryLiftedBoundary n w d v hv hcell).rev
    ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index x.val)) at hp
  rw [elementary_old_label n w d v hv hcell _ (H.edge0 _ x.property),
    elementary_old_label n w d v hv hcell _ x.property] at hp
  change ((elementaryWalkIndex n w d v hv hcell (P.index (P.pairing.edge x.val))).1 *
      coverOffset n w d v (elementaryWalkIndex n w d v hv hcell (P.index (P.pairing.edge x.val))).2,
      walkLabel n w d (elementaryWalkIndex n w d v hv hcell (P.index (P.pairing.edge x.val))).2) =
    ((elementaryWalkIndex n w d v hv hcell (P.index x.val)).1 *
      coverOffset n w d v (elementaryWalkIndex n w d v hv hcell (P.index x.val)).2 *
      v (walkLabel n w d (elementaryWalkIndex n w d v hv hcell (P.index x.val)).2),
      rev n w (walkLabel n w d (elementaryWalkIndex n w d v hv hcell (P.index x.val)).2))
  apply Prod.ext
  · exact congrArg (fun z : G × ElementaryDart n w => z.1) hp
  · exact elementaryOld_injective n w (congrArg (fun z : G × ElementaryDart n w => z.2) hp)

/-- A constructed macro picture, not an extra producer hypothesis. Exact
coordinate equality and frozen indexing are proved separately below. -/
def elementaryMacroPicture : WalkPicture (liftedWalkTarget n w d v hv hcell tc hc fc) where
  Dart := ElementaryBases n w d v hv hcell weight P
  pairing := (elementaryMarking n w d v hv hcell weight P).contraction
  index := elementaryContractIndex n w d v hv hcell weight P
  closed x := (elementaryContract_incidence n w d v hv hcell weight P tc hc fc x).2
  kind x := (elementaryContract_incidence n w d v hv hcell weight P tc hc fc x).1
  paired := elementaryContract_paired n w d v hv hcell weight P tc hc fc
  genusZero := elementaryContraction_genusZero n w d v hv hcell weight P

end

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)
variable {A : Type*} [AddCommGroup A] (weight : G × ElementaryCell n w d → A)
  (P : CellPicture (elementaryRawTarget n w d v hv hcell weight))
  (tc : G → Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ g a e, tc g a e.symm = -tc g a e) (fc : G → FrozenCell n w d → A)

lemma elementaryMacro_frozenMapped :
    (elementaryMacroPicture n w d v hv hcell weight P tc hc fc).FrozenMapped
      (liftedFrozenTarget n w d v hv hcell tc hc fc) := by
  let Q := elementaryMacroPicture n w d v hv hcell weight P tc hc fc
  have ht (x : Q.FrozenDart) : elementaryTop n w d v hv hcell (P.index x.val.val) = false := by
    rw [elementaryTop_walk]
    exact x.property
  have hf (x : Q.FrozenDart) : (Q.frozenFace x).val.val = P.pairing.face x.val.val := by
    exact elementaryContract_frozen_next n w d v hv hcell weight P x.val
      (by change ¬ elementaryTop n w d v hv hcell (P.index x.val.val) = true; rw [ht x]; decide)
  constructor
  · intro x
    change elementaryWalkIndex n w d v hv hcell (P.index (Q.frozenFace x).val.val) = _
    rw [hf,P.mapped.commute]
    exact elementary_frozen_next n w d v hv hcell tc hc fc _ (ht x)
  · intro x y hxy he
    apply Subtype.ext
    apply Subtype.ext
    apply P.mapped.injective (semiconj_perm_sameCycle hf hxy)
    exact elementaryWalkIndex_frozen_injective n w d v hv hcell (ht x) he

end

/-! The radial contraction preserves every independent lifted elementary-cell
coefficient, not just an augmentation or a projection to the old edges. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)
variable {A : Type*} [AddCommGroup A]
  (tc : G → Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ g a e, tc g a e.symm = -tc g a e) (fc : G → FrozenCell n w d → A)

def elementaryMacroWeight : G × ElementaryCell n w d → A
  | (g,.inl a) => tc g a.1 (macroCellDart a.2)
  | (g,.inr a) => fc g a

def elementaryMarkPosition : (c : ElementaryCell n w d) → Fin (elementarySize n w d c)
  | .inl _ => (1 : Fin 3)
  | .inr a => ⟨0,(frozenBoundary n w d).positive a⟩

lemma elementary_selected_weight (s : ElementaryLiftSide n w d v hv hcell) :
    (if elementarySideRole n w d v hv hcell s = 0 then
      (liftedWalkTarget n w d v hv hcell tc hc fc).weight (elementaryWalkIndex n w d v hv hcell s) else 0) =
    (@ite A (s.2.2 = elementaryMarkPosition n w d s.1.2)
      (instDecidableEqFin _ s.2.2 (elementaryMarkPosition n w d s.1.2))
      ((elementaryLiftedBoundary n w d v hv hcell).weight (elementaryMacroWeight n w d tc fc) s) 0) := by
  rcases s with ⟨⟨g,a|a⟩,b,i⟩
  · change Fin 3 at i
    cases b <;> fin_cases i
    · exact (ite_eq_right (by decide : (1 : Fin 3) ≠ 0)).trans
        (ite_eq_right (by decide : (0 : Fin 3) ≠ 1)).symm
    · exact (ite_eq_left rfl).trans ((hc g a.1 (macroCellDart a.2)).trans (ite_eq_left rfl).symm)
    · exact (ite_eq_right (by decide : (2 : Fin 3) ≠ 0)).trans
        (ite_eq_right (by decide : (2 : Fin 3) ≠ 1)).symm
    · exact (ite_eq_right (by decide : (2 : Fin 3) ≠ 0)).trans
        (ite_eq_right (by decide : (0 : Fin 3) ≠ 1)).symm
    · exact (ite_eq_left rfl).trans (ite_eq_left rfl).symm
    · exact (ite_eq_right (by decide : (1 : Fin 3) ≠ 0)).trans
        (ite_eq_right (by decide : (2 : Fin 3) ≠ 1)).symm
  · change Fin ((frozenBoundary n w d).size a) at i
    have hrole : elementarySideRole n w d v hv hcell (⟨(g,.inr a),b,i⟩) = 0 :=
      elementaryRole_frozen n w d v hv hcell _ rfl
    rw [hrole,ite_eq_left rfl]
    change (if i.val = 0 then (frozenBoundary n w d).weight (fc g) ⟨a,b,i⟩ else 0) = _
    have he : (i.val = 0) = (i = (⟨0,(frozenBoundary n w d).positive a⟩ : Fin _)) :=
      propext ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    exact ite_congr (c := i = (⟨0,(frozenBoundary n w d).positive a⟩ : Fin _))
      he (fun _ => by cases b <;> rfl) (fun _ => rfl)

variable (P : CellPicture (elementaryRawTarget n w d v hv hcell (elementaryMacroWeight n w d tc fc)))

lemma elementaryMacro_chain :
    (elementaryMacroPicture n w d v hv hcell (elementaryMacroWeight n w d tc fc) P tc hc fc).chain = P.chain := by
  let B := elementaryLiftedBoundary n w d v hv hcell
  let weight := elementaryMacroWeight n w d tc fc
  have hh := faceChain_eq_ite P.pairing.face
    ((elementaryRawTarget n w d v hv hcell weight).weight ∘ P.index)
    (fun x => by change B.weight weight (P.index (P.pairing.face x)) = _
                 rw [P.mapped.commute]; rfl)
    (fun x => (P.index x).2.2 = elementaryMarkPosition n w d (P.index x).1.2)
    (P.mapped.selected _ _ _ _ (B.marked_unique (fun a => elementaryMarkPosition n w d a.2)))
  change _ = faceChain _ _ _
  rw [hh]
  change (∑ x : {a : P.Dart // elementarySideRole n w d v hv hcell (P.index a) = 0},
    (liftedWalkTarget n w d v hv hcell tc hc fc).weight
      (elementaryWalkIndex n w d v hv hcell (P.index x.val))) = _
  erw [HyperbolicObstruction.sum_subtype_eq_ite
    (fun a : P.Dart => elementarySideRole n w d v hv hcell (P.index a) = 0)
    (fun a : P.Dart => (liftedWalkTarget n w d v hv hcell tc hc fc).weight
      (elementaryWalkIndex n w d v hv hcell (P.index a)))]
  apply Finset.sum_congr rfl
  intro x _
  simpa only [Function.comp_apply, elementaryRawTarget, PolygonTarget.Boundary.target]
    using elementary_selected_weight n w d v hv hcell tc hc fc (P.index x)

end

/-! Every genus-zero picture over the literal elementary lifted-cell boundary
has zero FULL cellular chain, by exact radial contraction. -/
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u v z
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type v} [Group G] {A : Type z} [AddCommGroup A]
  (weight : G × ElementaryCell n w d → A)

def elementaryTopWeight (g : G) (a : Top n w) (e : MacroGraph.graph.Dart) : A :=
  macroOrientation e • weight (g, .inl (a, macroCell e))
omit [_root_.Group G] in
lemma elementaryTopWeight_symm (g : G) (a : Top n w) (e : MacroGraph.graph.Dart) :
    elementaryTopWeight n w d weight g a e.symm = - elementaryTopWeight n w d weight g a e := by
  simp only [elementaryTopWeight,macroCell_symm,macroOrientation_symm,neg_zsmul]

omit [_root_.Group G] in
lemma elementaryMacroWeight_eq :
    elementaryMacroWeight n w d (elementaryTopWeight n w d weight)
      (fun g a => weight (g,.inr a)) = weight := by
  funext x
  rcases x with ⟨g,⟨a,e⟩|a⟩
  · simp only [elementaryMacroWeight,elementaryTopWeight,macroCellDart_cell,
      macroCellDart_orientation,one_zsmul]
  · rfl

/-- The cutoff precedes all realizations and independent lift coefficients. -/
theorem uniform_elementary_sphere_chain_zero {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ (G : Type v) [Group G] (A : Type z) [AddCommGroup A]
        (voltage : Dart n w → G) (hv : ∀ e, voltage (rev n w e) = (voltage e)⁻¹)
        (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => voltage (side n w d a i))).prod = 1)
        (weight : G × ElementaryCell n w d → A)
        (P : CellPicture.{u} (elementaryRawTarget n w d voltage hv hcell weight)),
        P.chain = 0 := by
  obtain ⟨M,hM,hh⟩ := uniform_actual_lifted_chain_zero.{u,v,z} ha hb hd
  refine ⟨M,hM,?_⟩
  intro n w d hgood G _ A _ voltage hv hcell weight
  rw [← elementaryMacroWeight_eq n w d weight]
  intro P
  rw [← elementaryMacro_chain n w d voltage hv hcell
    (elementaryTopWeight n w d weight) (elementaryTopWeight_symm n w d weight)
    (fun g a => weight (g,.inr a)) P]
  exact hh n w d hgood G A voltage hv hcell _ _ _ _
    (elementaryMacro_frozenMapped n w d voltage hv hcell _ P _ _ _)

end ConeSkeleton

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/
namespace VoltageWords

section
open HyperbolicObstruction.WordPictures
variable {A G : Type*} [Group G]

@[simp] lemma invRev_singleton (e : A × Bool) : FreeGroup.invRev [e] = [invLetter e] := rfl

def voltage (v : A → G) (e : A × Bool) : G := if e.2 then v e.1 else (v e.1)⁻¹

def total (v : A → G) (w : Word A) : G := (w.map (voltage v)).prod

@[simp] lemma voltage_inv (v : A → G) (e : A × Bool) :
    voltage v (invLetter e) = (voltage v e)⁻¹ := by
  rcases e with ⟨a,b⟩; cases b <;> simp [voltage,invLetter]

@[simp] lemma total_nil (v : A → G) : total v [] = 1 := rfl
@[simp] lemma total_cons (v : A → G) (e : A × Bool) (w : Word A) :
    total v (e::w) = voltage v e * total v w := rfl
@[simp] lemma total_append (v : A → G) (w z : Word A) :
    total v (w++z) = total v w * total v z := by simp [total]

@[simp] lemma total_inv (v : A → G) (w : Word A) :
    total v (FreeGroup.invRev w) = (total v w)⁻¹ := by
  induction w with
  | nil => simp
  | cons e w ih =>
    rw [FreeGroup.invRev_cons,total_append,ih]
    change (total v w)⁻¹ * (voltage v (invLetter e) * 1) = _
    simp only [voltage_inv,mul_one,total_cons,mul_inv_rev]

def liftLetter (v : A → G) (g : G) (e : A × Bool) : (G × A) × Bool :=
  if e.2 then ((g,e.1),true) else ((g * voltage v e,e.1),false)

@[simp] lemma liftLetter_inv (v : A → G) (g : G) (e : A × Bool) :
    liftLetter v (g * voltage v e) (invLetter e) = invLetter (liftLetter v g e) := by
  rcases e with ⟨a,b⟩; cases b <;> simp [liftLetter,voltage,invLetter]

def liftWord (v : A → G) (g : G) : Word A → Word (G × A)
  | [] => []
  | e::w => liftLetter v g e :: liftWord v (g * voltage v e) w

@[simp] lemma liftWord_nil (v : A → G) (g : G) : liftWord v g [] = [] := rfl
@[simp] lemma liftWord_cons (v : A → G) (g : G) (e : A × Bool) (w : Word A) :
    liftWord v g (e::w) = liftLetter v g e :: liftWord v (g * voltage v e) w := rfl

lemma liftWord_append (v : A → G) (g : G) (w z : Word A) :
    liftWord v g (w++z) = liftWord v g w ++ liftWord v (g * total v w) z := by
  induction w generalizing g with
  | nil => simp
  | cons e w ih => simp only [List.cons_append,liftWord_cons,ih,total_cons,mul_assoc]

lemma liftWord_inv (v : A → G) (g : G) (w : Word A) :
    liftWord v (g * total v w) (FreeGroup.invRev w) = FreeGroup.invRev (liftWord v g w) := by
  induction w generalizing g with
  | nil => simp
  | cons e w ih =>
    rw [FreeGroup.invRev_cons,liftWord_append,total_cons,← mul_assoc,ih]
    rw [total_inv]
    conv_rhs => rw [liftWord_cons,FreeGroup.invRev_cons]
    simp only [invRev_singleton,liftWord_cons,liftWord_nil]
    change _ ++ [liftLetter v (((g * voltage v e) * total v w) * (total v w)⁻¹) (invLetter e)] =
      _ ++ [invLetter (liftLetter v g e)]
    rw [mul_inv_cancel_right,liftLetter_inv]

lemma total_step (v : A → G) {w z : Word A} (h : FreeGroup.Red.Step w z) :
    total v w = total v z := by
  cases h with
  | @not l r a b =>
    cases b <;> simp [total_append,total_cons,voltage]

lemma liftWord_step (v : A → G) (g : G) {w z : Word A} (h : FreeGroup.Red.Step w z) :
    FreeGroup.Red.Step (liftWord v g w) (liftWord v g z) := by
  cases h with
  | @not l r a b =>
    simp only [liftWord_append,liftWord_cons]
    have he : (a,!b) = invLetter (a,b) := rfl
    rw [he,voltage_inv,liftLetter_inv,mul_inv_cancel_right]
    exact FreeGroup.Red.Step.not

/-- Relators of the actual voltage-cover edge presentation, not a quotient of
base-cell coefficients. Every deck coordinate remains an independent index. -/
def Relators (v : A → G) (R : Set (Word A)) : Set (Word (G × A)) :=
  {z | ∃ g w, w ∈ R ∧ z = liftWord v g w}

lemma move_total (v : A → G) {R : Set (Word A)}
    (hR : ∀ w ∈ R, total v w = 1) {w z : Word A} {n : ℕ} (h : Move R w z n) :
    total v w = total v z := by
  cases h with
  | free h => exact total_step v h
  | face l r w hw => simp only [total_append,hR w hw,mul_one]
  | reverseFace l r w hw => simp only [total_append,total_inv,hR w hw,inv_one,mul_one]

lemma homotopy_total (v : A → G) {R : Set (Word A)}
    (hR : ∀ w ∈ R, total v w = 1) {w z : Word A} {n : ℕ} (h : Homotopy R w z n) :
    total v w = total v z := by
  induction h with
  | refl => rfl
  | move h => exact move_total v hR h
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'

lemma move_lift (v : A → G) {R : Set (Word A)}
    (hR : ∀ w ∈ R, total v w = 1) {w z : Word A} {n : ℕ} (h : Move R w z n) (g : G) :
    Move (Relators v R) (liftWord v g w) (liftWord v g z) n := by
  cases h with
  | free h => exact Move.free (liftWord_step v g h)
  | face l r w hw =>
    simp only [liftWord_append,total_append,hR w hw,mul_one]
    exact Move.face _ _ _ ⟨g * total v l,w,hw,rfl⟩
  | reverseFace l r w hw =>
    have hi : liftWord v (g * total v l) (FreeGroup.invRev w) =
        FreeGroup.invRev (liftWord v (g * total v l) w) := by
      simpa only [hR w hw,mul_one] using liftWord_inv v (g * total v l) w
    simp only [liftWord_append,total_append,total_inv,hR w hw,inv_one,mul_one,hi]
    exact Move.reverseFace _ _ _ ⟨g * total v l,w,hw,rfl⟩

/-- An actual area-preserving homotopy lift. Closed relators, free cancellation
and both orientations are derived, not assumed as a cover's simple connectivity. -/
theorem homotopy_lift (v : A → G) {R : Set (Word A)}
    (hR : ∀ w ∈ R, total v w = 1) {w z : Word A} {n : ℕ} (h : Homotopy R w z n) (g : G) :
    Homotopy (Relators v R) (liftWord v g w) (liftWord v g z) n := by
  induction h with
  | refl => exact WordPictures.Homotopy.refl _
  | move h => exact WordPictures.Homotopy.move (move_lift v hR h g)
  | symm h ih => exact WordPictures.Homotopy.symm ih
  | trans h h' ih ih' => exact WordPictures.Homotopy.trans ih ih'

end

open HyperbolicObstruction.WordPictures HyperbolicObstruction.PictureSwitch
variable {A G V C : Type*} [Group G]

lemma liftWord_ofFn (v : A → G) (g : G) (w : Word A) :
    liftWord v g w = List.ofFn (fun i : Fin w.length =>
      liftLetter v (g * total v (w.take i.val)) w[i.val]) := by
  induction w generalizing g with
  | nil => rfl
  | cons e w ih =>
    rw [liftWord_cons,ih,List.ofFn_succ]
    congr 1
    · simp only [Fin.val_zero,List.take_zero,total_nil,mul_one,List.getElem_cons_zero]
    · apply congrArg List.ofFn
      funext i
      simp only [Fin.val_succ,List.take_succ_cons,total_cons,List.getElem_cons_succ,mul_assoc]

lemma liftWord_ofFn' (v : A → G) (g : G) {m : ℕ} (w : Fin m → A × Bool) :
    liftWord v g (List.ofFn w) = List.ofFn (fun i : Fin m =>
      liftLetter v (g * ((List.ofFn (voltage v ∘ w)).take i.val).prod) (w i)) := by
  rw [liftWord_ofFn]
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn,total,List.map_take,List.map_ofFn]

/-- Encoding the shifted reversal of a voltage cover as a true signed edge.
The negative generator is based at the initial point of its positive reverse. -/
def encode (v : A → G) : G × (A × Bool) ≃ (G × A) × Bool where
  toFun e := liftLetter v e.1 e.2
  invFun e := (if e.2 then e.1.1 else e.1.1 * v e.1.2, (e.1.2,e.2))
  left_inv := by rintro ⟨g,a,b⟩; cases b <;> simp [liftLetter,voltage]
  right_inv := by rintro ⟨⟨g,a⟩,b⟩; cases b <;> simp [liftLetter,voltage]

lemma encode_reverse (v : A → G) (g : G) (e : A × Bool) :
    encode v (g * voltage v e, invLetter e) = invLetter (encode v (g,e)) :=
  liftLetter_inv v g e

def liftedStart (B : PolygonTarget.Boundary C (A × Bool) V) (v : A → G)
    (e : (G × A) × Bool) : G × V :=
  ((encode v).symm e |>.1, B.start ((encode v).symm e |>.2))

lemma liftedStart_encode (B : PolygonTarget.Boundary C (A × Bool) V) (v : A → G)
    (g : G) (e : A × Bool) : liftedStart B v (encode v (g,e)) = (g,B.start e) := by
  simp only [liftedStart,Equiv.symm_apply_apply]

variable (B : PolygonTarget.Boundary C (A × Bool) V) (v : A → G)
  (hinv : B.rev = invLetter)
  (hc : ∀ c, total v (B.attachingWord c) = 1)

/-- All individual lifted polygons, expressed in genuine signed lift edges. -/
def liftedBoundary : PolygonTarget.Boundary (G × C) ((G × A) × Bool) (G × V) where
  size c := B.size c.2
  positive c := B.positive c.2
  label c i := encode v (c.1 * ((List.ofFn (voltage v ∘ B.label c.2)).take i.val).prod,
    B.label c.2 i)
  start := liftedStart B v
  rev := invLetter
  inv := invLetter_invLetter
  closed c i := by
    rw [← encode_reverse,liftedStart_encode,liftedStart_encode]
    apply Prod.ext
    · rw [ConeSkeleton.group_prefix_rotate _ (by
        simpa only [total,PolygonTarget.Boundary.attachingWord,List.map_ofFn] using hc c.2) i]
      exact (mul_assoc _ _ _).symm
    · simpa only [hinv] using B.closed c.2 i

lemma lifted_attachingWord (c : G × C) :
    (liftedBoundary B v hinv hc).attachingWord c = liftWord v c.1 (B.attachingWord c.2) := by
  simp only [PolygonTarget.Boundary.attachingWord]
  rw [liftWord_ofFn']
  rfl

lemma lifted_relators : Set.range (liftedBoundary B v hinv hc).attachingWord =
    Relators v (Set.range B.attachingWord) := by
  ext z
  constructor
  · rintro ⟨c,rfl⟩
    exact ⟨c.1,B.attachingWord c.2,⟨c.2,rfl⟩,lifted_attachingWord B v hinv hc c⟩
  · rintro ⟨g,w,⟨c,rfl⟩,rfl⟩
    exact ⟨(g,c),lifted_attachingWord B v hinv hc (g,c)⟩

/-- A null word in the base polygon bouquet, lifted from any deck coordinate,
is a null word in the actual independently indexed cover presentation. -/
theorem lifted_nullWord (g : G) (w : Word A)
    (hw : PresentedGroup.mk (FreeGroup.mk '' Set.range B.attachingWord) (FreeGroup.mk w) = 1) :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (liftedBoundary B v hinv hc).attachingWord)
      (FreeGroup.mk (liftWord v g w)) = 1 := by
  obtain ⟨k,hk⟩ := WordPictures.existence w hw
  have hl := homotopy_lift v (by rintro w ⟨c,rfl⟩; exact hc c) hk g
  rw [← lifted_relators B v hinv hc] at hl
  exact WordPictures.sound hl

end VoltageWords

/-!
The actual elementary triangles imply the compressed cone polygon equations.
Unlike the redundant polygon bouquet, this presentation retains exactly the
elementary indexed top triangles.
-/

section
namespace GraphGroupWalk
open SimpleGraph
variable {V H : Type*} {G : SimpleGraph V} [Group H]

lemma eval_potential (c : G.Dart → H) (p : V → H)
    (he : ∀ e : G.Dart, p e.fst * c e = p e.snd)
    {u v : V} (q : G.Walk u v) : p u * eval c q = p v := by
  induction q with
  | nil => exact mul_one _
  | @cons u v z h q ih =>
    rw [eval_cons, ← mul_assoc, he ⟨(u,v),h⟩, ih]
end GraphGroupWalk
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable

lemma macroCell_eq_or_symm {e f : MacroGraph.graph.Dart} (h : macroCell e = macroCell f) :
    e = f ∨ e = f.symm := by
  have hh := Sym2.eq_iff.mp (congrArg Subtype.val h)
  rcases e with ⟨⟨a,b⟩,he⟩
  rcases f with ⟨⟨c,d⟩,hf⟩
  rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {H : Type*} [_root_.Group H] (c : ElementaryDart n w → H)
  (hc : ∀ e, c (elementaryRev n w e) = (c e)⁻¹)
  (hcell : ∀ a : ElementaryCell n w d,
    (List.ofFn (fun i => c (elementarySide n w d a i))).prod = 1)

include hc hcell in
lemma elementary_radial_relation (a : Top n w) (e : MacroGraph.graph.Dart) :
    c (.inr (a,e.fst),true) * c (elementaryOld n w (macroStep n w a e.adj)) =
      c (.inr (a,e.snd),true) := by
  have hp (f : MacroGraph.graph.Dart) (hf : macroCellDart (macroCell e) = f) :
      c (.inr (a,f.fst),true) * c (elementaryOld n w (macroStep n w a f.adj)) =
        c (.inr (a,f.snd),true) := by
    have hh := hcell (.inl (a,macroCell e))
    change (List.ofFn (fun i => c (elementaryTriangle n w a (macroCellDart (macroCell e)) i))).prod = 1 at hh
    rw [hf] at hh
    simp only [elementaryTriangle,List.ofFn_succ,List.ofFn_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,List.prod_cons,List.prod_nil,mul_one] at hh
    have hr := hc (.inr (a,f.snd),true)
    change c (.inr (a,f.snd),false) = _ at hr
    rw [hr,← mul_assoc] at hh
    exact mul_inv_eq_one.mp hh
  rcases macroCell_eq_or_symm (macroCellDart_cell (macroCell e)) with he | he
  · exact hp e he
  · have hh := hp e.symm he
    have hr : c (elementaryOld n w (macroStep n w a e.symm.adj)) =
        (c (elementaryOld n w (macroStep n w a e.adj)))⁻¹ := by
      exact (congrArg (fun z => c (elementaryOld n w z)) (macroStep_reverse n w a e.adj)).trans
        ((congrArg c (elementaryOld_rev n w (macroStep n w a e.adj))).trans
          (hc (elementaryOld n w (macroStep n w a e.adj))))
    rw [hr] at hh
    exact (eq_mul_inv_iff_mul_eq.mp hh.symm)

include hc hcell in
lemma elementary_old_cell (a : Cell n w d) :
    (List.ofFn (fun i => c (elementaryOld n w (side n w d a i)))).prod = 1 := by
  rcases a with f | a | a | a
  · exact hcell (.inr (.inl f))
  · rcases a with ⟨a,u,p,hp⟩
    have he := GraphGroupWalk.eval_potential
      (fun e : MacroGraph.graph.Dart => c (elementaryOld n w (macroStep n w a e.adj)))
      (fun v => c (.inr (a,v),true)) (elementary_radial_relation n w d c hc hcell a) p
    have hz : GraphGroupWalk.eval
        (fun e : MacroGraph.graph.Dart => c (elementaryOld n w (macroStep n w a e.adj))) p = 1 :=
      mul_left_cancel (he.trans (mul_one _).symm)
    have hm := congrArg (fun z : List (Dart n w) => (z.map (c ∘ elementaryOld n w)).prod)
      (macro_darts n w a p hp)
    simp only [List.map_map,List.map_ofFn,Function.comp_def] at hm
    exact hm.symm.trans hz
  · exact hcell (.inr (.inr (.inl a)))
  · exact hcell (.inr (.inr (.inr a)))

/-- The literal edge-bouquet presentation of the elementary cells. -/
abbrev ElementaryPolygonGroup := PresentedGroup
  (FreeGroup.mk '' Set.range (elementaryBoundary n w d).attachingWord)

def elementaryPolygonValue (e : ElementaryDart n w) : ElementaryPolygonGroup n w d :=
  PresentedGroup.mk _ (FreeGroup.mk [e])

lemma elementaryPolygonValue_rev (e : ElementaryDart n w) :
    elementaryPolygonValue n w d (elementaryRev n w e) = (elementaryPolygonValue n w d e)⁻¹ := by
  unfold elementaryPolygonValue
  rw [← map_inv]
  congr 1

lemma elementaryPolygonValue_word (z : List (ElementaryDart n w)) :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (elementaryBoundary n w d).attachingWord)
      (FreeGroup.mk z) = (z.map (elementaryPolygonValue n w d)).prod := by
  induction z with
  | nil => exact map_one _
  | cons a z ih =>
    change PresentedGroup.mk _ (FreeGroup.mk ([a] ++ z)) = _
    rw [← FreeGroup.mul_mk,map_mul,ih]
    rfl

lemma elementaryPolygonValue_cell (a : ElementaryCell n w d) :
    (List.ofFn (fun i => elementaryPolygonValue n w d (elementarySide n w d a i))).prod = 1 := by
  have he := PresentedGroup.one_of_mem (show FreeGroup.mk (List.ofFn (elementarySide n w d a)) ∈
      FreeGroup.mk '' Set.range (elementaryBoundary n w d).attachingWord from
    ⟨(elementaryBoundary n w d).attachingWord a,⟨a,rfl⟩,rfl⟩)
  rw [elementaryPolygonValue_word,List.map_ofFn] at he
  exact he

end ConeSkeleton
end

namespace ConeSkeleton

section
open IncidenceTemplate CoreGeometry LetterPresentation
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Inclusion of original letters in the literal elementary edge bouquet. -/
def elementaryFreeComparison : FreeGroup (Fin (n+1)) →* ElementaryPolygonGroup n w d :=
  (PresentedGroup.mk _).comp
    (FreeGroup.map (fun i : Fin (n+1) => (Sum.inl (Sum.inl i) : ElementaryEdge n w)))

lemma elementaryFreeComparison_letter (a : Alphabet n) :
    elementaryFreeComparison n w d (freeLetter n a) =
      elementaryPolygonValue n w d (elementaryOld n w (letterDart n w a)) := by
  rw [freeLetter_mk]
  simp only [elementaryFreeComparison,MonoidHom.comp_apply,FreeGroup.map.mk,List.map_cons,List.map_nil]
  rfl

lemma elementaryFreeComparison_word (z : List (Alphabet n)) :
    elementaryFreeComparison n w d (FreeGroup.mk z) =
      PresentedGroup.mk (FreeGroup.mk '' Set.range (elementaryBoundary n w d).attachingWord)
        (FreeGroup.mk (z.map (elementaryOld n w ∘ letterDart n w))) := by
  simp only [elementaryFreeComparison,MonoidHom.comp_apply,FreeGroup.map.mk]
  rfl

lemma elementaryFreeComparison_relator (r : FreeGroup (Fin (n+1))) (hr : Relator n w d r) :
    elementaryFreeComparison n w d r = 1 := by
  let c : Dart n w → ElementaryPolygonGroup n w d := elementaryPolygonValue n w d ∘ elementaryOld n w
  have hc : ∀ e, c (rev n w e) = (c e)⁻¹ := fun e => elementaryPolygonValue_rev n w d (elementaryOld n w e)
  have hcell := elementary_old_cell n w d (elementaryPolygonValue n w d)
    (elementaryPolygonValue_rev n w d) (elementaryPolygonValue_cell n w d)
  cases hr with
  | fan l i present v p fields =>
    rw [MasterGraph.Path.eval_map]
    simp only [elementaryFreeComparison_letter]
    exact fan_relator_value n w d c hc hcell l i present v p fields
  | top l present fans v p core =>
    rw [MasterGraph.Path.eval_map]
    simp only [elementaryFreeComparison_letter]
    exact top_relator_value n w d c hc hcell l present fans v p core
  | square l τ present =>
    rw [MasterGraph.squareWord_map]
    simp only [elementaryFreeComparison_letter]
    exact square_relator_value n w d c hc hcell l τ present
  | six x present =>
    rw [map_list_prod,List.map_ofFn]
    simp only [Function.comp_def,elementaryFreeComparison_letter]
    exact six_relator_value n w d c hcell x present

lemma elementaryRelatorClosure_le :
    Subgroup.normalClosure (Relator n w d) ≤ (elementaryFreeComparison n w d).ker := by
  apply Subgroup.normalClosure_le_normal
  intro r hr
  exact elementaryFreeComparison_relator n w d r hr

/-- The original presentation maps to the elementary edge-bouquet group.
No fundamental-group equivalence, asphericity, or infinitude is assumed here. -/
def elementaryComparison : LetterPresentation.Group n w d →* ElementaryPolygonGroup n w d :=
  QuotientGroup.lift (Subgroup.normalClosure
    (show Set (FreeGroup (Fin (n+1))) from Relator n w d))
    (elementaryFreeComparison n w d) (elementaryRelatorClosure_le n w d)

lemma elementaryComparison_letter (a : Alphabet n) :
    elementaryComparison n w d (LetterPresentation.letter n w d a) =
      elementaryPolygonValue n w d (elementaryOld n w (letterDart n w a)) :=
  elementaryFreeComparison_letter n w d a

lemma elementaryComparison_word (z : List (Alphabet n)) :
    elementaryComparison n w d (PresentedGroup.mk (Relator n w d) (FreeGroup.mk z)) =
      ((z.map (elementaryOld n w ∘ letterDart n w)).map (elementaryPolygonValue n w d)).prod := by
  change elementaryFreeComparison n w d (FreeGroup.mk z) = _
  rw [elementaryFreeComparison_word,elementaryPolygonValue_word]

/-- Literal null words in the original generators have elementary-cell disks. -/
lemma nullWord_to_elementary (z : List (Alphabet n))
    (hz : PresentedGroup.mk (Relator n w d) (FreeGroup.mk z) = 1) :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (elementaryBoundary n w d).attachingWord)
      (FreeGroup.mk (z.map (elementaryOld n w ∘ letterDart n w))) = 1 := by
  rw [← elementaryFreeComparison_word]
  change elementaryComparison n w d (PresentedGroup.mk _ (FreeGroup.mk z)) = 1
  rw [hz,map_one]

end

open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch SimpleGraph
attribute [local instance] Classical.propDecidable

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

abbrev elementaryOldValue (e : Dart n w) : ElementaryPolygonGroup n w d :=
  elementaryPolygonValue n w d (elementaryOld n w e)

lemma elementaryOldValue_rev (e : Dart n w) :
    elementaryOldValue n w d (rev n w e) = (elementaryOldValue n w d e)⁻¹ :=
  elementaryPolygonValue_rev n w d (elementaryOld n w e)

lemma elementaryOldValue_cell (a : Cell n w d) :
    (List.ofFn (fun i => elementaryOldValue n w d (side n w d a i))).prod = 1 :=
  elementary_old_cell n w d (elementaryPolygonValue n w d)
    (elementaryPolygonValue_rev n w d) (elementaryPolygonValue_cell n w d) a

lemma base_fanVertex (i : Fin 7) : IsFanVertex i (.inl (CoreWordGraph.base i)) := by
  have hh : ∀ i : Fin 7, IsFanVertex i (.inl (CoreWordGraph.base i)) := by decide
  exact hh i

def fanBase (i : Fin 7) : FanVertex i := ⟨.inl (CoreWordGraph.base i),base_fanVertex i⟩

/-- The gauge at an old apex is its literal radial edge to the fixed fan base.
The bouquet vertex has gauge one. -/
def oldGauge : Vertex n w → ElementaryPolygonGroup n w d
  | .inl _ => 1
  | .inr f => elementaryOldValue n w d (.inr ⟨f,fanBase f.val.1⟩,true)

lemma radial_gauge (f : Fan n w) (v : FanVertex f.val.1) :
    oldGauge n w d (.inr f) * elementaryComparison n w d
      (letterVoltage n w d (.inr ⟨f,v⟩,true)) =
        elementaryOldValue n w d (.inr ⟨f,v⟩,true) := by
  let c := elementaryOldValue n w d
  let l := extendRow n (.inl f.val.1) f.val.2
  let p := CoreWordGraph.toMaster (fan f.val.1) (CoreWordGraph.fanRoute f.val.1 v)
  have he := MasterGraph.Path.eval_potential
    (fanPotential n w c f) ((c ∘ letterDart n w) ∘ l) p (by
      intro k hk
      obtain ⟨e,rfl,hm⟩ := CoreWordGraph.toMaster_fields (fan f.val.1)
        (CoreWordGraph.fanRoute f.val.1 v) k hk
      have hh := fanPotential_edge n w d c (elementaryOldValue_rev n w d)
        (elementaryOldValue_cell n w d) f e hm
      simpa only [Function.comp_apply,l,extendRow,dite_eq_left (show (.inl e : Field) ∈ rowSupport (.inl f.val.1)
        from by simpa [rowSupport] using hm)] using hh)
  rw [MasterGraph.Path.eval_comp] at he
  have hv : elementaryComparison n w d (letterVoltage n w d (.inr ⟨f,v⟩,true)) =
      p.eval l (c ∘ letterDart n w) := by
    change elementaryFreeComparison n w d (FreeGroup.mk (radialWord n w f v)) = _
    rw [radialWord,← CoreWordGraph.toMaster_word, mk_pathWord,MasterGraph.Path.eval_map]
    simp only [elementaryFreeComparison_letter]
    rfl
  rw [hv]
  simpa only [fanPotential,dite_eq_left (base_fanVertex f.val.1),dite_eq_left v.property,
    radialValue,oldGauge,fanBase,c,p] using he

/-- Every old edge equals its prescribed letter voltage, up to endpoint gauge.
This removes the extra free factors of the edge-bouquet only on CLOSED paths. -/
lemma old_gauge (e : Dart n w) :
    elementaryOldValue n w d e = oldGauge n w d (start n w e) *
      elementaryComparison n w d (letterVoltage n w d e) *
        (oldGauge n w d (start n w (rev n w e)))⁻¹ := by
  rcases e with ⟨i|⟨f,v⟩,b⟩
  · have he : (.inl i,b) = letterDart n w (i,b) := rfl
    rw [he,letterVoltage_letter,elementaryComparison_letter]
    simp only [start_letter,rev_letter,oldGauge,one_mul,inv_one,mul_one]
  · cases b with
    | true =>
      simpa only [start,rev,Bool.not_true,oldGauge,inv_one,mul_one] using
        (radial_gauge n w d f v).symm
    | false =>
      have he := congrArg Inv.inv (radial_gauge n w d f v).symm
      have hr := elementaryOldValue_rev n w d (.inr ⟨f,v⟩,true)
      have hv := letterVoltage_rev n w d (.inr ⟨f,v⟩,true)
      change letterVoltage n w d (.inr ⟨f,v⟩,false) = _ at hv
      change elementaryOldValue n w d (.inr ⟨f,v⟩,false) = _ at hr
      rw [hr,hv,map_inv]
      simpa only [start,rev,Bool.not_false,oldGauge,one_mul,mul_inv_rev] using he

lemma macro_old_gauge (a : Top n w) {u v : MacroGraph.Vertex} (p : MacroGraph.graph.Walk u v) :
    GraphGroupWalk.eval (macroValue n w (elementaryOldValue n w d) a) p =
      oldGauge n w d (macroVertex n w a u) *
        elementaryComparison n w d (GraphGroupWalk.eval (macroValue n w (letterVoltage n w d) a) p) *
          (oldGauge n w d (macroVertex n w a v))⁻¹ := by
  induction p with
  | nil => simp only [GraphGroupWalk.eval_nil,map_one,mul_one,mul_inv_cancel]
  | @cons u v z h p ih =>
    simp only [GraphGroupWalk.eval_cons,macroValue]
    change MacroGraph.Adjacent u v at h
    change elementaryOldValue n w d (macroStep n w a h) *
        GraphGroupWalk.eval (macroValue n w (elementaryOldValue n w d) a) p =
      oldGauge n w d (macroVertex n w a u) *
        elementaryComparison n w d (letterVoltage n w d (macroStep n w a h) *
          GraphGroupWalk.eval (macroValue n w (letterVoltage n w d) a) p) *
        (oldGauge n w d (macroVertex n w a z))⁻¹
    rw [old_gauge,macroStep_start,macroStep_end,ih,map_mul]
    group

/-- The gauge at a top apex is based at the fixed macro root. -/
def elementaryGauge : ElementaryVertex n w → ElementaryPolygonGroup n w d
  | .inl v => oldGauge n w d v
  | .inr a => elementaryPolygonValue n w d (.inr (a,MacroGraph.point 0),true) *
      oldGauge n w d (macroVertex n w a (MacroGraph.point 0))

lemma top_radial_gauge (a : Top n w) (v : MacroGraph.Vertex) :
    elementaryPolygonValue n w d (.inr (a,v),true) =
      elementaryGauge n w d (.inr a) * elementaryComparison n w d
        (elementaryVoltage n w (letterVoltage n w d) (.inr (a,v),true)) *
          (elementaryGauge n w d (.inl (macroVertex n w a v)))⁻¹ := by
  have he := GraphGroupWalk.eval_potential
    (macroValue n w (elementaryOldValue n w d) a)
    (fun v => elementaryPolygonValue n w d (.inr (a,v),true))
    (elementary_radial_relation n w d (elementaryPolygonValue n w d)
      (elementaryPolygonValue_rev n w d) (elementaryPolygonValue_cell n w d) a)
    (MacroGraph.route v)
  rw [macro_old_gauge] at he
  simpa only [elementaryGauge,elementaryVoltage,macroPotential,mul_assoc] using he.symm

/-- The full elementary graph has exactly its prescribed voltages modulo
endpoint gauges, proved using the literal fan and top cone triangles. -/
theorem elementary_gauge (e : ElementaryDart n w) :
    elementaryPolygonValue n w d e = elementaryGauge n w d (elementaryStart n w e) *
      elementaryComparison n w d (elementaryVoltage n w (letterVoltage n w d) e) *
        (elementaryGauge n w d (elementaryStart n w (elementaryRev n w e)))⁻¹ := by
  rcases e with ⟨i|⟨a,v⟩,b⟩
  · exact old_gauge n w d (i,b)
  · cases b with
    | true => exact top_radial_gauge n w d a v
    | false =>
      have he := congrArg Inv.inv (top_radial_gauge n w d a v)
      have hr := elementaryPolygonValue_rev n w d (.inr (a,v),true)
      change elementaryPolygonValue n w d (.inr (a,v),false) = _ at hr
      rw [hr]
      simpa only [elementaryStart,elementaryRev,Bool.not_false,
        elementaryVoltage,map_inv,mul_inv_rev,inv_inv,mul_assoc] using he

end ConeSkeleton

section

lemma prod_gauge_telescope {H : Type*} [Group H] (u x : ℕ → H) (k : ℕ) :
    (List.ofFn (fun i : Fin k => u i.val * x i.val * (u (i.val+1))⁻¹)).prod =
      u 0 * (List.ofFn (fun i : Fin k => x i.val)).prod * (u k)⁻¹ := by
  induction k generalizing u x with
  | zero => simp only [List.ofFn_zero,List.prod_nil,mul_one,mul_inv_cancel]
  | succ k ih =>
    simp only [List.ofFn_succ,List.prod_cons,Fin.val_zero,Fin.val_succ]
    rw [ih (fun i => u (i+1)) (fun i => x (i+1))]
    group

/-- Ordered, noncommutative telescope around a cyclic boundary. -/
lemma prod_gauge_cycle {H : Type*} [Group H] {k : ℕ} (hk : 0 < k)
    (u x : Fin k → H) :
    (List.ofFn (fun i => u i * x i * (u (finRotate k i))⁻¹)).prod =
      u ⟨0,hk⟩ * (List.ofFn x).prod * (u ⟨0,hk⟩)⁻¹ := by
  let u' : ℕ → H := fun j => u ⟨j % k,Nat.mod_lt _ hk⟩
  let x' : ℕ → H := fun j => x ⟨j % k,Nat.mod_lt _ hk⟩
  have hzero : u' 0 = u ⟨0,hk⟩ := by simp only [u',Nat.zero_mod]
  have hlast : u' k = u ⟨0,hk⟩ := by simp only [u',Nat.mod_self]
  have hx (i : Fin k) : x' i.val = x i := by simp only [x',Nat.mod_eq_of_lt i.isLt]
  have hu (i : Fin k) : u' i.val = u i := by simp only [u',Nat.mod_eq_of_lt i.isLt]
  have hn (i : Fin k) : u' (i.val+1) = u (finRotate k i) := by
    apply congrArg u
    apply Fin.ext
    cases k with
    | zero => omega
    | succ k =>
      rw [finRotate_apply,Fin.val_add_one]
      split_ifs with hi
      · subst i; simp only [Fin.val_last,Nat.mod_self]
      · exact Nat.mod_eq_of_lt (by have := i.isLt; have hv : i.val ≠ k := fun h => hi (Fin.ext h); omega)
  have hh := prod_gauge_telescope u' x' k
  simpa only [hu,hx,hn,hzero,hlast] using hh

namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Every closed elementary boundary with trivial original-group voltage is
null in the elementary-cell edge-bouquet. Open paths are deliberately excluded:
the extra fan/top apex gauges do not vanish on open paths. -/
theorem elementary_closed_null {ell : ℕ} (hell : 0 < ell) (word : Fin ell → ElementaryDart n w)
    (closed : ∀ i, elementaryStart n w (word (finRotate ell i)) =
      elementaryStart n w (elementaryRev n w (word i)))
    (hvol : (List.ofFn (fun i => elementaryVoltage n w (letterVoltage n w d) (word i))).prod = 1) :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (elementaryBoundary n w d).attachingWord)
      (FreeGroup.mk (List.ofFn word)) = 1 := by
  rw [elementaryPolygonValue_word,List.map_ofFn]
  have he : (fun i => elementaryPolygonValue n w d (word i)) =
      (fun i => elementaryGauge n w d (elementaryStart n w (word i)) *
        elementaryComparison n w d (elementaryVoltage n w (letterVoltage n w d) (word i)) *
          (elementaryGauge n w d (elementaryStart n w (word (finRotate ell i))))⁻¹) := by
    funext i
    rw [closed,elementary_gauge]
  simp only [Function.comp_def]
  rw [he,prod_gauge_cycle hell]
  have hv := congrArg (elementaryComparison n w d) hvol
  rw [map_list_prod,List.map_ofFn,map_one] at hv
  simp only [Function.comp_def] at hv
  rw [hv,mul_one,mul_inv_cancel]

end ConeSkeleton
end

namespace VoltageWords
open HyperbolicObstruction.WordPictures HyperbolicObstruction.PictureSwitch
variable {A G V C : Type*} [Group G]

lemma decode_inverse (v : A → G) (e : (G × A) × Bool) :
    (encode v).symm (invLetter e) =
      (((encode v).symm e).1 * voltage v ((encode v).symm e).2,
        invLetter ((encode v).symm e).2) := by
  apply (encode v).injective
  rw [Equiv.apply_symm_apply,encode_reverse,Equiv.apply_symm_apply]

/-- The deck coordinate at every corner is forced by the literal prefix. -/
lemma cycle_deck_prefix (v : A → G) {m : ℕ} (hm : 0 < m)
    (w : Fin m → A × Bool) (g : Fin m → G)
    (hg : ∀ i, g (finRotate m i) = g i * voltage v (w i)) (i : Fin m) :
    g i = g ⟨0,hm⟩ * ((List.ofFn (voltage v ∘ w)).take i.val).prod := by
  cases m with
  | zero => omega
  | succ m =>
    induction i using Fin.inductionOn with
    | zero => simp only [Fin.val_zero,List.take_zero,List.prod_nil,mul_one]; rfl
    | @succ i ih =>
      have he : finRotate (m+1) i.castSucc = i.succ := by
        rw [finRotate_apply]
        apply Fin.ext
        rw [Fin.val_add_one,ite_eq_right]
        · rfl
        · intro h
          have hh := congrArg Fin.val h
          simp only [Fin.val_castSucc,Fin.val_last] at hh
          omega
      rw [← he,hg,ih]
      have hp := List.prod_take_succ (List.ofFn (voltage v ∘ w)) i.val
        (by simp only [List.length_ofFn]; omega)
      rw [List.getElem_ofFn] at hp
      change _ = _ * ((List.ofFn (voltage v ∘ w)).take ((finRotate (m+1) i.castSucc).val)).prod
      rw [he]
      simp only [Fin.val_succ]
      rw [hp,mul_assoc]
      rfl
lemma cycle_voltage (v : A → G) {m : ℕ} (hm : 0 < m)
    (w : Fin m → A × Bool) (g : Fin m → G)
    (hg : ∀ i, g (finRotate m i) = g i * voltage v (w i)) :
    total v (List.ofFn w) = 1 := by
  have he (i : Fin m) : voltage v (w i) =
      (g i)⁻¹ * (1 : G) * ((g (finRotate m i))⁻¹)⁻¹ := by rw [hg]; group
  simp only [total,List.map_ofFn,Function.comp_def]
  simp_rw [he]
  rw [HyperbolicObstruction.prod_gauge_cycle hm]
  simp

variable (B : PolygonTarget.Boundary C (A × Bool) V) (v : A → G)
  (hinv : B.rev = invLetter)
variable {m : ℕ} (hm : 0 < m) (w : Fin m → (G × A) × Bool)
  (closed : ∀ i, liftedStart B v (w (finRotate m i)) = liftedStart B v (invLetter (w i)))

include closed

lemma closed_decks (i : Fin m) :
    ((encode v).symm (w (finRotate m i))).1 =
      ((encode v).symm (w i)).1 * voltage v ((encode v).symm (w i)).2 := by
  have hh := congrArg Prod.fst (closed i)
  simpa only [liftedStart,decode_inverse] using hh

include hinv in
lemma projected_closed (i : Fin m) :
    B.start ((encode v).symm (w (finRotate m i))).2 =
      B.start (B.rev ((encode v).symm (w i)).2) := by
  have hh := congrArg Prod.snd (closed i)
  simpa only [liftedStart,decode_inverse,hinv] using hh

lemma closed_is_lift :
    List.ofFn w = liftWord v (((encode v).symm (w ⟨0,hm⟩)).1)
      (List.ofFn (fun i => ((encode v).symm (w i)).2)) := by
  rw [liftWord_ofFn']
  apply congrArg List.ofFn
  funext i
  rw [← cycle_deck_prefix v hm (fun j => ((encode v).symm (w j)).2)
      (fun j => ((encode v).symm (w j)).1) (closed_decks B v w closed) i]
  exact (encode v).apply_symm_apply (w i) |>.symm

include hm in
lemma projected_voltage :
    total v (List.ofFn (fun i => ((encode v).symm (w i)).2)) = 1 :=
  cycle_voltage v hm _ (fun j => ((encode v).symm (w j)).1) (closed_decks B v w closed)

end VoltageWords

/-! Actual genus-zero disks for every closed elementary loop in the original
letter voltage cover. No cycle-representation or asphericity hypothesis. -/

namespace ConeSkeleton

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch WordPictures
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Positive voltages of the genuine elementary indexed edges. -/
def elementaryPositiveVoltage (e : ElementaryEdge n w) : LetterPresentation.Group n w d :=
  elementaryVoltage n w (letterVoltage n w d) (e,true)

lemma elementaryVoltage_signed (e : ElementaryDart n w) :
    elementaryVoltage n w (letterVoltage n w d) e =
      VoltageWords.voltage (elementaryPositiveVoltage n w d) e := by
  rcases e with ⟨e,b⟩
  cases b with
  | true => rfl
  | false => exact elementaryVoltage_rev n w (letterVoltage n w d) (letterVoltage_rev n w d) (e,true)

lemma elementaryTotal_cell (c : ElementaryCell n w d) :
    VoltageWords.total (elementaryPositiveVoltage n w d) ((elementaryBoundary n w d).attachingWord c) = 1 := by
  simp only [VoltageWords.total,PolygonTarget.Boundary.attachingWord,List.map_ofFn,Function.comp_def,
    ← elementaryVoltage_signed]
  exact elementaryLetterVoltage_cell n w d c

/-- Same individual cells and deck coordinates as `elementaryLetterLiftedBoundary`,
encoded using signed positive lifted edges rather than shifted dart reversal. -/
def elementaryEncodedBoundary := VoltageWords.liftedBoundary (elementaryBoundary n w d)
  (elementaryPositiveVoltage n w d) rfl (elementaryTotal_cell n w d)

variable {ell : ℕ} (hell : 0 < ell)
  (word : Fin ell → (LetterPresentation.Group n w d × ElementaryEdge n w) × Bool)
  (closed : ∀ i, (elementaryEncodedBoundary n w d).start (word (finRotate ell i)) =
    (elementaryEncodedBoundary n w d).start (invLetter (word i)))

include hell closed

/-- Every closed loop in this incidence cover is a null word in its exact lifted
polygon presentation. This is not a topological universal-cover assertion. -/
theorem elementary_encoded_null :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (elementaryEncodedBoundary n w d).attachingWord)
      (FreeGroup.mk (List.ofFn word)) = 1 := by
  let v := elementaryPositiveVoltage n w d
  let B := elementaryBoundary n w d
  let base : Fin ell → ElementaryDart n w := fun i => ((VoltageWords.encode v).symm (word i)).2
  have hclosed : ∀ i, B.start (base (finRotate ell i)) = B.start (B.rev (base i)) :=
    VoltageWords.projected_closed B v rfl word closed
  have hvol : (List.ofFn (fun i => elementaryVoltage n w (letterVoltage n w d) (base i))).prod = 1 := by
    simp only [elementaryVoltage_signed]
    simpa only [VoltageWords.total,List.map_ofFn,Function.comp_def] using
      VoltageWords.projected_voltage B v hell word closed
  have hbase := elementary_closed_null n w d hell base hclosed hvol
  rw [VoltageWords.closed_is_lift B v hell word closed]
  exact VoltageWords.lifted_nullWord B v rfl (elementaryTotal_cell n w d) _ _ hbase

/-- Every nonempty closed elementary loop has a genuinely genus-zero labelled
disk, carrying all independent lift-cell coordinates, and exactly one exterior.
The exterior coefficient is zero; no relator identities are conflated. -/
theorem elementary_cover_disk :
    ∃ (Q : CellPicture.{0} ((elementaryEncodedBoundary n w d).outsideTarget ell hell word closed
      (fun c => Finsupp.single c (1 : ℤ)) (fun _ => false) (by intro _ h; cases h)))
      (xs : List Q.Dart), IsBoundary Q.pairing.face xs ∧
      xs.map (((elementaryEncodedBoundary n w d).outsideTarget ell hell word closed
        (fun c => Finsupp.single c (1 : ℤ)) (fun _ => false) (by intro _ h; cases h)).edge ∘ Q.index) =
          List.ofFn word ∧
      ∀ x, (elementaryEncodedBoundary n w d).outsideTag ell hell word closed (Q.index x) =
        if x ∈ xs then some true else none := by
  exact (elementaryEncodedBoundary n w d).nullWord_picture ell hell word closed
    (fun c => Finsupp.single c (1 : ℤ)) (fun _ => false) (by intro l h; cases h) rfl
      (elementary_encoded_null n w d hell word closed)

end

/-! Signed-edge encoding preserves all individual cell identities and the
closed-picture chain. Sphere vanishing therefore applies to indexed disks. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch WordPictures
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma elementaryEncoded_label (c : LetterPresentation.Group n w d × ElementaryCell n w d)
    (i : Fin (elementarySize n w d c.2)) :
    (elementaryEncodedBoundary n w d).label c i =
      VoltageWords.encode (elementaryPositiveVoltage n w d)
        ((elementaryLetterLiftedBoundary n w d).label c i) := by
  simp only [elementaryEncodedBoundary,VoltageWords.liftedBoundary,
    elementaryLetterLiftedBoundary,elementaryLiftedBoundary,elementaryOffset,
    elementaryBoundary,elementaryVoltage_signed,Function.comp_def]

lemma elementaryEncoded_rev (e : LetterPresentation.Group n w d × ElementaryDart n w) :
    VoltageWords.encode (elementaryPositiveVoltage n w d)
      ((elementaryLetterLiftedBoundary n w d).rev e) =
      invLetter (VoltageWords.encode (elementaryPositiveVoltage n w d) e) := by
  change VoltageWords.encode _ (e.1 * elementaryVoltage n w (letterVoltage n w d) e.2,
    invLetter e.2) = _
  rw [elementaryVoltage_signed]
  exact VoltageWords.encode_reverse _ _ _

lemma elementaryEncoded_side (s : (elementaryEncodedBoundary n w d).Side) :
    (elementaryEncodedBoundary n w d).sideLabel s =
      VoltageWords.encode (elementaryPositiveVoltage n w d)
        ((elementaryLetterLiftedBoundary n w d).sideLabel s) := by
  rcases s with ⟨c,b,i⟩
  change Fin (elementarySize n w d c.2) at i
  cases b with
  | true => exact elementaryEncoded_label n w d c i
  | false =>
    change invLetter ((elementaryEncodedBoundary n w d).label c i) =
      VoltageWords.encode _ ((elementaryLetterLiftedBoundary n w d).rev
        ((elementaryLetterLiftedBoundary n w d).label c i))
    rw [elementaryEncoded_rev,elementaryEncoded_label]

variable {A : Type*} [AddCommGroup A]
  (weight : (LetterPresentation.Group n w d × ElementaryCell n w d) → A)

/-- Decode only the edge alphabet. Every cell, side, face and coefficient is
unchanged. The geometric incidence conditions follow from the actual target. -/
def elementaryDecodePicture
    (P : CellPicture ((elementaryEncodedBoundary n w d).target weight
      (fun _ => false) (by intro _ h; cases h))) :
    CellPicture (elementaryRawTarget n w d (letterVoltage n w d)
      (letterVoltage_rev n w d) (letterVoltage_cell n w d) weight) where
  Dart := P.Dart
  pairing := P.pairing
  genusZero := P.genusZero
  index := P.index
  mapped := P.mapped
  respects := (elementaryRawTarget n w d (letterVoltage n w d)
    (letterVoltage_rev n w d) (letterVoltage_cell n w d) weight).respects_of_edge
      P.pairing P.index P.mapped (by
        intro x
        change (elementaryLetterLiftedBoundary n w d).sideLabel (P.index (P.pairing.edge x)) =
          (elementaryLetterLiftedBoundary n w d).rev
            ((elementaryLetterLiftedBoundary n w d).sideLabel (P.index x))
        apply (VoltageWords.encode (elementaryPositiveVoltage n w d)).injective
        rw [elementaryEncoded_rev,←elementaryEncoded_side,←elementaryEncoded_side]
        exact P.respects.2 x)

lemma elementaryDecode_chain
    (P : CellPicture ((elementaryEncodedBoundary n w d).target weight
      (fun _ => false) (by intro _ h; cases h))) :
    (elementaryDecodePicture n w d weight P).chain = P.chain := rfl

/-- Uniform diagram uniqueness for exactly marked disks on the actual cover. -/
theorem uniform_elementary_indexed_sphere_zero {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      IndexedFilling.SphereZero (elementaryEncodedBoundary n w d)
        (fun c => Finsupp.single c (1 : ℤ)) := by
  obtain ⟨M,hM,hh⟩ := uniform_elementary_sphere_chain_zero.{0,0,0} ha hb hd
  refine ⟨M,hM,?_⟩
  intro n w d hgood P I
  have hz := hh n w d hgood (LetterPresentation.Group n w d)
    ((LetterPresentation.Group n w d × ElementaryCell n w d) →₀ ℤ)
    (letterVoltage n w d) (letterVoltage_rev n w d) (letterVoltage_cell n w d)
    (fun c => Finsupp.single c 1)
    (elementaryDecodePicture n w d (fun c => Finsupp.single c 1)
      (I.closedPicture rfl (fun c => Finsupp.single c 1)))
  exact (WordPicture.Indexing.closed_chain I rfl _).symm.trans hz

end

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch WordPictures SignedWalks
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Every componentwise closed walk, including the empty walk, has an actual
literal nullword certificate. No graph-connectedness hypothesis is needed. -/
theorem elementary_encoded_walk_null (x) (u)
    (h : Walk (elementaryEncodedBoundary n w d).start x x u) :
    IndexedFilling.Null (elementaryEncodedBoundary n w d) u := by
  by_cases hu : u = []
  · subst u
    change PresentedGroup.mk _ (1 : FreeGroup _) = 1
    exact map_one _
  have hpos : 0 < u.length := List.length_pos_iff.mpr hu
  have hc : ∀ i : Fin u.length,
      (elementaryEncodedBoundary n w d).start u[(finRotate u.length i).val] =
        (elementaryEncodedBoundary n w d).start (invLetter u[i.val]) :=
    h.closed_rotate hpos
  have hh := elementary_encoded_null n w d hpos (fun i : Fin u.length => u[i.val]) hc
  simpa only [IndexedFilling.Null,List.ofFn_getElem] using hh

end

/-! Actual integral boundaries for the uncompressed cone cells. -/
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch IntegralIncidence

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def elementaryPolygons : Polygons (ElementaryEdge n w) (ElementaryVertex n w)
    (ElementaryCell n w d) where
  start := elementaryStart n w
  size := elementarySize n w d
  positive := (elementaryBoundary n w d).positive
  side := elementarySide n w d
  closed := (elementaryBoundary n w d).closed

abbrev LetterC₂ := LiftedCellularChain n w d (LetterPresentation.Group n w d)
abbrev LetterC₁ := (LetterPresentation.Group n w d × ElementaryEdge n w) →₀ ℤ
abbrev LetterC₀ := (LetterPresentation.Group n w d × ElementaryVertex n w) →₀ ℤ

def letterBoundary₁ : LetterC₁ n w d →ₗ[ℤ] LetterC₀ n w d :=
  d₁ (elementaryStart n w) (elementaryVoltage n w (letterVoltage n w d))

def letterBoundary₂ : LetterC₂ n w d →ₗ[ℤ] LetterC₁ n w d :=
  (elementaryPolygons n w d).d₂ (elementaryVoltage n w (letterVoltage n w d))

/-- Actual lifted elementary incidence, not an augmented base-cell differential.
Every cell-voltage equation used here was proved from the original relators. -/
theorem letterBoundary_boundary (z : LetterC₂ n w d) :
    letterBoundary₁ n w d (letterBoundary₂ n w d z) = 0 :=
  (elementaryPolygons n w d).boundary_boundary _
    (elementaryVoltage_rev n w _ (letterVoltage_rev n w d))
    (elementaryLetterVoltage_cell n w d) z

/-- The exact algebraic cycle space whose sphere producer is needed. -/
def LetterCycles₂ : Submodule ℤ (LetterC₂ n w d) := LinearMap.ker (letterBoundary₂ n w d)

end ConeSkeleton

section

/-! Full independent lifted-cell d₂ injectivity. Rooted nullword disks, glued
with their exact cell identities, now resolve the algebraic cycle frontier. -/

namespace VoltageWords
open HyperbolicObstruction.IndexedFilling
variable {E G : Type*} [Group G]
lemma letterChain_encode (v : E → G) (e : G × (E × Bool)) :
    letterChain (encode v e) = IntegralIncidence.edgeChain (voltage v) e := by
  rcases e with ⟨g,e,b⟩
  cases b <;> rfl
end VoltageWords

namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch WordPictures
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma elementaryEncoded_cellBoundary
    (c : LetterPresentation.Group n w d × ElementaryCell n w d) :
    IndexedFilling.cellBoundary (elementaryEncodedBoundary n w d) c =
      (elementaryPolygons n w d).faceBoundary (elementaryVoltage n w (letterVoltage n w d)) c := by
  unfold IndexedFilling.cellBoundary IntegralIncidence.Polygons.faceBoundary
  apply Finset.sum_congr rfl
  intro i _
  change Fin (elementarySize n w d c.2) at i
  rw [elementaryEncoded_label,VoltageWords.letterChain_encode]
  have he : VoltageWords.voltage (elementaryPositiveVoltage n w d) =
      elementaryVoltage n w (letterVoltage n w d) := funext (fun e => (elementaryVoltage_signed n w d e).symm)
  rw [he]
  rfl

lemma elementaryEncoded_boundary :
    IndexedFilling.boundary (elementaryEncodedBoundary n w d) = letterBoundary₂ n w d := by
  unfold IndexedFilling.boundary letterBoundary₂ IntegralIncidence.Polygons.d₂
  exact congrArg (Finsupp.linearCombination ℤ) (funext (elementaryEncoded_cellBoundary n w d))

/-- No cycle-representation hypothesis remains: the original standing bounded
test assumptions imply injectivity of the ACTUAL uncompressed lifted d₂. -/
theorem uniform_elementary_boundary_injective {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      Function.Injective (letterBoundary₂ n w d) := by
  obtain ⟨M,hM,hh⟩ := uniform_elementary_indexed_sphere_zero ha hb hd
  refine ⟨M,hM,?_⟩
  intro n w d hgood
  rw [←elementaryEncoded_boundary]
  exact IndexedFilling.boundary_injective _ rfl (hh n w d hgood)
    (elementary_encoded_walk_null n w d)

/-- In particular the full algebraic cellular cycle module is zero. This is
not yet an identification with topological universal-cover homology. -/
theorem uniform_elementary_cycles_zero {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      LetterCycles₂ n w d = ⊥ := by
  obtain ⟨M,hM,hh⟩ := uniform_elementary_boundary_injective ha hb hd
  exact ⟨M,hM,fun n w d hgood => LinearMap.ker_eq_bot.mpr (hh n w d hgood)⟩

end ConeSkeleton
end

/-! No reselection: the same final arrays already have the precise uniform
lifted-picture estimate. Apply the new disk-chain left inverse to those arrays. -/

namespace IncidenceTemplate

section
open CoreGeometry LetterPresentation ConeSkeleton PictureSwitch WordPictures
attribute [local instance] Classical.propDecidable

abbrev finalSize (m : ℕ) := (finalDiagramStage m).size
abbrev finalMaster (m : ℕ) := (finalDiagramStage m).master
abbrev finalSix (m : ℕ) := (finalDiagramStage m).six

lemma finalDiagramStage_elementary_sphere_zero (m : ℕ)
    (G A : Type) [Group G] [AddCommGroup A]
    (v : Dart (finalSize m) (finalMaster m) → G)
    (hv : ∀ e, v (rev (finalSize m) (finalMaster m) e) = (v e)⁻¹)
    (hc : ∀ a : Cell (finalSize m) (finalMaster m) (finalSix m),
      (List.ofFn (fun i => v (side (finalSize m) (finalMaster m) (finalSix m) a i))).prod = 1)
    (weight : G × ElementaryCell (finalSize m) (finalMaster m) (finalSix m) → A)
    : ∀ P : CellPicture.{0} (elementaryRawTarget (finalSize m) (finalMaster m) (finalSix m)
      v hv hc weight), P.chain = 0 := by
  have he := elementaryMacroWeight_eq (finalSize m) (finalMaster m) (finalSix m) weight
  rw [←he]
  intro P
  rw [←elementaryMacro_chain (finalSize m) (finalMaster m) (finalSix m) v hv hc
    (elementaryTopWeight (finalSize m) (finalMaster m) (finalSix m) weight)
    (elementaryTopWeight_symm (finalSize m) (finalMaster m) (finalSix m) weight)
    (fun g a => weight (g,.inr a)) P]
  exact finalDiagramStage_lifted_chain_zero m G A v hv hc _ _ _ _
    (elementaryMacro_frozenMapped (finalSize m) (finalMaster m) (finalSix m) v hv hc _ P _ _ _)

lemma finalDiagramStage_indexed_sphere_zero (m : ℕ) :
    IndexedFilling.SphereZero (elementaryEncodedBoundary (finalSize m) (finalMaster m) (finalSix m))
      (fun c => Finsupp.single c (1 : ℤ)) := by
  intro P I
  have hz := finalDiagramStage_elementary_sphere_zero m
    (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m))
    ((LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m) ×
      ElementaryCell (finalSize m) (finalMaster m) (finalSix m)) →₀ ℤ)
    (letterVoltage (finalSize m) (finalMaster m) (finalSix m))
    (letterVoltage_rev (finalSize m) (finalMaster m) (finalSix m))
    (letterVoltage_cell (finalSize m) (finalMaster m) (finalSix m))
    (fun c => Finsupp.single c 1)
    (elementaryDecodePicture (finalSize m) (finalMaster m) (finalSix m) (fun c => Finsupp.single c 1)
      (I.closedPicture rfl (fun c => Finsupp.single c 1)))
  exact (WordPicture.Indexing.closed_chain I rfl _).symm.trans hz

/-- Injectivity of the full d₂ for the selected arrays. -/
theorem finalDiagramStage_boundary_injective (m : ℕ) :
    Function.Injective (letterBoundary₂ (finalSize m) (finalMaster m) (finalSix m)) := by
  rw [←elementaryEncoded_boundary]
  exact IndexedFilling.boundary_injective _ rfl (finalDiagramStage_indexed_sphere_zero m)
    (elementary_encoded_walk_null (finalSize m) (finalMaster m) (finalSix m))

end

/-! Arbitrary-valued cell cochains of the same chosen arrays extend to edges.
This is the full polygonal obstruction extension, not only a basis-vector
injectivity statement. -/

open CoreGeometry LetterPresentation ConeSkeleton PictureSwitch WordPictures
attribute [local instance] Classical.propDecidable

lemma finalDiagramStage_indexed_sphere_zero_weight (m : ℕ) (A : Type) [AddCommGroup A]
    (weight : LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m) ×
      ElementaryCell (finalSize m) (finalMaster m) (finalSix m) → A) :
    IndexedFilling.SphereZero
      (elementaryEncodedBoundary (finalSize m) (finalMaster m) (finalSix m)) weight := by
  intro P I
  have hz := finalDiagramStage_elementary_sphere_zero m
    (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) A
    (letterVoltage (finalSize m) (finalMaster m) (finalSix m))
    (letterVoltage_rev (finalSize m) (finalMaster m) (finalSix m))
    (letterVoltage_cell (finalSize m) (finalMaster m) (finalSix m)) weight
    (elementaryDecodePicture (finalSize m) (finalMaster m) (finalSix m) weight
      (I.closedPicture rfl weight))
  exact (WordPicture.Indexing.closed_chain I rfl _).symm.trans hz

/-- The literal lifted-edge cochain whose coboundary is any prescribed
independent lifted-cell cochain. No sphere-map producer is assumed. -/
theorem finalDiagramStage_extend_cochain (m : ℕ) (A : Type) [AddCommGroup A]
    (weight : LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m) ×
      ElementaryCell (finalSize m) (finalMaster m) (finalSix m) → A) :
    ∀ c, IndexedFilling.leftInverse
      (elementaryEncodedBoundary (finalSize m) (finalMaster m) (finalSix m)) weight
      (IndexedFilling.cellBoundary
        (elementaryEncodedBoundary (finalSize m) (finalMaster m) (finalSix m)) c) = weight c :=
  IndexedFilling.leftInverse_cell _ weight rfl
    (finalDiagramStage_indexed_sphere_zero_weight m A weight)
    (elementary_encoded_walk_null (finalSize m) (finalMaster m) (finalSix m))

end IncidenceTemplate

section

/-! Reindex the literal finite barycentric carrier onto the frozen challenge's
vertex type `Fin n`. No change of realization or topology is involved. -/

open scoped Topology
namespace FinitePolyhedron
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def reindex (K : AbstractSimplicialComplex V) (e : V ≃ W) : AbstractSimplicialComplex W :=
  { K.toPreAbstractSimplicialComplex.map e with
    singleton_mem := fun w => ⟨{e.symm w},K.singleton_mem _,by simp⟩ }

omit [DecidableEq V] in
lemma rename_mem (K : AbstractSimplicialComplex V) (e : V ≃ W) (x : V → ℝ) :
    x ∈ carrierSet K ↔ (fun j => x (e.symm j)) ∈ carrierSet (reindex K e) := by
  constructor
  · rintro ⟨h0,h1,s,hs,hx⟩
    refine ⟨fun j => h0 _,?_,s.image e,⟨s,hs,rfl⟩,?_⟩
    · simpa only [e.symm.sum_comp] using h1
    · intro j hj
      apply hx
      contrapose! hj
      exact Finset.mem_image.mpr ⟨e.symm j,hj,e.apply_symm_apply j⟩
  · rintro ⟨h0,h1,t,⟨s,hs,rfl⟩,hx⟩
    refine ⟨fun i => ?_,?_,s,hs,?_⟩
    · simpa using h0 (e i)
    · simpa only [e.symm.sum_comp] using h1
    · intro i hi
      simpa only [e.symm_apply_apply] using hx (e i) (by simpa using hi)

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- Coordinate permutation, restricted to the exact two carrier subtypes. -/
lemma reindexPi_apply (e : V ≃ W) (x : V → ℝ) (j : W) :
    Homeomorph.piCongrLeft (Y := fun _ : W => ℝ) e x j = x (e.symm j) := by
  simpa using Homeomorph.piCongrLeft_apply_apply (Y := fun _ : W => ℝ) e x (e.symm j)

def reindexHomeomorph (K : AbstractSimplicialComplex V) (e : V ≃ W) :
    Carrier K ≃ₜ Carrier (reindex K e) :=
  (Homeomorph.piCongrLeft (Y := fun _ : W => ℝ) e).subtype (fun x => by
    have he := funext (reindexPi_apply e x)
    rw [he]
    exact rename_mem K e x)

omit [DecidableEq V] in
@[simp] lemma reindexHomeomorph_apply (K : AbstractSimplicialComplex V) (e : V ≃ W)
    (x : Carrier K) (j : W) : (reindexHomeomorph K e x).val j = x.val (e.symm j) :=
  reindexPi_apply e x.val j

omit [DecidableEq V] in
@[simp] lemma reindexHomeomorph_vertex (K : AbstractSimplicialComplex V) (e : V ≃ W) (v : V) :
    reindexHomeomorph K e (vertex K v) = vertex (reindex K e) (e v) := by
  ext j
  rw [reindexHomeomorph_apply]
  simp only [vertex,Pi.single_apply]
  by_cases h : j = e v
  · subst j; simp
  · have hi : e.symm j ≠ v := fun he => h (by simpa [he] using e.apply_symm_apply j |>.symm)
    simp [h,hi]

/-- The exact finite-complex representation in the release reference. -/
def toFiniteComplex (K : AbstractSimplicialComplex V) : FiniteComplex :=
  ⟨Fintype.card V,reindex K (Fintype.equivFin V)⟩

def toFiniteComplexHomeomorph (K : AbstractSimplicialComplex V) :
    Carrier K ≃ₜ (toFiniteComplex K).Carrier :=
  reindexHomeomorph K (Fintype.equivFin V)

end FinitePolyhedron

namespace FiniteComplex
instance (K : FiniteComplex) : CompactSpace K.Carrier :=
  inferInstanceAs (CompactSpace (FinitePolyhedron.Carrier K.complex))
end FiniteComplex
end

/-! The actual elementary incidence data now defines an actual finite
barycentric polyhedron. This file proves compactness and connectivity only;
no CW-universal-cover comparison is smuggled in as a structure field. -/

namespace ConeSkeleton
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
attribute [local instance] Classical.propDecidable
local instance : DecidableEq (ElementaryVertex n w) := Classical.decEq _
local instance : DecidableEq (ElementaryEdge n w) := Classical.decEq _
local instance : DecidableEq (ElementaryCell n w d) := Classical.decEq _

def elementaryPolygonData : FinitePolygonModel.Data
    (ElementaryVertex n w) (ElementaryEdge n w) (ElementaryCell n w d) where
  size := elementarySize n w d
  positive := (elementaryBoundary n w d).positive
  side := elementarySide n w d
  start := elementaryStart n w
  closed := (elementaryBoundary n w d).closed

abbrev elementarySimplicialComplex := (elementaryPolygonData n w d).complex
abbrev elementaryPolyhedron := Carrier (elementarySimplicialComplex n w d)

def elementaryBaseVertex : (elementaryPolygonData n w d).Vertex :=
  (elementaryPolygonData n w d).old (.inl (.inl ()))

def elementaryBasepoint : elementaryPolyhedron n w d :=
  vertex (elementarySimplicialComplex n w d) (elementaryBaseVertex n w d)

lemma elementary_old_connected (v : ElementaryVertex n w) :
    Joined (elementaryBasepoint n w d)
      (vertex (elementarySimplicialComplex n w d) ((elementaryPolygonData n w d).old v)) := by
  change @Joined (Carrier ((elementaryPolygonData n w d).complex)) _ _ _
  rcases v with (u|f)|a
  · cases u
    exact Joined.refl _
  · simpa only [elementaryBasepoint, elementaryBaseVertex, elementaryPolygonData,
      elementarySimplicialComplex, elementaryStart, start, macroVertex] using
      ((elementaryPolygonData n w d).endpoints_joined (.inl (.inr ⟨f,fanBase f.val.1⟩))).symm
  · simpa only [elementaryBasepoint, elementaryBaseVertex, elementaryPolygonData,
      elementarySimplicialComplex, elementaryStart, start, macroVertex] using
      ((elementaryPolygonData n w d).endpoints_joined (.inr (a,.inr ()))).symm

instance elementaryPolyhedron_pathConnected : PathConnectedSpace (elementaryPolyhedron n w d) :=
  (elementaryPolygonData n w d).pathConnected_of_graph (.inl (.inl ())) (elementary_old_connected n w d)

/-- Literal conversion into the finite complex type. -/
def elementaryFiniteComplex : FiniteComplex :=
  toFiniteComplex (elementarySimplicialComplex n w d)

def elementaryFiniteHomeomorph :
    elementaryPolyhedron n w d ≃ₜ (elementaryFiniteComplex n w d).Carrier :=
  toFiniteComplexHomeomorph (elementarySimplicialComplex n w d)

def elementaryFiniteBasepoint : (elementaryFiniteComplex n w d).Carrier :=
  elementaryFiniteHomeomorph n w d (elementaryBasepoint n w d)

instance elementaryFinite_pathConnected :
    PathConnectedSpace (elementaryFiniteComplex n w d).Carrier := by
  refine ⟨⟨elementaryFiniteBasepoint n w d⟩, fun x y => ?_⟩
  simpa only [Homeomorph.apply_symm_apply] using (PathConnectedSpace.joined ((elementaryFiniteHomeomorph n w d).symm x)
    ((elementaryFiniteHomeomorph n w d).symm y)).map (elementaryFiniteHomeomorph n w d).continuous

end ConeSkeleton

section
variable {G : Type*} [Group G]

lemma group_cycle_transport {m : ℕ} (u v : Fin m → G)
    (h : ∀ i, u i * v i = u (finRotate m i)) : (List.ofFn v).prod = 1 := by
  cases m with
  | zero => simp
  | succ m =>
    have hp : ∀ i : Fin (m+1), u 0 * ((List.ofFn v).take i.val).prod = u i := by
      apply Fin.induction
      · simp
      · intro i ih
        simp only [Fin.val_castSucc] at ih
        have ht := List.prod_take_succ (List.ofFn v) i.val
          (by simpa only [List.length_ofFn] using i.isLt.trans (Nat.lt_succ_self m))
        have he : (List.ofFn v)[i.val] = v i.castSucc := List.getElem_ofFn _
        rw [he] at ht
        change u 0 * ((List.ofFn v).take (i.val+1)).prod = _
        rw [ht,←mul_assoc,ih,h]
        exact congrArg u (finRotate_of_lt i.isLt)
    have ht := List.prod_take_succ (List.ofFn v) m (by simp)
    have he : (List.ofFn v)[m] = v (Fin.last m) := List.getElem_ofFn _
    rw [he] at ht
    have hh := h (Fin.last m)
    rw [finRotate_last,←hp (Fin.last m),mul_assoc] at hh
    simp only [Fin.val_last] at hh
    rw [←ht] at hh
    have hlen : (List.ofFn v).length = m+1 := List.length_ofFn
    have ht0 : (List.ofFn v).take (m+1) = List.ofFn v := List.take_of_length_le hlen.le
    rw [ht0] at hh
    exact mul_left_cancel (hh.trans (mul_one (u 0)).symm)

end

/-! Restricting any flat voltage on the actual triangulation to the original
indexed graph. Literal cap triangles prove every original boundary relation. -/

namespace FinitePolygonModel.Data

section
open FinitePolyhedron
variable {V E C G : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C] [Group G]
variable (P : Data V E C) (W : Voltage P.complex G)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma triangle_of_facet (f : P.Facet) {a b c : P.Vertex}
    (ha : a ∈ P.facet f) (hb : b ∈ P.facet f) (hc : c ∈ P.facet f) :
    {a,b,c} ∈ P.complex.faces := by
  refine ⟨by simp,Or.inr ⟨f,?_⟩⟩
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl|rfl <;> assumption

omit [Fintype V] [Fintype E] [Fintype C] in
lemma voltage_on_facet (f : P.Facet) {a b c : P.Vertex}
    (ha : a ∈ P.facet f) (hb : b ∈ P.facet f) (hc : c ∈ P.facet f) :
    W.value a b * W.value b c = W.value a c :=
  W.triangle a b c (P.triangle_of_facet f ha hb hc)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma graph_edge_first (e : E) (b : Bool) :
    {P.old (P.start (e,b)),P.mid e b} ∈ P.complex.faces := by
  cases b
  · exact P.edge_of_facet (.inl (e,2)) (by simp [facet,graphFace]) (by simp [facet,graphFace])
  · exact P.edge_of_facet (.inl (e,0)) (by simp [facet,graphFace]) (by simp [facet,graphFace])

omit [Fintype V] [Fintype E] [Fintype C] in
lemma graph_edge_middle (e : E) (b : Bool) :
    {P.mid e b,P.mid e (!b)} ∈ P.complex.faces := by
  cases b <;> exact P.edge_of_facet (.inl (e,1)) (by simp [facet,graphFace]) (by simp [facet,graphFace])

/-- A full signed original edge is exactly its three path segments. -/
def graphTransport (e : E × Bool) : G :=
  W.value (P.old (P.start e)) (P.mid e.1 e.2) *
    W.value (P.mid e.1 e.2) (P.mid e.1 (!e.2)) *
      W.value (P.mid e.1 (!e.2)) (P.old (P.start (e.1,!e.2)))

omit [Fintype V] [Fintype E] [Fintype C] in
lemma graphTransport_reverse (e : E × Bool) :
    P.graphTransport W (e.1,!e.2) = (P.graphTransport W e)⁻¹ := by
  have h0 := W.reverse (P.graph_edge_first e.1 e.2)
  have h1 := W.reverse (P.graph_edge_middle e.1 e.2)
  have h2 := W.reverse (P.graph_edge_first e.1 (!e.2))
  rcases e with ⟨e,b⟩
  simp only [graphTransport,Bool.not_not,mul_inv_rev] at *
  rw [h0,h1,h2]
  group

omit [Fintype V] [Fintype E] [Fintype C] in
lemma graphTransport_signed (e : E × Bool) :
    P.graphTransport W e = signed (fun e => P.graphTransport W (e,true)) e := by
  rcases e with ⟨e,b⟩
  cases b
  · exact P.graphTransport_reverse W (e,true)
  · rfl

/-- A cap supplies a literal potential at every actual boundary occurrence. -/
def capTransport (q : P.Position) : G :=
  W.value (P.apex q.1) (P.outer q) * W.value (P.outer q) (P.base q)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma capTransport_next (q : P.Position) :
    P.capTransport W q * W.value (P.base q) (P.base (P.next q)) = P.capTransport W (P.next q) := by
  have h0 := P.voltage_on_facet W (.inr (q,0))
    (a := P.outer q) (b := P.base q) (c := P.base (P.next q))
    (by simp [facet,collarFace]) (by simp [facet,collarFace]) (by simp [facet,collarFace])
  have h1 := P.voltage_on_facet W (.inr (q,1))
    (a := P.outer q) (b := P.outer (P.next q)) (c := P.base (P.next q))
    (by simp [facet,collarFace]) (by simp [facet,collarFace]) (by simp [facet,collarFace])
  have h2 := P.voltage_on_facet W (.inr (q,2))
    (a := P.apex q.1) (b := P.outer q) (c := P.outer (P.next q))
    (by simp [facet,collarFace]) (by simp [facet,collarFace]) (by simp [facet,collarFace])
  change (W.value (P.apex q.1) (P.outer q) * W.value (P.outer q) (P.base q)) * _ =
    W.value (P.apex q.1) (P.outer (P.next q)) * W.value (P.outer (P.next q)) (P.base (P.next q))
  rw [mul_assoc,h0,←h1,←mul_assoc,h2]

omit [Fintype V] [Fintype E] [Fintype C] in
lemma capTransport_side (c : C) (i : Fin (P.size c)) :
    P.capTransport W ⟨c,(i,0)⟩ * P.graphTransport W (P.side c i) =
      P.capTransport W ⟨c,(finRotate _ i,0)⟩ := by
  have h0 := P.capTransport_next W ⟨c,(i,0)⟩
  have h1 := P.capTransport_next W ⟨c,(i,1)⟩
  have h2 := P.capTransport_next W ⟨c,(i,2)⟩
  rw [base_next] at h2
  change P.capTransport W ⟨c,(i,0)⟩ *
    W.value (P.old (P.start (P.side c i))) (P.mid (P.side c i).1 (P.side c i).2) =
      P.capTransport W ⟨c,(i,1)⟩ at h0
  change P.capTransport W ⟨c,(i,1)⟩ *
    W.value (P.mid (P.side c i).1 (P.side c i).2) (P.mid (P.side c i).1 (!(P.side c i).2)) =
      P.capTransport W ⟨c,(i,2)⟩ at h1
  change P.capTransport W ⟨c,(i,2)⟩ *
    W.value (P.mid (P.side c i).1 (!(P.side c i).2))
      (P.old (P.start ((P.side c i).1,!(P.side c i).2))) =
      P.capTransport W ⟨c,(finRotate _ i,0)⟩ at h2
  rw [graphTransport,←mul_assoc,←mul_assoc,h0,h1,h2]

omit [Fintype V] [Fintype E] [Fintype C] in
/-- No relation in the original polygon presentation is merely assumed. -/
lemma graphTransport_cell (c : C) :
    (List.ofFn (fun i => P.graphTransport W (P.side c i))).prod = 1 :=
  group_cycle_transport (fun i => P.capTransport W ⟨c,(i,0)⟩)
    (fun i => P.graphTransport W (P.side c i)) (P.capTransport_side W c)

end

/-! Literal graph paths and canonical extensions of chosen old-vertex routes. -/

open FinitePolyhedron
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable (P : Data V E C)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma outer_base_edge (q : P.Position) : {P.outer q,P.base q} ∈ P.complex.faces :=
  P.edge_of_facet (.inr (q,0)) (by simp [facet,collarFace]) (by simp [facet,collarFace])

omit [Fintype V] [Fintype E] [Fintype C] in
lemma apex_outer_edge (q : P.Position) : {P.apex q.1,P.outer q} ∈ P.complex.faces :=
  P.edge_of_facet (.inr (q,2)) (by simp [facet,collarFace]) (by simp [facet,collarFace])

abbrev edgeClass {a b : P.Vertex} (h : {a,b} ∈ P.complex.faces) :=
  Path.Homotopic.Quotient.mk (edgePath P.complex h)

/-- All three literal subdivisions of an indexed signed graph edge. -/
def graphChain (e : E × Bool) :
    EdgeChain P.complex (P.old (P.start e)) (P.old (P.start (e.1,!e.2))) :=
  .cons (P.graph_edge_first e.1 e.2)
    (.cons (P.graph_edge_middle e.1 e.2)
      (.cons (by simpa only [Finset.pair_comm] using P.graph_edge_first e.1 (!e.2)) (.nil _)))

omit [Fintype V] [Fintype E] [Fintype C] in
lemma graphChain_eval {G : Type*} [Group G] (W : Voltage P.complex G) (e : E × Bool) :
    Voltage.EdgeChain.eval W (P.graphChain e) = P.graphTransport W e := by
  simp only [graphChain,Voltage.EdgeChain.eval_cons,Voltage.EdgeChain.eval_nil,mul_one,graphTransport,mul_assoc]

variable (o : V)
abbrev OldRoutes := ∀ a : V,
  Path.Homotopic.Quotient (vertex P.complex (P.old o)) (vertex P.complex (P.old a))
variable (R : P.OldRoutes o)

def graphRoutes : ∀ a : V ⊕ (E × Bool),
    Path.Homotopic.Quotient (vertex P.complex (P.old o)) (vertex P.complex (P.graph a))
  | .inl a => R a
  | .inr (e,b) => (R (P.start (e,b))).trans (P.edgeClass (P.graph_edge_first e b))

def baseRoutes (q : P.Position) :
    Path.Homotopic.Quotient (vertex P.complex (P.old o)) (vertex P.complex (P.base q)) := by
  unfold base dartStart
  split_ifs
  · exact R (P.start (P.side q.1 q.2.1))
  · exact P.graphRoutes o R (.inr (P.side q.1 q.2.1))
  · exact P.graphRoutes o R (.inr ((P.side q.1 q.2.1).1,!(P.side q.1 q.2.1).2))

def outerRoutes (q : P.Position) :
    Path.Homotopic.Quotient (vertex P.complex (P.old o)) (vertex P.complex (P.outer q)) :=
  (P.baseRoutes o R q).trans (P.edgeClass (P.outer_base_edge q)).symm

def firstPosition (c : C) : P.Position := ⟨c,(⟨0,P.positive c⟩,0)⟩

/-- Contracting only the new subdivision/collar tree; no original edge is
collapsed by this choice. -/
def routes : ∀ a : P.Vertex,
    Path.Homotopic.Quotient (vertex P.complex (P.old o)) (vertex P.complex a)
  | .inl a => P.graphRoutes o R a
  | .inr (.inr q) => P.outerRoutes o R q
  | .inr (.inl c) => (P.outerRoutes o R (P.firstPosition c)).trans
      (P.edgeClass (P.apex_outer_edge (P.firstPosition c))).symm

lemma routes_old (a : V) : P.routes o R (P.old a) = R a := rfl
lemma routes_base (q : P.Position) : P.routes o R (P.base q) = P.baseRoutes o R q := by
  rcases q with ⟨c,i,j⟩
  fin_cases j <;> rfl

lemma based_eq_one_of_route {X : Type*} [TopologicalSpace X] {x a b : X}
    (r : Path.Homotopic.Quotient x a) (p : Path.Homotopic.Quotient a b) :
    r.trans (p.trans (r.trans p).symm) = .refl x := by
  rw [←Path.Homotopic.Quotient.trans_assoc,Path.Homotopic.Quotient.trans_symm]

lemma based_eq_one_of_rev_route {X : Type*} [TopologicalSpace X] {x a b : X}
    (r : Path.Homotopic.Quotient x b) (p : Path.Homotopic.Quotient a b) :
    (r.trans p.symm).trans (p.trans r.symm) = .refl x := by
  rw [Path.Homotopic.Quotient.trans_assoc,←Path.Homotopic.Quotient.trans_assoc p.symm p,
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.trans_symm]

abbrev rootedVoltage := RootedPaths.voltage (P.old o) (P.routes o R)

lemma rooted_first (e : E) (b : Bool) :
    (P.rootedVoltage o R).value (P.old (P.start (e,b))) (P.mid e b) = 1 := by
  change RootedPaths.edgeLoop (P.old o) (P.routes o R) _ _ = 1
  rw [RootedPaths.edgeLoop_of_edge _ _ (P.graph_edge_first e b)]
  apply MulOpposite.unop_injective
  exact based_eq_one_of_route (R (P.start (e,b))) (P.edgeClass (P.graph_edge_first e b))

lemma rooted_last (e : E) (b : Bool) :
    (P.rootedVoltage o R).value (P.mid e b) (P.old (P.start (e,b))) = 1 := by
  rw [(P.rootedVoltage o R).reverse (P.graph_edge_first e b),rooted_first,inv_one]

lemma rooted_outer_base (q : P.Position) :
    (P.rootedVoltage o R).value (P.outer q) (P.base q) = 1 := by
  change RootedPaths.edgeLoop (P.old o) (P.routes o R) _ _ = 1
  rw [RootedPaths.edgeLoop_of_edge _ _ (P.outer_base_edge q)]
  apply MulOpposite.unop_injective
  change (P.outerRoutes o R q).trans ((P.edgeClass (P.outer_base_edge q)).trans
    (P.routes o R (P.base q)).symm) = .refl _
  rw [routes_base]
  exact based_eq_one_of_rev_route (P.baseRoutes o R q) (P.edgeClass (P.outer_base_edge q))

lemma rooted_apex_first (c : C) :
    (P.rootedVoltage o R).value (P.apex c) (P.outer (P.firstPosition c)) = 1 := by
  change RootedPaths.edgeLoop (P.old o) (P.routes o R) _ _ = 1
  rw [RootedPaths.edgeLoop_of_edge _ _ (show {P.apex c,P.outer (P.firstPosition c)} ∈ P.complex.faces from P.apex_outer_edge (P.firstPosition c))]
  apply MulOpposite.unop_injective
  exact based_eq_one_of_rev_route (P.outerRoutes o R (P.firstPosition c))
    (P.edgeClass (P.apex_outer_edge (P.firstPosition c)))

lemma rooted_graphTransport (e : E × Bool) :
    P.graphTransport (P.rootedVoltage o R) e = (P.rootedVoltage o R).value (P.mid e.1 e.2) (P.mid e.1 (!e.2)) := by
  rcases e with ⟨e,b⟩
  simp [graphTransport,rooted_first,rooted_last]

end FinitePolygonModel.Data

/-! Genuine continuous fundamental groups are generated by the finite edges. -/

namespace FinitePolyhedron.RootedPaths
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}
variable (o : V) (R : ∀ a : V, Path.Homotopic.Quotient (vertex K o) (vertex K a))

lemma eq_top_of_edge_mem (hR : R o = .refl _) (H : Subgroup (PiOne (K := K) o))
    (h : ∀ a b, {a,b} ∈ K.faces → (voltage o R).value a b ∈ H) : H = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨p,hp⟩ := Quotient.exists_rep y.unop
  obtain ⟨q,hq⟩ := edgePath_representative K p
  have hm {a b : V} (q : EdgeChain K a b) : Voltage.EdgeChain.eval (voltage o R) q ∈ H := by
    induction q with
    | nil a => exact H.one_mem
    | @cons a b c he q ih => exact H.mul_mem (h a b he) ih
  have hh := hm q
  rw [eval_chain,based_loop o R hR] at hh
  have he : MulOpposite.op q.pathClass = y := by
    apply MulOpposite.unop_injective
    exact (Path.Homotopic.Quotient.eq.mpr hq).symm.trans hp
  rwa [he] at hh

end FinitePolyhedron.RootedPaths

/-! New subdivision, collar and cone edges do not create fundamental-group
generators. This concerns the actual barycentric realization. -/

namespace FinitePolygonModel.Data
open FinitePolyhedron
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable (P : Data V E C)

lemma finRotate_noWrap {m : ℕ} (i : Fin m) (h : i.val+1 < m) :
    finRotate m i = ⟨i.val+1,h⟩ := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m => exact finRotate_of_lt (by omega)

omit [Fintype V] [Fintype E] [Fintype C] [DecidableEq V] [DecidableEq E] [DecidableEq C] in
lemma position_induction (S : P.Position → Prop) (h0 : ∀ c, S (P.firstPosition c))
    (hs : ∀ q, S q → S (P.next q)) (q : P.Position) : S q := by
  rcases q with ⟨c,i,j⟩
  have hi : ∀ k (hk : k < P.size c), S ⟨c,(⟨k,hk⟩,0)⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact h0 c
    | succ k ih =>
      intro hk
      have hk0 : k < P.size c := by omega
      have hh := hs _ (hs _ (hs _ (ih hk0)))
      change S ⟨c,(finRotate _ ⟨k,hk0⟩,0)⟩ at hh
      have hr := finRotate_noWrap (⟨k,hk0⟩ : Fin (P.size c)) hk
      rwa [hr] at hh
  have hh := hi i.val i.isLt
  fin_cases j
  · exact hh
  · exact hs _ hh
  · exact hs _ (hs _ hh)

variable (o : V) (R : P.OldRoutes o)
variable (H : Subgroup (RootedPaths.PiOne (K := P.complex) (P.old o)))
variable (hG : ∀ e, P.graphTransport (P.rootedVoltage o R) e ∈ H)

include hG in
lemma rooted_base_next_mem (q : P.Position) :
    (P.rootedVoltage o R).value (P.base q) (P.base (P.next q)) ∈ H := by
  rw [base_next]
  rcases q with ⟨c,i,j⟩
  fin_cases j
  · change (P.rootedVoltage o R).value (P.old (P.start (P.side c i)))
      (P.mid (P.side c i).1 (P.side c i).2) ∈ H
    rw [rooted_first]
    exact H.one_mem
  · change (P.rootedVoltage o R).value (P.mid (P.side c i).1 (P.side c i).2)
      (P.mid (P.side c i).1 (!(P.side c i).2)) ∈ H
    rw [←rooted_graphTransport]
    exact hG _
  · change (P.rootedVoltage o R).value (P.mid (P.side c i).1 (!(P.side c i).2))
      (P.old (P.start ((P.side c i).1,!(P.side c i).2))) ∈ H
    rw [rooted_last]
    exact H.one_mem

include hG in
lemma rooted_outer_diagonal_mem (q : P.Position) :
    (P.rootedVoltage o R).value (P.outer q) (P.base (P.next q)) ∈ H := by
  have he := P.voltage_on_facet (P.rootedVoltage o R) (.inr (q,0))
    (a := P.outer q) (b := P.base q) (c := P.base (P.next q))
    (by simp [facet,collarFace]) (by simp [facet,collarFace]) (by simp [facet,collarFace])
  rw [rooted_outer_base,one_mul] at he
  rw [←he]
  exact P.rooted_base_next_mem o R H hG q

include hG in
lemma rooted_outer_next_mem (q : P.Position) :
    (P.rootedVoltage o R).value (P.outer q) (P.outer (P.next q)) ∈ H := by
  have he := P.voltage_on_facet (P.rootedVoltage o R) (.inr (q,1))
    (a := P.outer q) (b := P.outer (P.next q)) (c := P.base (P.next q))
    (by simp [facet,collarFace]) (by simp [facet,collarFace]) (by simp [facet,collarFace])
  rw [rooted_outer_base,mul_one] at he
  rw [he]
  exact P.rooted_outer_diagonal_mem o R H hG q

include hG in
lemma rooted_apex_mem (q : P.Position) :
    (P.rootedVoltage o R).value (P.apex q.1) (P.outer q) ∈ H := by
  apply P.position_induction (fun q => (P.rootedVoltage o R).value (P.apex q.1) (P.outer q) ∈ H)
  · intro c
    rw [show (P.firstPosition c).1 = c from rfl,rooted_apex_first]
    exact H.one_mem
  · intro q ih
    have he := P.voltage_on_facet (P.rootedVoltage o R) (.inr (q,2))
      (a := P.apex q.1) (b := P.outer q) (c := P.outer (P.next q))
      (by simp [facet,collarFace]) (by simp [facet,collarFace]) (by simp [facet,collarFace])
    change (P.rootedVoltage o R).value (P.apex q.1) (P.outer (P.next q)) ∈ H
    rw [←he]
    exact H.mul_mem ih (P.rooted_outer_next_mem o R H hG q)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma voltage_facet_mem {G : Type*} [Group G] (W : Voltage P.complex G) (H : Subgroup G)
    (f : P.Facet) {z a b : P.Vertex} (hz : z ∈ P.facet f)
    (hza : W.value z a ∈ H) (hzb : W.value z b ∈ H)
    (ha : a ∈ P.facet f) (hb : b ∈ P.facet f) : W.value a b ∈ H := by
  have ht := P.voltage_on_facet W f hz ha hb
  have he : W.value a b = (W.value z a)⁻¹ * W.value z b := by rw [←ht]; simp
  rw [he]
  exact H.mul_mem (H.inv_mem hza) hzb

include hG in
lemma rooted_facet_mem (f : P.Facet) {a b : P.Vertex} (ha : a ∈ P.facet f) (hb : b ∈ P.facet f) :
    (P.rootedVoltage o R).value a b ∈ H := by
  let W := P.rootedVoltage o R
  have hself (a) : W.value a a ∈ H := by rw [W.self]; exact H.one_mem
  cases f with
  | inl e =>
    rcases e with ⟨e,j⟩
    fin_cases j
    · have hz : ∀ x ∈ P.facet (.inl (e,0)), W.value (P.old (P.start (e,true))) x ∈ H := by
        intro x hx
        simp [facet,graphFace] at hx
        rcases hx with rfl|rfl
        · exact hself _
        · rw [show W = P.rootedVoltage o R from rfl,P.rooted_first]; exact H.one_mem
      exact P.voltage_facet_mem W H (.inl (e,0)) (by simp [facet,graphFace]) (hz a ha) (hz b hb) ha hb
    · have hz : ∀ x ∈ P.facet (.inl (e,1)), W.value (P.mid e true) x ∈ H := by
        intro x hx
        simp [facet,graphFace] at hx
        rcases hx with rfl|rfl
        · exact hself _
        · exact (P.rooted_graphTransport o R (e,true)) ▸ hG (e,true)
      exact P.voltage_facet_mem W H (.inl (e,1)) (by simp [facet,graphFace]) (hz a ha) (hz b hb) ha hb
    · have hz : ∀ x ∈ P.facet (.inl (e,2)), W.value (P.mid e false) x ∈ H := by
        intro x hx
        simp [facet,graphFace] at hx
        rcases hx with rfl|rfl
        · exact hself _
        · rw [show W = P.rootedVoltage o R from rfl,P.rooted_last]; exact H.one_mem
      exact P.voltage_facet_mem W H (.inl (e,2)) (by simp [facet,graphFace]) (hz a ha) (hz b hb) ha hb
  | inr q =>
    rcases q with ⟨q,j⟩
    fin_cases j
    · have hz : ∀ x ∈ P.facet (.inr (q,0)), W.value (P.outer q) x ∈ H := by
        intro x hx
        simp [facet,collarFace] at hx
        rcases hx with rfl|rfl|rfl
        · exact hself _
        · rw [show W = P.rootedVoltage o R from rfl,P.rooted_outer_base]; exact H.one_mem
        · exact P.rooted_outer_diagonal_mem o R H hG q
      exact P.voltage_facet_mem W H (.inr (q,0)) (by simp [facet,collarFace]) (hz a ha) (hz b hb) ha hb
    · have hz : ∀ x ∈ P.facet (.inr (q,1)), W.value (P.outer q) x ∈ H := by
        intro x hx
        simp [facet,collarFace] at hx
        rcases hx with rfl|rfl|rfl
        · exact hself _
        · exact P.rooted_outer_next_mem o R H hG q
        · exact P.rooted_outer_diagonal_mem o R H hG q
      exact P.voltage_facet_mem W H (.inr (q,1)) (by simp [facet,collarFace]) (hz a ha) (hz b hb) ha hb
    · have hz : ∀ x ∈ P.facet (.inr (q,2)), W.value (P.apex q.1) x ∈ H := by
        intro x hx
        simp [facet,collarFace] at hx
        rcases hx with rfl|rfl|rfl
        · exact P.rooted_apex_mem o R H hG q
        · exact P.rooted_apex_mem o R H hG (P.next q)
        · exact hself _
      exact P.voltage_facet_mem W H (.inr (q,2)) (by simp [facet,collarFace]) (hz a ha) (hz b hb) ha hb

include hG in
/-- Only original graph generators are needed for the actual pi1. -/
lemma rooted_group_generated (hR : R o = .refl _) : H = ⊤ := by
  apply RootedPaths.eq_top_of_edge_mem (P.old o) (P.routes o R) hR
  intro a b hab
  rcases hab.2 with hsmall|⟨f,hf⟩
  · have he : a = b := Finset.card_le_one.mp hsmall a (by simp) b (by simp)
    subst b
    rw [(P.rootedVoltage o R).self]
    exact H.one_mem
  · exact P.rooted_facet_mem o R H hG f (hf (by simp)) (hf (by simp))

end FinitePolygonModel.Data

section

/-! Literal monodromy detects rooted edge words. -/

open scoped Topology
open Set
namespace FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

def detect (o : V) : RootedPaths.PiOne (K := K) o →* G where
  toFun p := (v.isQuotientCoveringMap.fundamentalGroupToMulOpposite (v.vertexFiber o 1) p.unop).unop
  map_one' := by
    change (v.isQuotientCoveringMap.fundamentalGroupToMulOpposite (v.vertexFiber o 1) 1).unop = 1
    rw [map_one]
    rfl
  map_mul' p q := by
    change (v.isQuotientCoveringMap.fundamentalGroupToMulOpposite (v.vertexFiber o 1) (q.unop * p.unop)).unop = _
    rw [map_mul,MulOpposite.unop_mul]

lemma detect_eq_iff (o : V) (p : RootedPaths.PiOne (K := K) o) (g : G) :
    v.detect o p = g ↔ g • (v.vertexFiber o 1).val =
      (v.isCoveringMap.monodromy p.unop (v.vertexFiber o 1)).val := by
  change (v.isQuotientCoveringMap.fundamentalGroupToMulOpposite (v.vertexFiber o 1) p.unop).unop = g ↔ _
  rw [←MulOpposite.op_injective.eq_iff]
  simpa only [MulOpposite.op_unop,MulOpposite.unop_op] using
    (v.isQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff
      (e := v.vertexFiber o 1) (γ := p.unop) (g := MulOpposite.op g))

lemma smul_vertexFiber (o : V) (g : G) :
    g • (v.vertexFiber o 1).val = (v.vertexFiber o g).val := by
  apply v.totalSpace_ext
  · rfl
  · change g * 1 = g
    exact mul_one g

lemma detect_chain (o : V) (p : FinitePolyhedron.EdgeChain K o o) :
    v.detect o (MulOpposite.op p.pathClass) = EdgeChain.eval v p := by
  apply (v.detect_eq_iff o _ _).mpr
  change _ = (v.isCoveringMap.monodromy p.pathClass (v.vertexFiber o 1)).val
  rw [EdgeChain.monodromy,one_mul]
  exact v.smul_vertexFiber o _

lemma detect_based_chain (o : V) (R : ∀ a, FinitePolyhedron.EdgeChain K o a)
    (hR : ∀ a, EdgeChain.eval v (R a) = 1) {a b : V} (p : FinitePolyhedron.EdgeChain K a b) :
    v.detect o (RootedPaths.based o (fun a => (R a).pathClass) p.pathClass) = EdgeChain.eval v p := by
  have hmono (a : V) (g : G) : v.isCoveringMap.monodromy (R a).pathClass (v.vertexFiber o g) =
      v.vertexFiber a g := by rw [EdgeChain.monodromy,hR,mul_one]
  have hsymm (a : V) (g : G) : v.isCoveringMap.monodromy (R a).pathClass.symm (v.vertexFiber a g) =
      v.vertexFiber o g := by rw [←hmono a g,v.monodromy_symm]
  apply (v.detect_eq_iff o _ _).mpr
  change _ = (v.isCoveringMap.monodromy ((R a).pathClass.trans (p.pathClass.trans (R b).pathClass.symm)) _).val
  rw [v.isCoveringMap.monodromy_trans_apply,hmono,v.isCoveringMap.monodromy_trans_apply,
    EdgeChain.monodromy,one_mul,hsymm]
  exact v.smul_vertexFiber o _

lemma detect_edgeLoop (o : V) (R : ∀ a, FinitePolyhedron.EdgeChain K o a)
    (hR : ∀ a, EdgeChain.eval v (R a) = 1) {a b : V} (h : {a,b} ∈ K.faces) :
    v.detect o (RootedPaths.edgeLoop o (fun a => (R a).pathClass) a b) = v.value a b := by
  have hh := v.detect_based_chain o R hR (.cons h (.nil b))
  simpa only [FinitePolyhedron.EdgeChain.pathClass_cons,FinitePolyhedron.EdgeChain.pathClass_nil,
    Path.Homotopic.Quotient.trans_refl,EdgeChain.eval_cons,EdgeChain.eval_nil,mul_one,
    RootedPaths.edgeLoop_of_edge o (fun a => (R a).pathClass) h] using hh

end FinitePolyhedron.Voltage
end

/-! The literal polygon presentation maps to the actual pi1, and its tree
normalization has no hidden van Kampen hypothesis. -/

namespace FinitePolygonModel.Data
open FinitePolyhedron
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable (P : Data V E C)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma graphTransport_voltage {G : Type*} [Group G] (v : E → G)
    (h : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1) (e : E × Bool) :
    P.graphTransport (P.voltage v h) e = signed v e := by
  rcases e with ⟨e,b⟩
  cases b <;> simp [graphTransport,voltage,value,graphValue,signed]

variable (o : V) (R : P.OldRoutes o)
lemma rooted_graphChain (e : E × Bool) :
    P.graphTransport (P.rootedVoltage o R) e =
      RootedPaths.based (P.old o) (P.routes o R) (P.graphChain e).pathClass := by
  rw [←graphChain_eval,RootedPaths.eval_chain]

lemma lift_graphTransport (z : List (E × Bool)) :
    FreeGroup.lift (fun e => P.graphTransport (P.rootedVoltage o R) (e,true)) (FreeGroup.mk z) =
      (z.map (P.graphTransport (P.rootedVoltage o R))).prod := by
  rw [FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro e he
  conv_rhs => rw [graphTransport_signed]
  rcases e with ⟨e,b⟩
  cases b <;> rfl

abbrev PolygonGroup := PresentedGroup (FreeGroup.mk '' Set.range (fun c => List.ofFn (P.side c)))

lemma polygonRelation_valid (r : FreeGroup E)
    (hr : r ∈ FreeGroup.mk '' Set.range (fun c => List.ofFn (P.side c))) :
    FreeGroup.lift (fun e => P.graphTransport (P.rootedVoltage o R) (e,true)) r = 1 := by
  rcases hr with ⟨z,⟨c,rfl⟩,rfl⟩
  rw [lift_graphTransport,List.map_ofFn]
  exact P.graphTransport_cell (P.rootedVoltage o R) c

def polygonToTopology : P.PolygonGroup →* RootedPaths.PiOne (K := P.complex) (P.old o) :=
  PresentedGroup.toGroup (P.polygonRelation_valid o R)

lemma polygonToTopology_value (e : E × Bool) :
    P.polygonToTopology o R (PresentedGroup.mk _ (FreeGroup.mk [e])) =
      P.graphTransport (P.rootedVoltage o R) e := by
  change FreeGroup.lift (fun e => P.graphTransport (P.rootedVoltage o R) (e,true)) (FreeGroup.mk [e]) = _
  rw [lift_graphTransport]
  simp

end FinitePolygonModel.Data

/-! Identification of the actual finite elementary polyhedron's pi1 with the
original letter presentation, using actual path classes and voltage covers. -/

namespace ConeSkeleton

section
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

local instance : DecidableEq (ElementaryVertex n w) := Classical.decEq _
local instance : DecidableEq (ElementaryEdge n w) := Classical.decEq _
local instance : DecidableEq (ElementaryCell n w d) := Classical.decEq _

abbrev elementaryRoot : ElementaryVertex n w := .inl (.inl ())

def elementaryCoreRoutes (v : Vertex n w) :
    Path.Homotopic.Quotient
      (vertex (elementarySimplicialComplex n w d) ((elementaryPolygonData n w d).old (elementaryRoot n w)))
      (vertex (elementarySimplicialComplex n w d) ((elementaryPolygonData n w d).old (.inl v))) := by
  rcases v with u|f
  · cases u
    exact .refl _
  · exact ((elementaryPolygonData n w d).graphChain (.inl (.inr ⟨f,fanBase f.val.1⟩),true)).pathClass.symm

/-- Only literal radial edges are chosen as old-vertex routes. -/
def elementaryOldRoutes : (elementaryPolygonData n w d).OldRoutes (elementaryRoot n w)
  | .inl v => elementaryCoreRoutes n w d v
  | .inr a => (elementaryCoreRoutes n w d (macroVertex n w a (MacroGraph.point 0))).trans
      ((elementaryPolygonData n w d).graphChain (.inr (a,MacroGraph.point 0),true)).pathClass.symm

@[simp] lemma elementaryOldRoutes_root :
    elementaryOldRoutes n w d (elementaryRoot n w) = .refl _ := rfl

abbrev ElementaryPiOne := RootedPaths.PiOne (K := elementarySimplicialComplex n w d)
  (elementaryBaseVertex n w d)
abbrev elementaryRootedVoltage := (elementaryPolygonData n w d).rootedVoltage
  (elementaryRoot n w) (elementaryOldRoutes n w d)

def elementaryPolygonToTopology : ElementaryPolygonGroup n w d →* ElementaryPiOne n w d :=
  (elementaryPolygonData n w d).polygonToTopology (elementaryRoot n w) (elementaryOldRoutes n w d)

lemma elementaryPolygonToTopology_value (e : ElementaryDart n w) :
    elementaryPolygonToTopology n w d (elementaryPolygonValue n w d e) =
      (elementaryPolygonData n w d).graphTransport (elementaryRootedVoltage n w d) e :=
  (elementaryPolygonData n w d).polygonToTopology_value (elementaryRoot n w) (elementaryOldRoutes n w d) e

def elementaryLetterToTopology : LetterPresentation.Group n w d →* ElementaryPiOne n w d :=
  (elementaryPolygonToTopology n w d).comp (elementaryComparison n w d)

lemma elementaryLetterToTopology_letter (a : Alphabet n) :
    elementaryLetterToTopology n w d (LetterPresentation.letter n w d a) =
      (elementaryPolygonData n w d).graphTransport (elementaryRootedVoltage n w d)
        (elementaryOld n w (letterDart n w a)) := by
  rw [elementaryLetterToTopology,MonoidHom.comp_apply,elementaryComparison_letter,
    elementaryPolygonToTopology_value]

lemma elementary_oldGauge_toTopology (v : Vertex n w) :
    elementaryPolygonToTopology n w d (oldGauge n w d v) = 1 := by
  rcases v with u|f
  · exact map_one _
  · rw [oldGauge,elementaryPolygonToTopology_value,Data.rooted_graphChain]
    apply MulOpposite.unop_injective
    change (((elementaryPolygonData n w d).graphChain (.inl (.inr ⟨f,fanBase f.val.1⟩),true)).pathClass.symm).trans
      (((elementaryPolygonData n w d).graphChain (.inl (.inr ⟨f,fanBase f.val.1⟩),true)).pathClass.trans (.refl _)) = .refl _
    simp

lemma elementary_gauge_toTopology (v : ElementaryVertex n w) :
    elementaryPolygonToTopology n w d (elementaryGauge n w d v) = 1 := by
  rcases v with v|a
  · exact elementary_oldGauge_toTopology n w d v
  · rw [elementaryGauge,map_mul]
    have hg : elementaryPolygonToTopology n w d (oldGauge n w d
        (macroVertex n w a (MacroGraph.point 0))) = 1 := by
      exact elementary_oldGauge_toTopology n w d _
    rw [hg,mul_one,elementaryPolygonToTopology_value,Data.rooted_graphChain]
    apply MulOpposite.unop_injective
    exact Data.based_eq_one_of_rev_route
      (elementaryCoreRoutes n w d (macroVertex n w a (MacroGraph.point 0)))
      ((elementaryPolygonData n w d).graphChain (.inr (a,MacroGraph.point 0),true)).pathClass

lemma elementaryLetterToTopology_surjective : Function.Surjective (elementaryLetterToTopology n w d) := by
  apply MonoidHom.range_eq_top.mp
  apply (elementaryPolygonData n w d).rooted_group_generated
    (elementaryRoot n w) (elementaryOldRoutes n w d)
  · intro e
    refine ⟨elementaryVoltage n w (letterVoltage n w d) e,?_⟩
    have he := congrArg (elementaryPolygonToTopology n w d) (elementary_gauge n w d e)
    rw [elementaryPolygonToTopology_value,map_mul,map_mul,map_inv,
      elementary_gauge_toTopology,elementary_gauge_toTopology,one_mul,inv_one,mul_one] at he
    exact he.symm
  · rfl

end

/-! Injectivity of the actual pi1 comparison, detected by the genuine
voltage covering. -/

open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
local instance : DecidableEq (ElementaryVertex n w) := Classical.decEq _
local instance : DecidableEq (ElementaryEdge n w) := Classical.decEq _
local instance : DecidableEq (ElementaryCell n w d) := Classical.decEq _
local instance : TopologicalSpace (LetterPresentation.Group n w d) := ⊥
local instance : DiscreteTopology (LetterPresentation.Group n w d) := ⟨rfl⟩

lemma elementarySignedVoltage (e : ElementaryDart n w) :
    Data.signed (fun e => elementaryVoltage n w (letterVoltage n w d) (e,true)) e =
      elementaryVoltage n w (letterVoltage n w d) e := by
  rcases e with ⟨e,b⟩
  cases b
  · exact (elementaryVoltage_rev n w (letterVoltage n w d)
      (letterVoltage_rev n w d) (e,true)).symm
  · rfl

def elementarySourceVoltage : Voltage (elementarySimplicialComplex n w d) (LetterPresentation.Group n w d) :=
  (elementaryPolygonData n w d).voltage
    (fun e => elementaryVoltage n w (letterVoltage n w d) (e,true)) (by
      intro c
      simpa only [elementarySignedVoltage, elementaryPolygonData] using elementaryLetterVoltage_cell n w d c)

def elementaryTopologyToLetter : ElementaryPiOne n w d →* LetterPresentation.Group n w d :=
  (elementarySourceVoltage n w d).detect (elementaryBaseVertex n w d)

lemma elementaryLetterToTopology_loop (i : Fin (n+1)) :
    elementaryLetterToTopology n w d (LetterPresentation.letter n w d (i,true)) =
      MulOpposite.op ((elementaryPolygonData n w d).graphChain
        (elementaryOld n w (letterDart n w (i,true)))).pathClass := by
  rw [elementaryLetterToTopology_letter,Data.rooted_graphChain]
  exact RootedPaths.based_loop _ _ rfl _

lemma elementaryTopologyToLetter_letter (i : Fin (n+1)) :
    elementaryTopologyToLetter n w d
      (elementaryLetterToTopology n w d (LetterPresentation.letter n w d (i,true))) =
        LetterPresentation.letter n w d (i,true) := by
  rw [elementaryLetterToTopology_loop]
  change (elementarySourceVoltage n w d).detect _ (MulOpposite.op _) = _
  refine (Voltage.detect_chain (elementarySourceVoltage n w d) (elementaryBaseVertex n w d)
    ((elementaryPolygonData n w d).graphChain (elementaryOld n w (letterDart n w (i,true))))).trans ?_
  refine (Data.graphChain_eval (elementaryPolygonData n w d) (elementarySourceVoltage n w d)
    (elementaryOld n w (letterDart n w (i,true)))).trans ?_
  change (elementaryPolygonData n w d).graphTransport ((elementaryPolygonData n w d).voltage _ _) _ = _
  rw [Data.graphTransport_voltage,elementarySignedVoltage]
  exact letterVoltage_letter n w d (i,true)

lemma elementaryTopology_leftInverse :
    (elementaryTopologyToLetter n w d).comp (elementaryLetterToTopology n w d) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  exact elementaryTopologyToLetter_letter n w d i

lemma elementaryLetterToTopology_injective : Function.Injective (elementaryLetterToTopology n w d) := by
  apply Function.LeftInverse.injective (f := elementaryLetterToTopology n w d)
    (g := elementaryTopologyToLetter n w d)
  intro x
  exact DFunLike.congr_fun (elementaryTopology_leftInverse n w d) x

/-- The actual letter group equals the actual topological pi1-op of the finite
literal elementary polygon realization. -/
def elementaryTopologyEquiv : LetterPresentation.Group n w d ≃* ElementaryPiOne n w d :=
  MulEquiv.ofBijective (elementaryLetterToTopology n w d)
    ⟨elementaryLetterToTopology_injective n w d,elementaryLetterToTopology_surjective n w d⟩

end ConeSkeleton

section

/-! The arbitrary obstruction cochain on the literal collar triangles of the
SAME chosen arrays extends to their literal directed lifted edges. -/

namespace FinitePolygonModel.Data
lemma map_edgeChain {E G B : Type*} [Group G] [AddCommGroup B]
    (v : E → G) (F : ((G × E) →₀ ℤ) →ₗ[ℤ] B) (g : G) (e : E × Bool) :
    F (IntegralIncidence.edgeChain (signed v) (g,e)) =
      signedCochain v (fun x => F (Finsupp.single x 1)) g e := by
  rcases e with ⟨e,b⟩
  cases b <;> simp [IntegralIncidence.edgeChain,signed,signedCochain]
end FinitePolygonModel.Data
namespace IncidenceTemplate
open CoreGeometry LetterPresentation ConeSkeleton FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (m : ℕ) (B : Type) [AddCommGroup B]
local instance : DecidableEq (ElementaryVertex (finalSize m) (finalMaster m)) := Classical.decEq _
local instance : DecidableEq (ElementaryEdge (finalSize m) (finalMaster m)) := Classical.decEq _
local instance : DecidableEq (ElementaryCell (finalSize m) (finalMaster m) (finalSix m)) := Classical.decEq _
variable (T : (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) → Data.Position (elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)) → Fin 3 → B)

def finalTrianglePolygonWeight (x : (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) × ElementaryCell (finalSize m) (finalMaster m) (finalSix m)) : B :=
  ∑ i : Fin ((elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).size x.2), ∑ j : Fin 3,
    (elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).triangleWeight T (x.1 * (elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).cornerOffset (fun e => elementaryVoltage (finalSize m) (finalMaster m) (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) (e,true)) ⟨x.2,(i,j)⟩) ⟨x.2,(i,j)⟩

def finalTriangleEdgeWeight (x : (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) × ElementaryEdge (finalSize m) (finalMaster m)) : B :=
  IndexedFilling.leftInverse (elementaryEncodedBoundary (finalSize m) (finalMaster m) (finalSix m))
    (finalTrianglePolygonWeight m B T) (Finsupp.single x 1)

lemma finalTriangleEdgeWeight_equation (g : (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m))) (c : ElementaryCell (finalSize m) (finalMaster m) (finalSix m)) :
    (∑ i : Fin ((elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).size c), Data.signedCochain (fun e => elementaryVoltage (finalSize m) (finalMaster m) (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) (e,true)) (finalTriangleEdgeWeight m B T)
      (g * ((List.ofFn (fun i => Data.signed (fun e => elementaryVoltage (finalSize m) (finalMaster m) (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) (e,true)) ((elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).side c i))).take i.val).prod) ((elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).side c i)) =
    ∑ i : Fin ((elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).size c), ∑ j : Fin 3,
      (elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).triangleWeight T (g * (elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).cornerOffset (fun e => elementaryVoltage (finalSize m) (finalMaster m) (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) (e,true)) ⟨c,(i,j)⟩) ⟨c,(i,j)⟩ := by
  have hh := finalDiagramStage_extend_cochain m B (finalTrianglePolygonWeight m B T) (g,c)
  rw [elementaryEncoded_cellBoundary] at hh
  have hv : elementaryVoltage (finalSize m) (finalMaster m)
      (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) = Data.signed
      (fun e => elementaryVoltage (finalSize m) (finalMaster m)
        (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) (e,true)) := by
    funext e; exact (elementarySignedVoltage _ _ _ e).symm
  rw [hv] at hh
  simp only [IntegralIncidence.Polygons.faceBoundary,map_sum,
    IntegralIncidence.Polygons.liftedSide,IntegralIncidence.Polygons.offset,Data.map_edgeChain] at hh
  exact hh

end IncidenceTemplate
end

section

/-! The converse monodromy criterion, for an actual covering map. This does
not assume a universal cover: it proves path connectivity and simple
connectivity from bijectivity of the monodromy action on one fiber. -/

open Set Function

lemma simplyConnected_of_fundamentalGroup_subsingleton {E : Type*} [TopologicalSpace E]
    [PathConnectedSpace E] (e₀ : E) [Subsingleton (FundamentalGroup E e₀)] :
    SimplyConnectedSpace E := by
  apply simply_connected_iff_paths_homotopic.mpr
  refine ⟨inferInstance,fun x y => ⟨fun p q => ?_⟩⟩
  let a : Path.Homotopic.Quotient e₀ x := .mk (PathConnectedSpace.somePath e₀ x)
  let b : Path.Homotopic.Quotient e₀ y := .mk (PathConnectedSpace.somePath e₀ y)
  have he : a.trans (p.trans b.symm) = a.trans (q.trans b.symm) :=
    Subsingleton.elim (α := FundamentalGroup E e₀) _ _
  have := congrArg (fun r : Path.Homotopic.Quotient e₀ e₀ => a.symm.trans (r.trans b)) he
  simp only [Path.Homotopic.Quotient.trans_assoc
    ] at this
  simpa only [← Path.Homotopic.Quotient.trans_assoc,Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans,Path.Homotopic.Quotient.trans_refl] using this

namespace Covering
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (cov : IsCoveringMap p) (e₀ : E)

lemma pathConnected_of_monodromy_surjective [PathConnectedSpace X]
    (hs : Surjective (fun γ : FundamentalGroup X (p e₀) => cov.monodromy γ ⟨e₀,rfl⟩)) :
    PathConnectedSpace E := by
  have joined₀ (e : E) : Joined e₀ e := by
    let γ : Path.Homotopic.Quotient (p e₀) (p e) :=
      .mk (PathConnectedSpace.somePath _ _)
    obtain ⟨a,ha⟩ := (cov.monodromy_bijective γ).2 ⟨e,rfl⟩
    obtain ⟨r,hr⟩ := hs a
    let r' : Path.Homotopic.Quotient e₀ a.val :=
      (cov.liftPathQuotient r ⟨e₀,rfl⟩).cast rfl (congrArg Subtype.val hr).symm
    let γ' : Path.Homotopic.Quotient a.val e :=
      (cov.liftPathQuotient γ a).cast rfl (congrArg Subtype.val ha).symm
    exact ⟨(r'.trans γ').out⟩
  exact ⟨⟨e₀⟩,fun e f => (joined₀ e).symm.trans (joined₀ f)⟩

lemma fundamentalGroup_subsingleton_of_monodromy_injective
    (hi : Injective (fun γ : FundamentalGroup X (p e₀) => cov.monodromy γ ⟨e₀,rfl⟩)) :
    Subsingleton (FundamentalGroup E e₀) := by
  refine ⟨fun r s => cov.injective_path_homotopic_map e₀ e₀ (hi ?_)⟩
  change cov.monodromy (Path.Homotopic.Quotient.map r ⟨p,cov.continuous⟩) ⟨e₀,rfl⟩ =
    cov.monodromy (Path.Homotopic.Quotient.map s ⟨p,cov.continuous⟩) ⟨e₀,rfl⟩
  exact (cov.monodromy_map r).trans (cov.monodromy_map s).symm

lemma simplyConnected_of_monodromy_bijective [PathConnectedSpace X]
    (h : Bijective (fun γ : FundamentalGroup X (p e₀) => cov.monodromy γ ⟨e₀,rfl⟩)) :
    SimplyConnectedSpace E := by
  let := pathConnected_of_monodromy_surjective cov e₀ h.2
  let := fundamentalGroup_subsingleton_of_monodromy_injective cov e₀ h.1
  exact simplyConnected_of_fundamentalGroup_subsingleton e₀

end Covering
end

/-! The actual voltage cover is universal whenever its proved monodromy
comparison is bijective. No simple-connectivity premise on the total space
is substituted for the producer. -/

namespace FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

lemma monodromy_bijective_of_detect (o : V) (h : Function.Bijective (v.detect o)) :
    Function.Bijective (fun γ : FundamentalGroup (Carrier K) (vertex K o) =>
      v.isCoveringMap.monodromy γ (v.vertexFiber o 1)) := by
  constructor
  · intro r s hrs
    apply MulOpposite.op_injective
    apply h.1
    apply (v.detect_eq_iff o (MulOpposite.op r) (v.detect o (MulOpposite.op s))).mpr
    exact ((v.detect_eq_iff o (MulOpposite.op s) _).mp rfl).trans (congrArg Subtype.val hrs).symm
  · intro e
    obtain ⟨g,hg⟩ := (v.same_fiber_iff_orbit e.val (v.vertexFiber o 1).val).mp e.property
    obtain ⟨r,hr⟩ := h.2 g
    refine ⟨r.unop,Subtype.ext ?_⟩
    exact ((v.detect_eq_iff o r g).mp hr).symm.trans hg

lemma simplyConnected_of_detect [PathConnectedSpace (Carrier K)] (o : V)
    (h : Function.Bijective (v.detect o)) : SimplyConnectedSpace v.TotalSpace := by
  apply Covering.simplyConnected_of_monodromy_bijective v.isCoveringMap (v.vertexFiber o 1).val
  exact v.monodromy_bijective_of_detect o h

end FinitePolyhedron.Voltage

/-! The literal voltage bundle is an actual simply connected covering
of the actual finite polygon realization. We construct its connectivity from
monodromy, rather than naming an abstract universal cover as a hypothesis. -/

namespace ConeSkeleton
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
local instance : DecidableEq (ElementaryVertex n w) := Classical.decEq _
local instance : DecidableEq (ElementaryEdge n w) := Classical.decEq _
local instance : DecidableEq (ElementaryCell n w d) := Classical.decEq _
local instance : TopologicalSpace (LetterPresentation.Group n w d) := ⊥
local instance : DiscreteTopology (LetterPresentation.Group n w d) := ⟨rfl⟩

lemma elementaryTopologyToLetter_bijective :
    Function.Bijective (elementaryTopologyToLetter n w d) := by
  have left : Function.LeftInverse (elementaryTopologyToLetter n w d)
      (elementaryLetterToTopology n w d) := fun x =>
    DFunLike.congr_fun (elementaryTopology_leftInverse n w d) x
  have right : Function.RightInverse (elementaryTopologyToLetter n w d)
      (elementaryLetterToTopology n w d) := by
    intro x
    obtain ⟨g,rfl⟩ := elementaryLetterToTopology_surjective n w d x
    rw [left]
  exact ⟨right.injective,left.surjective⟩

instance elementarySourceUniversalCover_simplyConnected :
    SimplyConnectedSpace (elementarySourceVoltage n w d).TotalSpace := by
  apply Voltage.simplyConnected_of_detect (elementarySourceVoltage n w d)
    (elementaryBaseVertex n w d)
  exact elementaryTopologyToLetter_bijective n w d

end ConeSkeleton

section

/-! Actual higher homotopy transport across actual topological covering maps.
The connected cube boundary is constructed explicitly; it is not a lifting
or cellular approximation hypothesis. -/
open scoped Topology unitInterval
namespace HigherCovering

variable {N : Type*}

local instance : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
local instance : LocallyPathConnectedSpace I :=
  (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace

instance cube_contractible (N : Type*) : ContractibleSpace (N → I) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit I
  exact (ContinuousMap.HomotopyEquiv.piCongrRight (fun _ : N => e)).contractibleSpace

/-- A path in a single face of the cube boundary. -/
def facePath [DecidableEq N] (x y : Cube.boundary N) (i : N) (a : I)
    (ha : a = 0 ∨ a = 1) (hx : x.val i = a) (hy : y.val i = a) : Path x y where
  toFun t := ⟨fun j => if j = i then a else PathConnectedSpace.somePath (x.val j) (y.val j) t,
    ⟨i, by simpa using ha⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    split_ifs
    · exact continuous_const
    · exact Path.continuous _
  source' := by
    apply Subtype.ext
    funext j
    by_cases h : j = i
    · subst j; simpa using hx.symm
    · simp [h]
  target' := by
    apply Subtype.ext
    funext j
    by_cases h : j = i
    · subst j; simpa using hy.symm
    · simp [h]

instance boundary_pathConnected [DecidableEq N] [Nontrivial N] :
    PathConnectedSpace (Cube.boundary N) := by
  let z : Cube.boundary N := ⟨fun _ => 0, ⟨Classical.arbitrary N, Or.inl rfl⟩⟩
  have hz (x : Cube.boundary N) : Joined x z := by
    obtain ⟨i, hi⟩ := x.property
    obtain ⟨j, hj⟩ := exists_ne i
    let y : Cube.boundary N := ⟨Function.update (fun _ : N => (0 : I)) i (x.val i),
      ⟨i, by simpa using hi⟩⟩
    exact ⟨(facePath x y i (x.val i) hi rfl (by simp [y])).trans
      (facePath y z j 0 (Or.inl rfl) (by simp [y,hj]) rfl)⟩
  exact ⟨⟨z⟩, fun x y => (hz x).trans (hz y).symm⟩

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- Postcomposition of actual cube-relative loops. -/
def loopMap (f : C(E,X)) {e : E} (a : GenLoop N E e) : GenLoop N X (f e) :=
  ⟨f.comp a.val, fun y hy => by simp [a.property y hy]⟩

lemma loopMap_homotopic (f : C(E,X)) {e : E} {a b : GenLoop N E e}
    (h : GenLoop.Homotopic a b) : GenLoop.Homotopic (loopMap f a) (loopMap f b) :=
  h.comp_continuousMap f

/-- The actual induced map on the cube-relative homotopy quotient. -/
def homotopyMap (N : Type*) (f : C(E,X)) (e : E) :
    HomotopyGroup N E e → HomotopyGroup N X (f e) :=
  Quotient.map (loopMap f) (fun _ _ h => loopMap_homotopic f h)

variable {p : E → X} (cov : IsCoveringMap p) (e : E)

lemma homotopyMap_injective [Nonempty N] :
    Function.Injective (homotopyMap N ⟨p,cov.continuous⟩ e) := by
  apply Quotient.ind₂
  intro a b h
  apply Quotient.sound
  apply (cov.homotopicRel_iff_comp ?_).mpr
  · exact Quotient.exact h
  · refine ⟨fun _ => 0, ⟨Classical.arbitrary N, Or.inl rfl⟩, ?_⟩
    exact (a.property _ ⟨Classical.arbitrary N, Or.inl rfl⟩).trans
      (b.property _ ⟨Classical.arbitrary N, Or.inl rfl⟩).symm

lemma loopMap_surjective [DecidableEq N] [Nontrivial N] :
    Function.Surjective (loopMap (N := N) ⟨p,cov.continuous⟩ (e := e)) := by
  intro a
  let z : N → I := fun _ => 0
  have hz : z ∈ Cube.boundary N := ⟨Classical.arbitrary N, Or.inl rfl⟩
  obtain ⟨F, ⟨Fz,Flift⟩, _⟩ := cov.existsUnique_continuousMap_lifts a.val z e
    (a.property z hz).symm
  have hb (y : N → I) (hy : y ∈ Cube.boundary N) : F y = e := by
    have hc : Continuous (fun q : Cube.boundary N => F q.val) :=
      F.continuous.comp continuous_subtype_val
    have he (q q' : Cube.boundary N) : p (F q.val) = p (F q'.val) := by
      change (p ∘ F) q.val = (p ∘ F) q'.val
      rw [Flift, a.property _ q.property, a.property _ q'.property]
    exact (cov.const_of_comp hc he ⟨y,hy⟩ ⟨z,hz⟩).trans Fz
  refine ⟨⟨F,hb⟩, ?_⟩
  apply GenLoop.ext
  intro y
  exact congrFun Flift y

lemma homotopyMap_surjective [DecidableEq N] [Nontrivial N] :
    Function.Surjective (homotopyMap N ⟨p,cov.continuous⟩ e) := by
  intro a
  induction a using Quotient.ind with
  | _ a =>
    obtain ⟨b,rfl⟩ := loopMap_surjective cov e a
    exact ⟨Quotient.mk _ b,rfl⟩

/-- Coverings preserve the genuine higher homotopy sets/groups. -/
def homotopyEquiv [DecidableEq N] [Nontrivial N] :
    HomotopyGroup N E e ≃ HomotopyGroup N X (p e) :=
  Equiv.ofBijective (homotopyMap N ⟨p,cov.continuous⟩ e)
    ⟨homotopyMap_injective cov e,homotopyMap_surjective cov e⟩

include cov in
lemma subsingleton_higher_iff (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n+2) E e) ↔
      Subsingleton (HomotopyGroup.Pi (n+2) X (p e)) :=
  (homotopyEquiv (N := Fin (n+2)) cov e).subsingleton_congr

end HigherCovering
end

/-! Exact higher homotopy identification for the constructed simply connected
voltage covering of the actual frozen finite polyhedron. -/

namespace ConeSkeleton
attribute [local instance] Classical.propDecidable
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
local instance : DecidableEq (ElementaryVertex n w) := Classical.decEq _
local instance : DecidableEq (ElementaryEdge n w) := Classical.decEq _
local instance : DecidableEq (ElementaryCell n w d) := Classical.decEq _
local instance : TopologicalSpace (LetterPresentation.Group n w d) := ⊥
local instance : DiscreteTopology (LetterPresentation.Group n w d) := ⟨rfl⟩

abbrev elementaryUniversalBasepoint : (elementarySourceVoltage n w d).TotalSpace :=
  ((elementarySourceVoltage n w d).vertexFiber (elementaryBaseVertex n w d) 1).val

/-- This is the literal cover already proved simply connected, not an abstract
cover named in a premise. -/
def elementaryHigherCoverEquiv (k : ℕ) :
    HomotopyGroup.Pi (k+2) (elementarySourceVoltage n w d).TotalSpace
      (elementaryUniversalBasepoint n w d) ≃
    HomotopyGroup.Pi (k+2) (elementaryFiniteComplex n w d).Carrier
      (elementaryFiniteBasepoint n w d) :=
  HigherCovering.homotopyEquiv
    ((elementarySourceVoltage n w d).isCoveringMap.homeomorph_comp
      (elementaryFiniteHomeomorph n w d)) (elementaryUniversalBasepoint n w d)

lemma elementaryAspherical_iff :
    (elementaryFiniteComplex n w d).Aspherical (elementaryFiniteBasepoint n w d) ↔
      ∀ k : ℕ, Subsingleton (HomotopyGroup.Pi (k+2)
        (elementarySourceVoltage n w d).TotalSpace (elementaryUniversalBasepoint n w d)) := by
  constructor <;> intro h k
  · exact (elementaryHigherCoverEquiv n w d k).subsingleton_congr.mpr (h k)
  · exact (elementaryHigherCoverEquiv n w d k).subsingleton_congr.mp (h k)

end ConeSkeleton

section

/-! A literal basepoint-fixing contraction kills the actual cube-relative
homotopy groups, with no Hurewicz/Whitehead assumption. -/
open scoped Topology unitInterval
namespace BasedHigherContraction
variable {X : Type*} [TopologicalSpace X] (z : X) (H : C(I × X,X))
  (h0 : ∀ x, H (0,x) = x) (h1 : ∀ x, H (1,x) = z) (hz : ∀ t, H (t,z) = z)
  {N : Type*}

def nullhomotopy (p : GenLoop N X z) :
    p.val.HomotopyRel (GenLoop.const : GenLoop N X z).val (Cube.boundary N) where
  toFun tx := H (tx.1,p tx.2)
  continuous_toFun := H.continuous.comp (continuous_fst.prodMk (p.val.continuous.comp continuous_snd))
  map_zero_left x := h0 (p x)
  map_one_left x := h1 (p x)
  prop' t x hx := by
    change H (t,p x) = p x
    have hp : p x = z := p.property x hx
    rw [hp,hz]

include h0 h1 hz in
lemma subsingleton : Subsingleton (HomotopyGroup N X z) := by
  refine ⟨?_⟩
  intro a b
  induction a using Quotient.ind with | _ a =>
  induction b using Quotient.ind with | _ b =>
  apply Quotient.sound
  exact ⟨(nullhomotopy z H h0 h1 hz a).trans (nullhomotopy z H h0 h1 hz b).symm⟩

end BasedHigherContraction
end

section

/-! Literal area-counted edge-disk calculus on the frozen finite-complex
model. All path algebra below uses only the challenge's stutters and spurs. -/
namespace FiniteComplex
variable (K : FiniteComplex)
namespace DiskHomotopy
variable {K}
lemma contextual {p q : List K.Vertex} {n : ℕ} (h : K.DiskHomotopy p q n)
    (l r : List K.Vertex) : K.DiskHomotopy (l++p++r) (l++q++r) n := by
  induction h with
  | refl => exact .refl _
  | move h =>
    apply DiskHomotopy.move
    cases h with
    | stutter l' r' a => simpa only [List.append_assoc] using DiskMove.stutter (l++l') (r'++r) a
    | spur l' r' a b h => simpa only [List.append_assoc] using DiskMove.spur (l++l') (r'++r) a b h
    | triangle l' r' a b c h hn =>
      simpa only [List.append_assoc] using DiskMove.triangle (l++l') (r'++r) a b c h hn
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'

lemma append_both {p q r s : List K.Vertex} {m n : ℕ}
    (h : K.DiskHomotopy p q m) (h' : K.DiskHomotopy r s n) :
    K.DiskHomotopy (p++r) (q++s) (m+n) := by
  have h₁ : K.DiskHomotopy (p++r) (q++r) m := by simpa using h.contextual [] r
  have h₂ : K.DiskHomotopy (q++r) (q++s) n := by simpa using h'.contextual q []
  exact h₁.trans h₂

lemma reverse {p q : List K.Vertex} {n : ℕ} (h : K.DiskHomotopy p q n) :
    K.DiskHomotopy p.reverse q.reverse n := by
  induction h with
  | refl => exact .refl _
  | move h =>
    cases h with
    | stutter l r a =>
      simpa [List.reverse_append,List.append_assoc] using
        (DiskHomotopy.move (DiskMove.stutter r.reverse l.reverse a))
    | spur l r a b h =>
      simpa [List.reverse_append,List.append_assoc] using
        (DiskHomotopy.move (DiskMove.spur r.reverse l.reverse a b h))
    | triangle l r a b c h hn =>
      have he : ({c,b,a} : Finset K.Vertex) = {a,b,c} := by ext; simp; tauto
      simpa [List.reverse_append,List.append_assoc] using
        (DiskHomotopy.move (DiskMove.triangle r.reverse l.reverse c b a (he.symm ▸ h) (he.symm ▸ hn)))
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
end DiskHomotopy

abbrev Chain := FinitePolyhedron.EdgeChain K.complex
end FiniteComplex
namespace FinitePolyhedron.EdgeChain
open HyperbolicObstruction.FiniteComplex
variable {K : FiniteComplex}
def nodes {a b : K.Vertex} : K.Chain a b → List K.Vertex
  | .nil a => [a]
  | .cons (a := a) _ p => a :: p.nodes

def starts {a b : K.Vertex} : K.Chain a b → List K.Vertex
  | .nil _ => []
  | .cons (a := a) _ p => a :: p.starts

def steps {a b : K.Vertex} : K.Chain a b → List K.Vertex
  | .nil _ => []
  | .cons (b := b) _ p => b :: p.steps

lemma nodes_eq_starts {a b : K.Vertex} (p : K.Chain a b) : p.nodes = p.starts ++ [b] := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [nodes,starts,ih,List.cons_append]

lemma nodes_eq_steps {a b : K.Vertex} (p : K.Chain a b) : p.nodes = a :: p.steps := by
  induction p with
  | nil => rfl
  | cons h p ih => change _ :: p.nodes = _ :: _ :: p.steps; rw [ih]

@[simp] lemma nodes_append {a b c : K.Vertex} (p : K.Chain a b) (q : K.Chain b c) :
    (p.append q).nodes = p.starts ++ q.nodes := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [FinitePolyhedron.EdgeChain.append,nodes,starts,ih,List.cons_append]

lemma nodes_append' {a b c : K.Vertex} (p : K.Chain a b) (q : K.Chain b c) :
    (p.append q).nodes = p.nodes ++ q.steps := by
  rw [nodes_append,nodes_eq_starts p,nodes_eq_steps q,List.append_assoc]
  rfl

@[simp] lemma append_nil {a b : K.Vertex} (p : K.Chain a b) : p.append (.nil b) = p := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [FinitePolyhedron.EdgeChain.append,ih]

lemma append_assoc {a b c d : K.Vertex} (p : K.Chain a b) (q : K.Chain b c) (r : K.Chain c d) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [FinitePolyhedron.EdgeChain.append,ih]

def single {a b : K.Vertex} (h : K.Edge a b) : K.Chain a b := .cons h (.nil b)

def reverse {a b : K.Vertex} : K.Chain a b → K.Chain b a
  | .nil a => .nil a
  | .cons h p => p.reverse.append (single (by simpa only [Edge,Finset.pair_comm] using h))

lemma nodes_reverse {a b : K.Vertex} (p : K.Chain a b) : p.reverse.nodes = p.nodes.reverse := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [reverse,nodes_append',ih]
    simp only [single,steps,nodes,List.reverse_cons]

lemma nodes_injective {a b : K.Vertex} : Function.Injective (nodes (K := K) (a := a) (b := b)) := by
  intro p
  induction p with
  | nil a =>
    intro q h
    cases q with
    | nil => rfl
    | cons he q =>
      have hh := congrArg List.length h
      simp only [nodes] at hh
      rw [nodes_eq_steps q] at hh
      simp only [List.length_cons,List.length_nil] at hh
      omega
  | @cons a c b he p ih =>
    intro q h
    cases q with
    | nil =>
      have hh := congrArg List.length h
      simp only [nodes] at hh
      rw [nodes_eq_steps p] at hh
      simp only [List.length_cons,List.length_nil] at hh
      omega
    | @cons _ d _ hf q =>
      have h' := List.cons.inj h
      have hd : c = d := by
        have hh := h'.2
        rw [nodes_eq_steps p,nodes_eq_steps q] at hh
        exact (List.cons.inj hh).1
      subst d
      exact congrArg (FinitePolyhedron.EdgeChain.cons he) (ih h'.2)

@[simp] lemma reverse_reverse {a b : K.Vertex} (p : K.Chain a b) : p.reverse.reverse = p := by
  apply nodes_injective
  simp only [nodes_reverse,List.reverse_reverse]

lemma reverse_append {a b c : K.Vertex} (p : K.Chain a b) (q : K.Chain b c) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  apply nodes_injective
  rw [nodes_reverse,nodes_append',List.reverse_append,nodes_append,nodes_reverse]
  have hq : q.steps.reverse = q.reverse.starts := by
    have h := nodes_reverse q
    rw [nodes_eq_starts q.reverse,nodes_eq_steps q,List.reverse_cons] at h
    exact List.append_cancel_right h |>.symm
  rw [hq]

abbrev Homotopy {a b : K.Vertex} (p q : K.Chain a b) (n : ℕ) : Prop := K.DiskHomotopy p.nodes q.nodes n
namespace Homotopy
variable {a b c : K.Vertex} {p q : K.Chain a b} {n : ℕ}
lemma refl (p : K.Chain a b) : p.Homotopy p 0 := DiskHomotopy.refl _
lemma symm (h : p.Homotopy q n) : q.Homotopy p n := DiskHomotopy.symm h
lemma trans {r : K.Chain a b} {m : ℕ} (h : p.Homotopy q n) (h' : q.Homotopy r m) :
    p.Homotopy r (n+m) := DiskHomotopy.trans h h'
lemma trans_zero {r : K.Chain a b} (h : p.Homotopy q n) (h' : q.Homotopy r 0) :
    p.Homotopy r n := by simpa using h.trans h'
lemma zero_trans {r : K.Chain a b} (h : p.Homotopy q 0) (h' : q.Homotopy r n) :
    p.Homotopy r n := by simpa using h.trans h'
lemma append_right (h : p.Homotopy q n) (r : K.Chain b c) :
    (p.append r).Homotopy (q.append r) n := by
  unfold Homotopy
  simpa only [nodes_append',List.nil_append] using h.contextual [] r.steps
lemma append_left (h : p.Homotopy q n) {c : K.Vertex} (r : K.Chain c a) :
    (r.append p).Homotopy (r.append q) n := by
  unfold Homotopy
  simpa only [nodes_append,List.append_nil] using h.contextual r.starts []
lemma reverse (h : p.Homotopy q n) : p.reverse.Homotopy q.reverse n := by
  unfold Homotopy
  simpa only [nodes_reverse] using DiskHomotopy.reverse h
end Homotopy

lemma cancel {a b : K.Vertex} (p : K.Chain a b) :
    (p.append p.reverse).Homotopy (.nil a) 0 := by
  induction p with
  | nil a => exact .refl _
  | @cons a b c he p ih =>
    have hre : K.Edge b a := by simpa only [Edge,Finset.pair_comm] using he
    have h := (ih.append_right (single hre)).append_left (single he)
    have hh : ((single he).append (single hre)).Homotopy (.nil a) 0 := by
      change K.DiskHomotopy [a,b,a] [a] 0
      exact DiskHomotopy.move (by simpa only [List.nil_append,List.append_nil] using DiskMove.spur (K := K) [] [] a b he)
    apply Homotopy.zero_trans ?_ hh
    simpa only [single,FinitePolyhedron.EdgeChain.append,reverse,append_assoc] using h

lemma cancel_left {a b : K.Vertex} (p : K.Chain a b) :
    (p.reverse.append p).Homotopy (.nil b) 0 := by simpa only [reverse_reverse] using cancel p.reverse

end FinitePolyhedron.EdgeChain
end

/-! Rooted path algebra with exact zero-cost spur cancellations. This is a
literal triangular disk calculus, not an appeal to topological equivalence. -/
namespace FinitePolyhedron.EdgeChain
open HyperbolicObstruction.FiniteComplex
variable {K : FiniteComplex}

lemma single_self (a : K.Vertex) :
    (single (FinitePolyhedron.edge_self K.complex a)).Homotopy (.nil a) 0 := by
  change K.DiskHomotopy [a,a] [a] 0
  exact DiskHomotopy.move (by simpa using DiskMove.stutter (K := K) [] [] a)

lemma triangle {a b c : K.Vertex} (h : {a,b,c} ∈ K.complex.faces)
    (hab : K.Edge a b) (hbc : K.Edge b c) (hac : K.Edge a c) :
    ∃ k ≤ 1, ((single hab).append (single hbc)).Homotopy (single hac) k := by
  change ∃ k ≤ 1, K.DiskHomotopy [a,b,c] [a,c] k
  by_cases hab' : a = b
  · subst b
    exact ⟨0,by omega,DiskHomotopy.move (by simpa using DiskMove.stutter (K := K) [] [c] a)⟩
  by_cases hbc' : b = c
  · subst c
    exact ⟨0,by omega,DiskHomotopy.move (by simpa using DiskMove.stutter (K := K) [a] [] b)⟩
  by_cases hac' : a = c
  · subst c
    have hh : K.DiskHomotopy [a,b,a] [a] 0 := DiskHomotopy.move (by simpa using DiskMove.spur (K := K) [] [] a b hab)
    have ht : K.DiskHomotopy [a,a] [a] 0 := DiskHomotopy.move (by simpa using DiskMove.stutter (K := K) [] [] a)
    exact ⟨0,by omega,by simpa using hh.trans ht.symm⟩
  · exact ⟨1,le_rfl,DiskHomotopy.move (by simpa using DiskMove.triangle (K := K) [] [] a b c h (by simp [hab',hbc',hac']))⟩

variable (o : K.Vertex) (R : ∀ a, K.Chain o a)
def based {a b : K.Vertex} (p : K.Chain a b) : K.Chain o o :=
  (R a).append (p.append (R b).reverse)

lemma based_nil (a : K.Vertex) : (based o R (.nil a)).Homotopy (.nil o) 0 := cancel (R a)

lemma based_append {a b c : K.Vertex} (p : K.Chain a b) (q : K.Chain b c) :
    ((based o R p).append (based o R q)).Homotopy (based o R (p.append q)) 0 := by
  have h := ((cancel_left (R b)).append_right (q.append (R c).reverse)).append_left ((R a).append p)
  simpa only [based,append_assoc,append] using h

lemma based_reverse {a b : K.Vertex} (p : K.Chain a b) :
    based o R p.reverse = (based o R p).reverse := by
  simp only [based,reverse_append,reverse_reverse,append_assoc]

lemma based_homotopy {a b : K.Vertex} {p q : K.Chain a b} {k : ℕ} (h : p.Homotopy q k) :
    (based o R p).Homotopy (based o R q) k :=
  (h.append_right (R b).reverse).append_left (R a)

lemma based_route (hR : R o = .nil o) (a : K.Vertex) :
    (based o R (R a)).Homotopy (.nil o) 0 := by
  simpa only [based,hR,append] using cancel (R a)

lemma unbase {a : K.Vertex} {p : K.Chain a a} {k : ℕ}
    (h : (based o R p).Homotopy (.nil o) k) : p.Homotopy (.nil a) k := by
  let r := R a
  have left : ((r.reverse.append r).append p).Homotopy p 0 := by
    simpa only [append] using (cancel_left r).append_right p
  have right : (p.append (r.reverse.append r)).Homotopy p 0 := by
    simpa only [append_nil] using (cancel_left r).append_left p
  have both : ((r.reverse.append r).append (p.append (r.reverse.append r))).Homotopy p 0 := by
    simpa only [append_assoc] using (left.append_right (r.reverse.append r)).trans_zero right
  have mid := (h.append_right r).append_left r.reverse
  have cancelR := cancel_left r
  have head : ((r.reverse.append (based o R p)).append r).Homotopy p 0 := by
    simpa only [based,append_assoc] using both
  have tail : ((r.reverse.append (.nil o)).append r).Homotopy (.nil a) 0 := by
    simpa only [append_nil] using cancelR
  have mid' : ((r.reverse.append (based o R p)).append r).Homotopy
      ((r.reverse.append (.nil o)).append r) k := by
    simpa only [append_assoc] using mid
  exact head.symm.zero_trans (mid'.trans_zero tail)

end FinitePolyhedron.EdgeChain

section

/-! A proved edge-and-triangle presentation of the actual fundamental group
of a finite barycentric realization. The rooted routes are actual edge paths;
no van Kampen theorem or fundamental-group comparison is postulated. -/

attribute [local instance] Classical.propDecidable
open Set
namespace FinitePolyhedron.EdgePresentation
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

abbrev Generator := {p : V × V // {p.1,p.2} ∈ K.faces}

def freeEval {a b : V} (p : EdgeChain K a b) : FreeGroup (Generator K) := by
  induction p with
  | nil _ => exact 1
  | @cons a b c h q ih => exact FreeGroup.of ⟨(a,b),h⟩ * ih

omit [Fintype V] in
@[simp] lemma freeEval_nil (a : V) : freeEval K (.nil a) = 1 := rfl
omit [Fintype V] in
@[simp] lemma freeEval_cons {a b c : V} (h : {a,b} ∈ K.faces) (q : EdgeChain K b c) :
    freeEval K (.cons h q) = FreeGroup.of ⟨(a,b),h⟩ * freeEval K q := rfl

variable (o : V) (R : ∀ a, EdgeChain K o a)

inductive Relation : FreeGroup (Generator K) → Prop
  | self (a : V) : Relation (FreeGroup.of ⟨(a,a),edge_self K a⟩)
  | triangle {a b c : V} (h : {a,b,c} ∈ K.faces)
      (hab : {a,b} ∈ K.faces) (hbc : {b,c} ∈ K.faces) (hac : {a,c} ∈ K.faces) :
      Relation (FreeGroup.of ⟨(a,b),hab⟩ * FreeGroup.of ⟨(b,c),hbc⟩ * (FreeGroup.of ⟨(a,c),hac⟩)⁻¹)
  | route (a : V) : Relation (freeEval K (R a))

abbrev PresentationGroup :=
  PresentedGroup (show Set (FreeGroup (Generator K)) from Relation K o R)

def gen {a b : V} (h : {a,b} ∈ K.faces) : PresentationGroup K o R :=
  PresentedGroup.of ⟨(a,b),h⟩

omit [Fintype V] in
lemma gen_self (a : V) : gen K o R (edge_self K a) = 1 :=
  PresentedGroup.one_of_mem (Relation.self a)

omit [Fintype V] in
lemma gen_triangle {a b c : V} (h : {a,b,c} ∈ K.faces)
    (hab : {a,b} ∈ K.faces) (hbc : {b,c} ∈ K.faces) (hac : {a,c} ∈ K.faces) :
    gen K o R hab * gen K o R hbc = gen K o R hac := by
  have hh := PresentedGroup.one_of_mem
    (rels := show Set (FreeGroup (Generator K)) from Relation K o R)
    (Relation.triangle (K := K) (o := o) (R := R) h hab hbc hac)
  rw [map_mul,map_mul,map_inv,mul_inv_eq_one] at hh
  exact hh

/-- The canonical cocycle of the finite edge presentation. -/
def voltage : Voltage K (PresentationGroup K o R) where
  value a b := if h : {a,b} ∈ K.faces then gen K o R h else 1
  self a := by rw [dite_eq_left (edge_self K a)]; exact gen_self K o R a
  triangle a b c h := by
    have hab := edge_of_subset K h (a := a) (b := b) (by simp) (by simp)
    have hbc := edge_of_subset K h (a := b) (b := c) (by simp) (by simp)
    have hac := edge_of_subset K h (a := a) (b := c) (by simp) (by simp)
    rw [dite_eq_left hab,dite_eq_left hbc,dite_eq_left hac]
    exact gen_triangle K o R h hab hbc hac

omit [Fintype V] in
lemma voltage_value {a b : V} (h : {a,b} ∈ K.faces) :
    (voltage K o R).value a b = gen K o R h := dite_eq_left h

omit [Fintype V] in
lemma eval_eq_mk {a b : V} (p : EdgeChain K a b) :
    Voltage.EdgeChain.eval (voltage K o R) p = PresentedGroup.mk (show Set (FreeGroup (Generator K)) from Relation K o R) (freeEval K p) := by
  induction p with
  | nil a => simp
  | cons h q ih => rw [Voltage.EdgeChain.eval_cons,voltage_value K o R h,ih,freeEval_cons,map_mul]; rfl

omit [Fintype V] in
lemma eval_route (a : V) : Voltage.EdgeChain.eval (voltage K o R) (R a) = 1 := by
  rw [eval_eq_mk]
  exact PresentedGroup.one_of_mem (Relation.route a)

abbrev routeClasses (a : V) := (R a).pathClass
abbrev topGenerator (s : Generator K) : RootedPaths.PiOne (K := K) o :=
  RootedPaths.edgeLoop o (routeClasses K o R) s.val.1 s.val.2

lemma lift_freeEval {a b : V} (p : EdgeChain K a b) :
    FreeGroup.lift (topGenerator K o R) (freeEval K p) =
      RootedPaths.based o (routeClasses K o R) p.pathClass := by
  induction p with
  | nil a => simpa using (RootedPaths.based_refl o (routeClasses K o R) a).symm
  | cons h q ih =>
    rw [freeEval_cons,map_mul,FreeGroup.lift_apply_of,ih,EdgeChain.pathClass_cons,
      RootedPaths.based_trans]
    congr 1
    exact RootedPaths.edgeLoop_of_edge o (routeClasses K o R) h

lemma relation_valid (hR : R o = .nil o) (r : FreeGroup (Generator K))
    (hr : Relation K o R r) : FreeGroup.lift (topGenerator K o R) r = 1 := by
  cases hr with
  | self a =>
    rw [FreeGroup.lift_apply_of]
    exact (RootedPaths.voltage o (routeClasses K o R)).self a
  | triangle h hab hbc hac =>
    rw [map_mul,map_mul,map_inv,FreeGroup.lift_apply_of,FreeGroup.lift_apply_of,FreeGroup.lift_apply_of,
      mul_inv_eq_one]
    exact (RootedPaths.voltage o (routeClasses K o R)).triangle _ _ _ h
  | route a =>
    rw [lift_freeEval]
    apply RootedPaths.based_route
    simp [routeClasses,hR]

/-- The presented edge group maps into the actual topological pi1. -/
def toTopology (hR : R o = .nil o) : PresentationGroup K o R →* RootedPaths.PiOne (K := K) o :=
  PresentedGroup.toGroup (relation_valid K o R hR)

@[simp] lemma toTopology_gen (hR : R o = .nil o) {a b : V} (h : {a,b} ∈ K.faces) :
    toTopology K o R hR (gen K o R h) = RootedPaths.edgeLoop o (routeClasses K o R) a b := by
  exact PresentedGroup.toGroup.of _

lemma toTopology_mk (hR : R o = .nil o) (z : FreeGroup (Generator K)) :
    toTopology K o R hR (PresentedGroup.mk (show Set (FreeGroup (Generator K)) from Relation K o R) z) =
      FreeGroup.lift (topGenerator K o R) z := rfl

lemma toTopology_chain (hR : R o = .nil o) {a b : V} (p : EdgeChain K a b) :
    toTopology K o R hR (PresentedGroup.mk (show Set (FreeGroup (Generator K)) from Relation K o R) (freeEval K p)) =
      RootedPaths.based o (routeClasses K o R) p.pathClass := by rw [toTopology_mk,lift_freeEval]

lemma toTopology_injective (hR : R o = .nil o) : Function.Injective (toTopology K o R hR) := by
  let : TopologicalSpace (PresentationGroup K o R) := ⊥
  let : DiscreteTopology (PresentationGroup K o R) := ⟨rfl⟩
  let f := (voltage K o R).detect o
  have hcomp : f.comp (toTopology K o R hR) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    rintro ⟨⟨a,b⟩,h⟩
    change (voltage K o R).detect o (toTopology K o R hR (gen K o R h)) = gen K o R h
    rw [toTopology_gen]
    exact ((voltage K o R).detect_edgeLoop o R (eval_route K o R) h).trans (voltage_value K o R h)
  have hl : Function.LeftInverse f (toTopology K o R hR) := fun x => DFunLike.congr_fun hcomp x
  exact hl.injective

lemma toTopology_surjective (hR : R o = .nil o) : Function.Surjective (toTopology K o R hR) := by
  intro y
  obtain ⟨p,hp⟩ := Quotient.exists_rep y.unop
  obtain ⟨c,hc⟩ := edgePath_representative K p
  refine ⟨PresentedGroup.mk (show Set (FreeGroup (Generator K)) from Relation K o R) (freeEval K c),?_⟩
  rw [toTopology_chain]
  have hRo : routeClasses K o R o = .refl _ := by simp [routeClasses,hR]
  rw [RootedPaths.based_loop o (routeClasses K o R) hRo]
  apply MulOpposite.unop_injective
  exact (Path.Homotopic.Quotient.eq.mpr hc).symm.trans hp

/-- A genuine isomorphism to the actual topological fundamental group. -/
def equivFundamentalGroup (hR : R o = .nil o) :
    PresentationGroup K o R ≃* RootedPaths.PiOne (K := K) o :=
  MulEquiv.ofBijective (toTopology K o R hR)
    ⟨toTopology_injective K o R hR,toTopology_surjective K o R hR⟩

/-- No route-existence hypothesis is needed for a connected realization. -/
def canonicalEquiv [PathConnectedSpace (Carrier K)] :
    PresentationGroup K o (edgeRoutes K o) ≃* RootedPaths.PiOne (K := K) o :=
  equivFundamentalGroup K o (edgeRoutes K o) (edgeRoutes_self K o)

end FinitePolyhedron.EdgePresentation
end

/-! Quantitative finite-presentation change, with all word substitutions and
comparison disks constructed. Relator disks are used only after establishing
that the corresponding literal words are null. -/
namespace WordPictures
variable {A B G : Type*} [Group G]

def signedWords (f : A → Word B) (a : A × Bool) : Word B :=
  if a.2 then f a.1 else FreeGroup.invRev (f a.1)

lemma signedWords_rev (f : A → Word B) (a : A × Bool) :
    signedWords f (a.1,!a.2) = FreeGroup.invRev (signedWords f a) := by
  rcases a with ⟨a,b⟩
  cases b <;> simp [signedWords]

lemma signedWords_eval (p : FreeGroup A →* G) (q : FreeGroup B →* G)
    (f : A → Word B) (hf : ∀ a, q (FreeGroup.mk (f a)) = p (FreeGroup.of a)) (a : A × Bool) :
    q (FreeGroup.mk (signedWords f a)) = p (FreeGroup.mk [a]) := by
  rcases a with ⟨a,b⟩
  cases b
  · change q ((FreeGroup.mk (f a))⁻¹) = p ((FreeGroup.of a)⁻¹)
    rw [map_inv,map_inv,hf]
  · exact hf a

lemma flatMap_eval (p : FreeGroup A →* G) (q : FreeGroup B →* G)
    (f : A × Bool → Word B) (hf : ∀ a, q (FreeGroup.mk (f a)) = p (FreeGroup.mk [a]))
    (z : Word A) : q (FreeGroup.mk (z.flatMap f)) = p (FreeGroup.mk z) := by
  induction z with
  | nil => exact (map_one q).trans (map_one p).symm
  | cons a z ih =>
    change q (FreeGroup.mk (f a ++ z.flatMap f)) = p (FreeGroup.mk ([a] ++ z))
    rw [← FreeGroup.mul_mk,← FreeGroup.mul_mk,map_mul,map_mul,hf,ih]

lemma exists_word (p : FreeGroup A →* G) (hp : Function.Surjective p) (g : G) :
    ∃ z : Word A, p (FreeGroup.mk z) = g := by
  obtain ⟨a,ha⟩ := hp g
  obtain ⟨z,hz⟩ := Quot.exists_rep a
  exact ⟨z,(congrArg p hz).trans ha⟩

namespace Homotopy
variable {R : Set (Word A)}

lemma append_both {z z' t t' : Word A} {k l : ℕ}
    (h : Homotopy R z z' k) (h' : Homotopy R t t' l) :
    Homotopy R (z++t) (z'++t') (k+l) := by
  have h₁ : Homotopy R (z++t) (z'++t) k := by simpa using h.contextual [] t
  have h₂ : Homotopy R (z'++t) (z'++t') l := by simpa using h'.contextual z' []
  exact h₁.trans h₂

lemma of_null_difference {z t : Word A} {k : ℕ}
    (h : Homotopy R (z ++ FreeGroup.invRev t) [] k) : Homotopy R z t k := by
  have h₀ : Homotopy R z ((z ++ FreeGroup.invRev t) ++ t) 0 :=
    Homotopy.free (by simp only [← FreeGroup.mul_mk,← FreeGroup.inv_mk]; group)
  have h₁ : Homotopy R ((z ++ FreeGroup.invRev t) ++ t) t k := by
    simpa using h.contextual [] t
  simpa using h₀.trans h₁

/-- A finite per-letter change of boundary words accumulates only linearly. -/
lemma compare_flatMap {B : Type*} (f : B × Bool → Word A) (g : B × Bool → Word A)
    (D : ℕ) (h : ∀ b, ∃ k ≤ D, Homotopy R (f b) (g b) k) (z : Word B) :
    ∃ k ≤ D*z.length, Homotopy R (z.flatMap f) (z.flatMap g) k := by
  induction z with
  | nil => exact ⟨0,by simp,.refl _⟩
  | cons b z ih =>
    obtain ⟨k,hk,hh⟩ := h b
    obtain ⟨l,hl,hz⟩ := ih
    refine ⟨k+l,?_,hh.append_both hz⟩
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega
end Homotopy

lemma flatMap_length_le (f : A × Bool → Word B) (L : ℕ)
    (hf : ∀ a, (f a).length ≤ L) (z : Word A) : (z.flatMap f).length ≤ L*z.length := by
  induction z with
  | nil => simp
  | cons a z ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    have := hf a
    omega

/-- Main quantitative substitution calculation. Both comparison disks and
old-relator disks are supplied as explicit literal Homotopy certificates. -/
lemma linear_of_substitutions {R : Set (Word A)} {S : Set (Word B)}
    (p : FreeGroup A →* G) (q : FreeGroup B →* G)
    (c : B × Bool → Word A) (d : A × Bool → Word B)
    (hd : ∀ a, d (a.1,!a.2) = FreeGroup.invRev (d a))
    (hc : ∀ b, p (FreeGroup.mk (c b)) = q (FreeGroup.mk [b]))
    (M D L : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hlength : ∀ b, (c b).length ≤ L)
    (hR : ∀ z ∈ R, ∃ a ≤ M, Homotopy S (z.flatMap d) [] a)
    (hcomp : ∀ b, ∃ a ≤ D, Homotopy S [b] ((c b).flatMap d) a)
    (hfill : ∀ z : Word A, p (FreeGroup.mk z) = 1 →
      ∃ a, Homotopy R z [] a ∧ (a : ℝ) ≤ C*z.length) :
    ∀ z : Word B, q (FreeGroup.mk z) = 1 →
      ∃ a, Homotopy S z [] a ∧ (a : ℝ) ≤ ((D : ℝ) + M*C*L)*z.length := by
  intro z hz
  have hz' : p (FreeGroup.mk (z.flatMap c)) = 1 := (flatMap_eval q p c hc z).trans hz
  obtain ⟨a,ha,hbound⟩ := hfill _ hz'
  obtain ⟨b,hb,hbfill⟩ := ha.substitute d hd hR
  obtain ⟨k,hk,hkfill⟩ := Homotopy.compare_flatMap (R := S) (fun b => [b])
    (fun b => (c b).flatMap d) D hcomp z
  have hleft : z.flatMap (fun b => [b]) = z := by simp
  rw [hleft,← List.flatMap_assoc] at hkfill
  refine ⟨k+b,by simpa using hkfill.trans hbfill,?_⟩
  have hk' : (k : ℝ) ≤ D*z.length := by exact_mod_cast hk
  have hb' : (b : ℝ) ≤ M*a := by exact_mod_cast hb
  have hlen : ((z.flatMap c).length : ℝ) ≤ L*z.length := by
    exact_mod_cast flatMap_length_le c L hlength z
  have ha' : (a : ℝ) ≤ C*(L*z.length) := hbound.trans (mul_le_mul_of_nonneg_left hlen hC)
  have hb'' := hb'.trans (mul_le_mul_of_nonneg_left ha' (Nat.cast_nonneg M))
  push_cast
  nlinarith

/-! Finite change of presentation preserves the literal linear disk bound.
All finite comparison disks are produced by ordinary algebraic van Kampen
existence; they are not introduced as extra geometric hypotheses. -/

lemma finitely_bounded [Fintype B] (f : B → ℕ) : ∃ M : ℕ, ∀ b, f b ≤ M :=
  ⟨Finset.univ.sup f,fun b => Finset.le_sup (f := f) (Finset.mem_univ b)⟩

/-- The target completeness premise is only the unquantified normal-closure
criterion, proved independently for every presentation used below. -/
theorem finite_change [Finite B] {R : Set (Word A)} {S : Set (Word B)}
    (p : FreeGroup A →* G) (hp : Function.Surjective p)
    (q : FreeGroup B →* G) (hq : Function.Surjective q)
    (finR : R.Finite) (validR : ∀ z ∈ R, p (FreeGroup.mk z) = 1)
    (completeS : ∀ z : Word B, q (FreeGroup.mk z) = 1 → ∃ k, Homotopy S z [] k)
    (C : ℝ) (hC : 0 ≤ C)
    (fillR : ∀ z : Word A, p (FreeGroup.mk z) = 1 →
      ∃ k, Homotopy R z [] k ∧ (k : ℝ) ≤ C*z.length) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : Word B, q (FreeGroup.mk z) = 1 →
      ∃ k, Homotopy S z [] k ∧ (k : ℝ) ≤ D*z.length := by
  classical
  let := Fintype.ofFinite B
  let := finR.fintype
  choose c hc using (fun b : B => exists_word p hp (q (FreeGroup.of b)))
  choose d hd using (fun a : A => exists_word q hq (p (FreeGroup.of a)))
  let cc := signedWords c
  let dd := signedWords d
  have cc_eval : ∀ b, p (FreeGroup.mk (cc b)) = q (FreeGroup.mk [b]) :=
    signedWords_eval q p c hc
  have dd_eval : ∀ a, q (FreeGroup.mk (dd a)) = p (FreeGroup.mk [a]) :=
    signedWords_eval p q d hd
  have old_disks : ∀ z : R, ∃ k, Homotopy S (z.val.flatMap dd) [] k := by
    intro z
    apply completeS
    exact (flatMap_eval p q dd dd_eval z.val).trans (validR z.val z.property)
  choose old_cost old_disk using old_disks
  obtain ⟨M,hM⟩ := finitely_bounded old_cost
  have comparisons : ∀ b : B × Bool, ∃ k, Homotopy S [b] ((cc b).flatMap dd) k := by
    intro b
    apply (completeS ([b] ++ FreeGroup.invRev ((cc b).flatMap dd)) ?_).imp
      (fun k hk => hk.of_null_difference)
    rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_inv,
      flatMap_eval p q dd dd_eval, cc_eval, mul_inv_cancel]
  choose compare_cost compare_disk using comparisons
  obtain ⟨D,hD⟩ := finitely_bounded compare_cost
  obtain ⟨L,hL⟩ := finitely_bounded (fun b => (cc b).length)
  refine ⟨D+M*C*L,by positivity,?_⟩
  apply linear_of_substitutions p q cc dd (signedWords_rev d) cc_eval M D L C hC hL
  · intro z hz
    exact ⟨old_cost ⟨z,hz⟩,hM _,old_disk ⟨z,hz⟩⟩
  · intro b
    exact ⟨compare_cost b,hD b,compare_disk b⟩
  · exact fillR

end WordPictures

/-! Literal finite relator words for the proved actual fundamental-group
presentation, including exact rooted route words. -/

namespace FinitePolyhedron.EdgePresentation
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

def chainWord {a b : V} : EdgeChain K a b → WordPictures.Word (Generator K)
  | .nil _ => []
  | .cons (a := a) (b := b) h p => (⟨(a,b),h⟩,true) :: chainWord p

omit [Fintype V] in
lemma mk_chainWord {a b : V} (p : EdgeChain K a b) : FreeGroup.mk (chainWord K p) = freeEval K p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    change FreeGroup.mk ([(⟨_,h⟩,true)] ++ chainWord K p) = _
    rw [←FreeGroup.mul_mk,ih]
    rfl

variable (o : V) (R : ∀ a, EdgeChain K o a)
inductive WordRelation : WordPictures.Word (Generator K) → Prop
  | self (a : V) : WordRelation [(⟨(a,a),edge_self K a⟩,true)]
  | triangle {a b c : V} (h : {a,b,c} ∈ K.faces)
      (hab : {a,b} ∈ K.faces) (hbc : {b,c} ∈ K.faces) (hac : {a,c} ∈ K.faces) :
      WordRelation [(⟨(a,b),hab⟩,true),(⟨(b,c),hbc⟩,true),(⟨(a,c),hac⟩,false)]
  | route (a : V) : WordRelation (chainWord K (R a))

omit [Fintype V] in
lemma relation_image : FreeGroup.mk '' WordRelation K o R = Relation K o R := by
  ext r
  constructor
  · rintro ⟨z,hz,rfl⟩
    cases hz with
    | self a => exact Relation.self a
    | triangle h hab hbc hac => exact Relation.triangle h hab hbc hac
    | route a => rw [mk_chainWord]; exact Relation.route a
  · intro hr
    cases hr with
    | self a => exact ⟨_,WordRelation.self a,rfl⟩
    | triangle h hab hbc hac => exact ⟨_,WordRelation.triangle h hab hbc hac,rfl⟩
    | route a => exact ⟨_,WordRelation.route a,mk_chainWord K (R a)⟩

lemma wordRelation_finite : Set.Finite (WordRelation K o R) := by
  classical
  let selves : V → WordPictures.Word (Generator K) := fun a => [(⟨(a,a),edge_self K a⟩,true)]
  let routes : V → WordPictures.Word (Generator K) := fun a => chainWord K (R a)
  have short : Set.Finite {z : WordPictures.Word (Generator K) | z.length ≤ 3} := by
    let f : (Σ n : Fin 4, Fin n.val → Generator K × Bool) → WordPictures.Word (Generator K) := fun x => List.ofFn x.2
    apply (Set.finite_range f).subset
    intro z hz
    change z.length ≤ 3 at hz
    refine ⟨⟨⟨z.length,by omega⟩,fun i => z[i]⟩,?_⟩
    exact List.ofFn_get z
  apply (short.union (Set.finite_range routes)).subset
  intro z hz
  cases hz with
  | self => exact Or.inl (by simp)
  | triangle => exact Or.inl (by simp)
  | route a => exact Or.inr ⟨a,rfl⟩

def wordToTopology (hR : R o = .nil o) : FreeGroup (Generator K) →* RootedPaths.PiOne (K := K) o :=
  (toTopology K o R hR).comp (PresentedGroup.mk (show Set (FreeGroup (Generator K)) from Relation K o R))

lemma wordToTopology_surjective (hR : R o = .nil o) : Function.Surjective (wordToTopology K o R hR) :=
  (toTopology_surjective K o R hR).comp (PresentedGroup.mk_surjective _)

lemma word_to_disk (hR : R o = .nil o) (z : WordPictures.Word (Generator K))
    (hz : wordToTopology K o R hR (FreeGroup.mk z) = 1) :
    ∃ k, WordPictures.Homotopy (WordRelation K o R) z [] k := by
  apply WordPictures.existence
  rw [relation_image]
  apply toTopology_injective K o R hR
  simpa only [wordToTopology,MonoidHom.comp_apply,map_one] using hz

end FinitePolyhedron.EdgePresentation

/-! Realization of ordinary word disks as literal triangular edge disks over
the frozen finite polyhedron. Free-group folds become actual zero-cost spurs. -/

namespace FiniteComplex

section
open FinitePolyhedron FinitePolyhedron.EdgeChain
variable (K : FiniteComplex) (o : K.Vertex) (R : ∀ a, K.Chain o a)
abbrev EdgeGenerator := EdgePresentation.Generator K.complex

def generatorChain (e : K.EdgeGenerator) : K.Chain o o := based o R (single e.property)
def signedChain (e : K.EdgeGenerator × Bool) : K.Chain o o :=
  if e.2 then generatorChain K o R e.1 else (generatorChain K o R e.1).reverse

def wordChain : WordPictures.Word K.EdgeGenerator → K.Chain o o
  | [] => .nil o
  | e::z => (signedChain K o R e).append (wordChain z)

lemma wordChain_append (z t : WordPictures.Word K.EdgeGenerator) :
    wordChain K o R (z++t) = (wordChain K o R z).append (wordChain K o R t) := by
  induction z with
  | nil => rfl
  | cons e z ih => simp only [List.cons_append,wordChain,ih,append_assoc]

lemma signedChain_reverse (e : K.EdgeGenerator × Bool) :
    signedChain K o R (e.1,!e.2) = (signedChain K o R e).reverse := by
  rcases e with ⟨e,b⟩
  cases b <;> simp [signedChain]

lemma wordChain_reverse (z : WordPictures.Word K.EdgeGenerator) :
    wordChain K o R (FreeGroup.invRev z) = (wordChain K o R z).reverse := by
  induction z with
  | nil => rfl
  | cons e z ih =>
    rw [FreeGroup.invRev_cons,wordChain_append,ih]
    change (wordChain K o R z).reverse.append ((signedChain K o R (e.1,!e.2)).append (.nil o)) = _
    rw [append_nil,signedChain_reverse]
    exact (reverse_append _ _).symm

lemma wordChain_context {z t : WordPictures.Word K.EdgeGenerator} {k : ℕ}
    (h : (wordChain K o R z).Homotopy (wordChain K o R t) k)
    (l r : WordPictures.Word K.EdgeGenerator) :
    (wordChain K o R (l++z++r)).Homotopy (wordChain K o R (l++t++r)) k := by
  simpa only [wordChain_append,append_assoc] using
    (h.append_right (wordChain K o R r)).append_left (wordChain K o R l)

lemma wordChain_free {z t : WordPictures.Word K.EdgeGenerator} (h : FreeGroup.Red.Step z t) :
    (wordChain K o R z).Homotopy (wordChain K o R t) 0 := by
  cases h with
  | @not l r e b =>
    have hh : (wordChain K o R [(e,b),(e,!b)]).Homotopy (wordChain K o R []) 0 := by
      change ((signedChain K o R (e,b)).append ((signedChain K o R (e,!b)).append (.nil o))).Homotopy (.nil o) 0
      rw [append_nil,show signedChain K o R (e,!b) = (signedChain K o R (e,b)).reverse from signedChain_reverse K o R (e,b)]
      exact cancel _
    simpa only [List.append_nil,List.append_assoc,List.cons_append,List.nil_append] using wordChain_context K o R hh l r

lemma wordChain_homotopy {S : Set (WordPictures.Word K.EdgeGenerator)} {M : ℕ}
    (rel : ∀ z ∈ S, ∃ k ≤ M, (wordChain K o R z).Homotopy (.nil o) k)
    {z t : WordPictures.Word K.EdgeGenerator} {a : ℕ} (h : WordPictures.Homotopy S z t a) :
    ∃ k ≤ M*a, (wordChain K o R z).Homotopy (wordChain K o R t) k := by
  induction h with
  | refl => exact ⟨0,by simp,DiskHomotopy.refl _⟩
  | move h =>
    cases h with
    | free h => exact ⟨0,by simp,wordChain_free K o R h⟩
    | face l r z hz =>
      obtain ⟨k,hk,hh⟩ := rel z hz
      exact ⟨k,by simpa using hk,by simpa using wordChain_context K o R (show (wordChain K o R z).Homotopy (wordChain K o R []) k from hh) l r⟩
    | reverseFace l r z hz =>
      obtain ⟨k,hk,hh⟩ := rel z hz
      have hh' : (wordChain K o R (FreeGroup.invRev z)).Homotopy (wordChain K o R []) k := by
        simpa only [wordChain_reverse,wordChain,reverse] using hh.reverse
      exact ⟨k,by simpa using hk,by simpa using wordChain_context K o R hh' l r⟩
  | symm _ ih => obtain ⟨k,hk,hh⟩ := ih; exact ⟨k,hk,hh.symm⟩
  | trans h h' ih ih' =>
    obtain ⟨k,hk,hh⟩ := ih
    obtain ⟨l,hl,hh'⟩ := ih'
    exact ⟨k+l,by rw [Nat.mul_add]; omega,hh.trans hh'⟩

lemma wordChain_chainWord {a b : K.Vertex} (p : K.Chain a b) :
    (wordChain K o R (EdgePresentation.chainWord K.complex p)).Homotopy (based o R p) 0 := by
  induction p with
  | nil a => exact (based_nil o R a).symm
  | cons h p ih =>
    exact (ih.append_left (generatorChain K o R ⟨_,h⟩)).trans_zero (based_append o R (single h) p)

lemma wordChain_relator (hR : R o = .nil o)
    (z : WordPictures.Word K.EdgeGenerator) (hz : EdgePresentation.WordRelation K.complex o R z) :
    ∃ k ≤ 1, (wordChain K o R z).Homotopy (.nil o) k := by
  cases hz with
  | self a =>
    have hh := (based_homotopy o R (single_self (K := K) a)).trans_zero (based_nil o R a)
    exact ⟨0,by omega,by simpa [wordChain,signedChain,generatorChain] using hh⟩
  | route a =>
    exact ⟨0,by omega,(wordChain_chainWord K o R (R a)).trans_zero (based_route o R hR a)⟩
  | @triangle a b c hf hab hbc hac =>
    obtain ⟨k,hk,hh⟩ := triangle (K := K) hf hab hbc hac
    have h₁ := (based_append o R (single hab) (single hbc)).zero_trans (based_homotopy o R hh)
    have h₂ := (h₁.append_right (based o R (single hac)).reverse).trans_zero (cancel (based o R (single hac)))
    refine ⟨k,hk,?_⟩
    simpa [wordChain,signedChain,generatorChain,append_assoc] using h₂

/-- A literal word disk in the intrinsic triangular presentation becomes an
actual disk of no more triangular faces; route cancellations have zero area. -/
lemma word_disk_realization (hR : R o = .nil o)
    {z : WordPictures.Word K.EdgeGenerator} {a : ℕ}
    (h : WordPictures.Homotopy (EdgePresentation.WordRelation K.complex o R) z [] a) :
    ∃ k ≤ a, (wordChain K o R z).Homotopy (.nil o) k := by
  simpa only [Nat.one_mul,wordChain] using wordChain_homotopy K o R (wordChain_relator K o R hR) h

end

/-! The challenge's literal disk moves preserve every triangular voltage.
This is valid even for the untyped intermediate lists in DiskHomotopy. -/
open FinitePolyhedron
variable (K : FiniteComplex) {G : Type*} [Group G] (v : Voltage K.complex G)

def pathValue : List K.Vertex → G
  | [] => 1
  | [_] => 1
  | a::b::r => v.value a b * pathValue (b::r)

lemma pathValue_prefix {a : K.Vertex} {u t : List K.Vertex}
    (h : pathValue K v (a::u) = pathValue K v (a::t)) (l : List K.Vertex) :
    pathValue K v (l++a::u) = pathValue K v (l++a::t) := by
  induction l with
  | nil => exact h
  | cons b l ih =>
    cases l with
    | nil => exact congrArg (v.value b a * ·) h
    | cons c l => exact congrArg (v.value b c * ·) ih

lemma diskMove_sound {p q : List K.Vertex} {k : ℕ} (h : K.DiskMove p q k) :
    pathValue K v p = pathValue K v q := by
  cases h with
  | stutter l r a =>
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    apply pathValue_prefix K v (l := l)
    simp only [pathValue,v.self,one_mul]
  | spur l r a b he =>
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    apply pathValue_prefix K v (l := l)
    simp only [pathValue,v.reverse he]
    group
  | triangle l r a b c hf hn =>
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    apply pathValue_prefix K v (l := l)
    simp only [pathValue,←mul_assoc,v.triangle a b c hf]

lemma diskHomotopy_sound {p q : List K.Vertex} {k : ℕ} (h : K.DiskHomotopy p q k) :
    pathValue K v p = pathValue K v q := by
  induction h with
  | refl => rfl
  | move h => exact diskMove_sound K v h
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'

lemma chain_pathValue {a b : K.Vertex} (p : K.Chain a b) :
    pathValue K v p.nodes = Voltage.EdgeChain.eval v p := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    change pathValue K v (a::p.nodes) = v.value a b * _
    rw [EdgeChain.nodes_eq_steps p,pathValue,←EdgeChain.nodes_eq_steps p,ih]
    rfl

end FiniteComplex

/-! Group-isomorphism transport for geometric actions. -/
section
universe u v w
namespace GeometricAction
variable {G : Type v} {H : Type w} [Group G] [Group H]
  {X : Type u} [MetricSpace X]

def pullback (e : G ≃* H) (A : GeometricAction H X) : GeometricAction G X where
  act := A.act.comp e.toMonoidHom
  proper C hC := by
    have hfin := A.proper C hC
    change (e ⁻¹' {g : H | ∃ x ∈ C, A.act g x ∈ C}).Finite
    exact Set.Finite.preimage e.injective.injOn hfin
  cocompact := by
    obtain ⟨C,hC,hcov⟩ := A.cocompact
    refine ⟨C,hC,fun x => ?_⟩
    obtain ⟨g,y,hy,he⟩ := hcov x
    exact ⟨e.symm g,y,hy,by simpa using he⟩
end GeometricAction

lemma NoGeometricCATZeroAction.of_mulEquiv {G : Type v} {H : Type w} [Group G] [Group H]
    (e : G ≃* H) (h : NoGeometricCATZeroAction.{u} G) : NoGeometricCATZeroAction.{u} H := by
  intro X m hn hp hc hz
  let := m
  let := hn
  let := hp
  let := hc
  have := h X m hn hp hc hz
  exact ⟨fun A => isEmptyElim (A.pullback e)⟩

/-- Inversion identifies a group with the opposite group without any
commutativity assumption. -/
def groupOppositeEquiv (G : Type v) [Group G] : Gᵐᵒᵖ ≃* G where
  toFun g := g.unop⁻¹
  invFun g := MulOpposite.op g⁻¹
  left_inv g := by simp
  right_inv g := by simp
  map_mul' g h := by simp [MulOpposite.unop_mul]

end

section

/-! Transfer of linear word filling to literal triangular disk filling.
All disk-null loops are handled,
with the same list length convention `length - 1`. -/

namespace FinitePolyhedron.EdgeChain
open HyperbolicObstruction.FiniteComplex
variable {K : FiniteComplex}

def ofListEnd (a b : K.Vertex) (t : List K.Vertex)
    (h : K.EdgePath (a :: (t ++ [b]))) : K.Chain a b :=
  match t with
  | [] => single h.1
  | c :: t => .cons h.1 (ofListEnd c b t h.2)

lemma nodes_ofListEnd (a b : K.Vertex) (t : List K.Vertex)
    (h : K.EdgePath (a :: (t ++ [b]))) :
    (ofListEnd a b t h).nodes = a :: (t ++ [b]) := by
  induction t generalizing a with
  | nil => rfl
  | cons c t ih => simp only [ofListEnd,nodes,ih,List.cons_append]

lemma chainWord_length {a b : K.Vertex} (p : K.Chain a b) :
    (EdgePresentation.chainWord K.complex p).length = p.nodes.length - 1 := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [EdgePresentation.chainWord,List.length_cons,nodes,ih]
    rw [nodes_eq_steps p]
    simp
end FinitePolyhedron.EdgeChain

namespace FiniteComplex
open FinitePolyhedron FinitePolyhedron.EdgeChain
variable (K : FiniteComplex) (o : K.Vertex) (R : ∀ a, K.Chain o a) (hR : R o = .nil o)

lemma disk_word_null {a : K.Vertex} (p : K.Chain a a)
    (hd : ∃ k, K.Disk p.nodes k) :
    EdgePresentation.wordToTopology K.complex o R hR
      (FreeGroup.mk (EdgePresentation.chainWord K.complex p)) = 1 := by
  obtain ⟨k,b,h⟩ := hd
  have hh := diskHomotopy_sound K (EdgePresentation.voltage K.complex o R) h
  rw [chain_pathValue,EdgePresentation.eval_eq_mk] at hh
  change _ = 1 at hh
  rw [EdgePresentation.wordToTopology,MonoidHom.comp_apply,EdgePresentation.mk_chainWord,hh,map_one]

/-- Intrinsic word area gives literal triangular disk area with no loss. -/
theorem linearDiskFilling_of_intrinsic (C : ℝ) (_ : 0 ≤ C)
    (fill : ∀ z : WordPictures.Word K.EdgeGenerator,
      EdgePresentation.wordToTopology K.complex o R hR (FreeGroup.mk z) = 1 →
      ∃ k, WordPictures.Homotopy (EdgePresentation.WordRelation K.complex o R) z [] k ∧
        (k : ℝ) ≤ C*z.length) : K.LinearDiskFilling C := by
  intro p hp hc hd
  obtain ⟨a,t,hp'|hp'⟩ := hc
  · subst p
    let q := ofListEnd a a t hp
    have hq : q.nodes = a :: (t ++ [a]) := nodes_ofListEnd a a t hp
    have hd' : ∃ k, K.Disk q.nodes k := by simpa only [hq] using hd
    obtain ⟨k,hk,hbound⟩ := fill (EdgePresentation.chainWord K.complex q)
      (disk_word_null K o R hR q hd')
    obtain ⟨l,hl,hreal⟩ := word_disk_realization K o R hR hk
    have hbased := (wordChain_chainWord K o R q).symm.zero_trans hreal
    have hback := unbase o R hbased
    refine ⟨l,⟨a,?_⟩,?_⟩
    · change K.DiskHomotopy q.nodes [a] l at hback
      simpa only [hq] using hback
    · rw [chainWord_length,hq] at hbound
      exact le_trans (by exact_mod_cast hl) hbound
  · subst p
    exact ⟨0,⟨a,DiskHomotopy.refl _⟩,by simp⟩

include R hR in
/-- Quantitative finite-presentation change, followed by literal geometric
realization, produces the exact main's triangular filling assertion. -/
theorem linearDiskFilling_of_presentation {A G : Type*} [Group G]
    (S : Set (WordPictures.Word A)) (p : FreeGroup A →* G) (hp : Function.Surjective p)
    (e : G ≃* RootedPaths.PiOne (K := K.complex) o)
    (finS : S.Finite) (validS : ∀ z ∈ S, p (FreeGroup.mk z) = 1)
    (C : ℝ) (hC : 0 ≤ C)
    (fill : ∀ z : WordPictures.Word A, p (FreeGroup.mk z) = 1 →
      ∃ k, WordPictures.Homotopy S z [] k ∧ (k : ℝ) ≤ C*z.length) :
    ∃ D : ℝ, 0 ≤ D ∧ K.LinearDiskFilling D := by
  obtain ⟨D,hD,hfill⟩ := WordPictures.finite_change
    (e.toMonoidHom.comp p) (e.surjective.comp hp)
    (EdgePresentation.wordToTopology K.complex o R hR)
    (EdgePresentation.wordToTopology_surjective K.complex o R hR) finS
    (fun z hz => by simp only [MonoidHom.comp_apply,validS z hz,map_one])
    (EdgePresentation.word_to_disk K.complex o R hR) C hC
    (fun z hz => fill z (e.injective (by
      change e (p (FreeGroup.mk z)) = 1 at hz
      exact hz.trans (map_one e).symm)))
  exact ⟨D,hD,linearDiskFilling_of_intrinsic K o R hR D hD hfill⟩

lemma nonempty_vertex (x : K.Carrier) : Nonempty K.Vertex := by
  by_contra h
  have : IsEmpty K.Vertex := not_nonempty_iff.mp h
  have hs := x.property.2.1
  simp at hs

/-- Basepoint-independent form of the faithful finite-presentation transfer. -/
theorem linearDiskFilling_of_piOne [PathConnectedSpace K.Carrier]
    {A G : Type*} [Group G] (x : K.Carrier)
    (S : Set (WordPictures.Word A)) (p : FreeGroup A →* G) (hp : Function.Surjective p)
    (e : G ≃* FundamentalGroup K.Carrier x)
    (finS : S.Finite) (validS : ∀ z ∈ S, p (FreeGroup.mk z) = 1)
    (C : ℝ) (hC : 0 ≤ C)
    (fill : ∀ z : WordPictures.Word A, p (FreeGroup.mk z) = 1 →
      ∃ k, WordPictures.Homotopy S z [] k ∧ (k : ℝ) ≤ C*z.length) :
    ∃ D : ℝ, 0 ≤ D ∧ K.LinearDiskFilling D := by
  let : PathConnectedSpace (FinitePolyhedron.Carrier K.complex) := ‹PathConnectedSpace K.Carrier›
  obtain ⟨o⟩ := nonempty_vertex K x
  let e' : G ≃* RootedPaths.PiOne (K := K.complex) o :=
    e.trans ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x (vertex K.complex o)).trans
      (groupOppositeEquiv _).symm)
  exact linearDiskFilling_of_presentation K o (edgeRoutes K.complex o)
    (edgeRoutes_self K.complex o) S p hp e' finS validS C hC fill

end FiniteComplex
end

/-! Actual homotopy-equivalence invariance of the fundamental group. -/
section
open CategoryTheory
open scoped ContinuousMap

def fundamentalGroupHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (e x) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  exact MulEquiv.ofBijective (E.functor.mapEnd (FundamentalGroupoid.mk x))
    ⟨E.functor.map_injective,E.functor.map_surjective⟩

end

/-! The literal finite barycentric complex has exactly the original letter group,
not a conditional presentation of it. -/

namespace ConeSkeleton

section
universe u
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
local instance : DecidableEq (ElementaryVertex n w) := Classical.decEq _
local instance : DecidableEq (ElementaryEdge n w) := Classical.decEq _
local instance : DecidableEq (ElementaryCell n w d) := Classical.decEq _

def elementaryFinitePiOneEquiv : LetterPresentation.Group n w d ≃*
    FundamentalGroup (elementaryFiniteComplex n w d).Carrier (elementaryFiniteBasepoint n w d) :=
  (elementaryTopologyEquiv n w d).trans ((groupOppositeEquiv _).trans
    (fundamentalGroupHomotopyEquiv (elementaryFiniteHomeomorph n w d).toHomotopyEquiv
      (elementaryBasepoint n w d)))

lemma elementaryFinite_noAction (h : NoGeometricCATZeroAction.{u} (LetterPresentation.Group n w d)) :
    NoGeometricCATZeroAction.{u}
      (FundamentalGroup (elementaryFiniteComplex n w d).Carrier (elementaryFiniteBasepoint n w d)) :=
  h.of_mulEquiv (elementaryFinitePiOneEquiv n w d)

end

/-! Infinitude can be obtained without a topological Euler theorem: the many
six-letter cells alone inject into the original letter-edge module of any
finite cover. Their cardinality exceeds the number of original generators. -/

open IncidenceTemplate CoreGeometry LetterPresentation IntegralIncidence
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

abbrev SixChain := (LetterPresentation.Group n w d × Six n d) →₀ ℤ
abbrev OriginalEdgeChain := (LetterPresentation.Group n w d × Fin (n+1)) →₀ ℤ

def sixCellIndex (c : LetterPresentation.Group n w d × Six n d) :
    LetterPresentation.Group n w d × ElementaryCell n w d :=
  (c.1,.inr (.inr (.inr c.2)))

def originalEdgeIndex (e : LetterPresentation.Group n w d × Fin (n+1)) :
    LetterPresentation.Group n w d × ElementaryEdge n w :=
  (e.1,.inl (.inl e.2))

lemma sixCellIndex_injective : Function.Injective (sixCellIndex n w d) := by
  intro x y h
  have hh : x.1 = y.1 ∧ x.2 = y.2 := by
    simpa only [sixCellIndex,Prod.mk.injEq,Sum.inr.injEq] using h
  exact Prod.ext hh.1 hh.2

lemma originalEdgeIndex_injective : Function.Injective (originalEdgeIndex n w d) := by
  intro x y h
  have hh : x.1 = y.1 ∧ x.2 = y.2 := by
    simpa only [originalEdgeIndex,Prod.mk.injEq,Sum.inl.injEq] using h
  exact Prod.ext hh.1 hh.2

def sixFaceBoundary (c : LetterPresentation.Group n w d × Six n d) : OriginalEdgeChain n w d :=
  ∑ i : Fin 6, edgeChain (fun a : Alphabet n =>
    elementaryVoltage n w (letterVoltage n w d) ((.inl (.inl a.1)),a.2))
      (c.1 * elementaryOffset n w d (letterVoltage n w d) (sixCellIndex n w d c).2 i,
        c.2.val i)

def sixBoundary : SixChain n w d →ₗ[ℤ] OriginalEdgeChain n w d :=
  Finsupp.linearCombination ℤ (sixFaceBoundary n w d)

lemma originalEdgeChain_map (g : LetterPresentation.Group n w d) (a : Alphabet n) :
    Finsupp.lmapDomain ℤ ℤ (originalEdgeIndex n w d)
      (edgeChain (fun a : Alphabet n => elementaryVoltage n w (letterVoltage n w d)
        ((.inl (.inl a.1)),a.2)) (g,a)) =
    edgeChain (elementaryVoltage n w (letterVoltage n w d)) (g,(.inl (.inl a.1),a.2)) := by
  rcases a with ⟨a,b⟩
  cases b <;> simp only [edgeChain,Bool.false_eq_true,ite_false,ite_true,map_neg,
    Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,originalEdgeIndex]

lemma sixFaceBoundary_map (c : LetterPresentation.Group n w d × Six n d) :
    Finsupp.lmapDomain ℤ ℤ (originalEdgeIndex n w d) (sixFaceBoundary n w d c) =
      (elementaryPolygons n w d).faceBoundary (elementaryVoltage n w (letterVoltage n w d))
        (sixCellIndex n w d c) := by
  unfold sixFaceBoundary Polygons.faceBoundary
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [originalEdgeChain_map]
  rfl

lemma sixBoundary_map (z : SixChain n w d) :
    Finsupp.lmapDomain ℤ ℤ (originalEdgeIndex n w d) (sixBoundary n w d z) =
      letterBoundary₂ n w d (Finsupp.lmapDomain ℤ ℤ (sixCellIndex n w d) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single c a =>
    simp only [sixBoundary,Finsupp.linearCombination_single,map_smul,
      letterBoundary₂,Polygons.d₂]
    rw [sixFaceBoundary_map]
    simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
      Finsupp.linearCombination_single]

lemma sixBoundary_injective (h : Function.Injective (letterBoundary₂ n w d)) :
    Function.Injective (sixBoundary n w d) := by
  intro x y he
  apply Finsupp.mapDomain_injective (sixCellIndex_injective n w d)
  apply h
  change letterBoundary₂ n w d (Finsupp.lmapDomain ℤ ℤ (sixCellIndex n w d) x) =
    letterBoundary₂ n w d (Finsupp.lmapDomain ℤ ℤ (sixCellIndex n w d) y)
  rw [←sixBoundary_map,←sixBoundary_map,he]

lemma six_card_le_of_finite [Fintype (LetterPresentation.Group n w d)]
    (h : Function.Injective (letterBoundary₂ n w d)) : Fintype.card (Six n d) ≤ n+1 := by
  have hk := LinearMap.finrank_le_finrank_of_injective (sixBoundary_injective n w d h)
  simp only [Module.finrank_finsupp_self,Fintype.card_prod,Fintype.card_fin] at hk
  have hp := Fintype.card_pos (α := LetterPresentation.Group n w d)
  nlinarith

/-- An exact algebraic infinitude criterion for the actual presentation. -/
theorem infinite_of_boundary_and_six (h : Function.Injective (letterBoundary₂ n w d))
    (hs : n+1 < Fintype.card (Six n d)) : Infinite (LetterPresentation.Group n w d) := by
  rcases finite_or_infinite (LetterPresentation.Group n w d) with hf | hi
  · let := Fintype.ofFinite (LetterPresentation.Group n w d)
    exact False.elim (Nat.not_lt_of_ge (six_card_le_of_finite n w d h) hs)
  · exact hi

end ConeSkeleton

section

namespace SixTable
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

lemma included_pair_of_good {δ ε : ℝ} (he : ε < 1)
    {d : (Fin 6 → A) → Bool} (hd : ¬ BadPairs δ ε d)
    {r q : Fin 6} (hrq : r ≠ q) (u v : A) :
    ∃ x : Fin 6 → A, d x = true ∧ x r = u ∧ x q = v := by
  have hh : |count r q u v d - (Fintype.card A : ℝ)^(1-δ)| <
      ε*(Fintype.card A : ℝ)^(1-δ) :=
    lt_of_not_ge (fun h => hd ⟨⟨(r,q),hrq⟩,u,v,h⟩)
  have hp : 0 < (Fintype.card A : ℝ)^(1-δ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Fintype.card_pos (α := A)) _
  have hc : 0 < count r q u v d := by
    have hlo := (abs_lt.mp hh).1
    nlinarith
  by_contra hn
  have hz : count r q u v d = 0 := by
    unfold count
    apply Finset.sum_eq_zero
    intro x hx
    have hpair := (mem_pairTrials hrq u v x).mp hx
    have hfalse : d x = false := Bool.eq_false_iff.mpr (fun h => hn ⟨x,h,hpair⟩)
    simp [hfalse]
  linarith

lemma card_included_at_least_pairs {δ ε : ℝ} (he : ε < 1)
    {d : (Fin 6 → A) → Bool} (hd : ¬ BadPairs δ ε d) :
    Fintype.card A * Fintype.card A ≤ Fintype.card {x : Fin 6 → A // d x = true} := by
  classical
  let f : {x : Fin 6 → A // d x = true} → A × A := fun x => (x.val 0,x.val 1)
  have hs : Function.Surjective f := by
    rintro ⟨u,v⟩
    obtain ⟨x,hx,hr,hq⟩ := included_pair_of_good he hd (by decide : (0 : Fin 6) ≠ 1) u v
    exact ⟨⟨x,hx⟩,Prod.ext hr hq⟩
  simpa only [Fintype.card_prod] using Fintype.card_le_of_surjective f hs
end SixTable

namespace IncidenceTemplate
open LetterPresentation
lemma SamplingStage.many_six {m : ℕ} {δ : ℝ} (s : SamplingStage m δ) :
    s.size+1 < Fintype.card (ConeSkeleton.Six s.size s.six) := by
  have hh := SixTable.card_included_at_least_pairs
    ((stageError_le_third m).trans_lt (by norm_num : (1:ℝ)/3 < 1)) s.six_good
  rw [card_symmetricAlphabet] at hh
  simp only [←Nat.card_eq_fintype_card] at hh ⊢
  change 2*(s.size+1)*(2*(s.size+1)) ≤ Nat.card (ConeSkeleton.Six s.size s.six) at hh
  nlinarith
end IncidenceTemplate
end

/-! The same supplied final arrays yield infinite groups unconditionally.
This discharges the last group-action-side hypothesis; the finite-polyhedron
realization and group-to-topology consequences are still separate obligations. -/
namespace IncidenceTemplate

section
open CoreGeometry LetterPresentation ConeSkeleton

/-- Infinitude via the independent six-cell rank obstruction, with all
finite-table/cardinality and d₂ hypotheses discharged. -/
instance finalDiagramStage_infinite (m : ℕ) :
    Infinite (SamplingStage.LetterGroup finalDiagramStage m) :=
  infinite_of_boundary_and_six (finalSize m) (finalMaster m) (finalSix m)
    (finalDiagramStage_boundary_injective m) ((finalDiagramStage m).many_six)

/-- The no-action conclusion for the selected original groups,
without an infinitude assumption. -/
theorem finalDiagramStage_noAction :
    ∀ᶠ m in Filter.atTop, NoGeometricCATZeroAction (SamplingStage.LetterGroup finalDiagramStage m) :=
  SamplingStage.eventually_noAction finalDiagramStage

/-- A single finite letter presentation, infinite with linear nullword filling
and no geometric action on any proper complete CAT(0) space. -/
theorem exists_infinite_linear_noAction : ∃ m : ℕ,
    Infinite (SamplingStage.LetterGroup finalDiagramStage m) ∧
    NoGeometricCATZeroAction (SamplingStage.LetterGroup finalDiagramStage m) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ word : List (Alphabet (finalSize m)),
      PresentedGroup.mk (Relator (finalSize m) (finalMaster m) (finalSix m)) (FreeGroup.mk word) = 1 →
      ∃ a, WordPictures.Homotopy (SimpleWordRelator (finalSize m) (finalMaster m) (finalSix m))
        word [] a ∧ (a : ℝ) ≤ C * word.length := by
  obtain ⟨m,hm⟩ := finalDiagramStage_noAction.exists
  exact ⟨m,inferInstance,hm,finalDiagramStage_linear m⟩

/-! The selected presentations give actual connected finite polyhedra
whose fundamental groups admit no geometric CAT(0) action. -/
open CoreGeometry LetterPresentation ConeSkeleton
universe u

def finalFiniteComplex (m : ℕ) : FiniteComplex :=
  elementaryFiniteComplex (finalSize m) (finalMaster m) (finalSix m)

def finalFiniteBasepoint (m : ℕ) : (finalFiniteComplex m).Carrier :=
  elementaryFiniteBasepoint (finalSize m) (finalMaster m) (finalSix m)

instance finalFinite_pathConnected (m : ℕ) : PathConnectedSpace (finalFiniteComplex m).Carrier :=
  elementaryFinite_pathConnected (finalSize m) (finalMaster m) (finalSix m)

def finalFinitePiOneEquiv (m : ℕ) : SamplingStage.LetterGroup finalDiagramStage m ≃*
    FundamentalGroup (finalFiniteComplex m).Carrier (finalFiniteBasepoint m) :=
  elementaryFinitePiOneEquiv (finalSize m) (finalMaster m) (finalSix m)

instance finalFinite_infinite (m : ℕ) :
    Infinite (FundamentalGroup (finalFiniteComplex m).Carrier (finalFiniteBasepoint m)) :=
  Infinite.of_injective (finalFinitePiOneEquiv m) (finalFinitePiOneEquiv m).injective

theorem finalFinite_noAction : ∀ᶠ m in Filter.atTop,
    NoGeometricCATZeroAction.{u}
      (FundamentalGroup (finalFiniteComplex m).Carrier (finalFiniteBasepoint m)) :=
  finalDiagramStage_noAction.mono fun m h => h.of_mulEquiv (finalFinitePiOneEquiv m)

/-- A finite topological model whose fundamental group admits no geometric
CAT(0) action, without asphericity or metric conclusions. -/
theorem exists_finite_infinite_noAction : ∃ K : FiniteComplex, ∃ x : K.Carrier,
    ConnectedSpace K.Carrier ∧ Infinite (FundamentalGroup K.Carrier x) ∧
      NoGeometricCATZeroAction.{u} (FundamentalGroup K.Carrier x) := by
  obtain ⟨m,hm⟩ := finalFinite_noAction.exists
  exact ⟨finalFiniteComplex m,finalFiniteBasepoint m,inferInstance,inferInstance,hm⟩

end

/-! The very same selected finite complex now satisfies the original main's
literal triangular linear disk inequality, in addition to its pi1 obstruction.
No picture-producer or filling-transfer hypothesis remains. -/
section
open CoreGeometry LetterPresentation ConeSkeleton
universe u

lemma finalFinite_linear (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ (finalFiniteComplex m).LinearDiskFilling C := by
  obtain ⟨C,hC,fill⟩ := finalDiagramStage_linear m
  apply FiniteComplex.linearDiskFilling_of_piOne (finalFiniteComplex m)
    (finalFiniteBasepoint m)
    (SimpleWordRelator (finalSize m) (finalMaster m) (finalSix m))
    (PresentedGroup.mk (Relator (finalSize m) (finalMaster m) (finalSix m)))
    (PresentedGroup.mk_surjective _) (finalFinitePiOneEquiv m)
    (simpleWordRelator_finite _ _ _) ?_ C hC.le fill
  intro z hz
  apply PresentedGroup.one_of_mem
  rw [← wordRelator_image]
  exact ⟨z,simpleWordRelator_original _ _ _ hz,rfl⟩

/-- A connected finite model with infinite fundamental group, linear disk
filling, and no geometric CAT(0) action of its fundamental group. -/
theorem exists_finite_linear_noAction : ∃ K : FiniteComplex, ∃ x : K.Carrier, ∃ C : ℝ,
    ConnectedSpace K.Carrier ∧ Infinite (FundamentalGroup K.Carrier x) ∧
      0 ≤ C ∧ K.LinearDiskFilling C ∧
      NoGeometricCATZeroAction.{u} (FundamentalGroup K.Carrier x) := by
  obtain ⟨m,hm⟩ := finalFinite_noAction.exists
  obtain ⟨C,hC,hfill⟩ := finalFinite_linear m
  exact ⟨finalFiniteComplex m,finalFiniteBasepoint m,C,inferInstance,inferInstance,hC,hfill,hm⟩

end

/-! The SAME selected arrays give a literal basepoint-fixing contraction of
 their actual universal cover. In particular the full higher-homotopy clause
 of the unchanged finite-model theorem is discharged, unconditionally. -/

open CoreGeometry LetterPresentation ConeSkeleton FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
universe u
variable (m : ℕ)
local instance : DecidableEq (ElementaryVertex (finalSize m) (finalMaster m)) := Classical.decEq _
local instance : DecidableEq (ElementaryEdge (finalSize m) (finalMaster m)) := Classical.decEq _
local instance : DecidableEq (ElementaryCell (finalSize m) (finalMaster m) (finalSix m)) := Classical.decEq _
local instance : TopologicalSpace (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) := ⊥
local instance : DiscreteTopology (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) := ⟨rfl⟩

lemma finalCover_higher (k : ℕ) : Subsingleton (HomotopyGroup.Pi (k+2)
    (elementarySourceVoltage (finalSize m) (finalMaster m) (finalSix m)).TotalSpace
    (elementaryUniversalBasepoint (finalSize m) (finalMaster m) (finalSix m))) := by
  let P := elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)
  let ρ := fun e => elementaryVoltage (finalSize m) (finalMaster m)
    (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) (e,true)
  have hc : ∀ c, (List.ofFn (fun i => Data.signed ρ (P.side c i))).prod = 1 := by
    dsimp only [P,ρ]
    intro c
    simpa only [elementarySignedVoltage,elementaryPolygonData] using
      elementaryLetterVoltage_cell (finalSize m) (finalMaster m) (finalSix m) c
  let v := P.voltage ρ hc
  let z : v.TotalSpace := elementaryUniversalBasepoint (finalSize m) (finalMaster m) (finalSix m)
  let : LinearOrder P.Vertex := linearOrderOfSTO WellOrderingRel
  let : SimplyConnectedSpace v.TotalSpace :=
    elementarySourceUniversalCover_simplyConnected (finalSize m) (finalMaster m) (finalSix m)
  let : CommGroup (v.LoopClass z) := HSpaceFundamental.commGroup
  let T := P.obstructionWeight ρ hc z
  let w := finalTriangleEdgeWeight m (Additive (v.LoopClass z)) T
  have hw := finalTriangleEdgeWeight_equation m (Additive (v.LoopClass z)) T
  change Subsingleton (HomotopyGroup.Pi (k+2) v.TotalSpace z)
  apply BasedHigherContraction.subsingleton z (P.coverContraction ρ hc z w hw)
    (P.coverContraction_initial ρ hc z w hw) (P.coverContraction_final ρ hc z w hw)
  exact P.coverContraction_fixed ρ hc z w hw (elementaryBaseVertex (finalSize m) (finalMaster m) (finalSix m)) 1 rfl

lemma finalFinite_aspherical : (finalFiniteComplex m).Aspherical (finalFiniteBasepoint m) := by
  apply (elementaryAspherical_iff (finalSize m) (finalMaster m) (finalSix m)).mpr
  exact finalCover_higher m

/-- The entire finite aspherical linear-filling no-action construction, on one
model. The two metric consequences remain distinct obligations of main. -/
theorem exists_finite_aspherical_linear_noAction :
    ∃ K : FiniteComplex, ∃ x : K.Carrier, ∃ C : ℝ,
    ConnectedSpace K.Carrier ∧ K.Aspherical x ∧ Infinite (FundamentalGroup K.Carrier x) ∧
      0 ≤ C ∧ K.LinearDiskFilling C ∧
      NoGeometricCATZeroAction.{u} (FundamentalGroup K.Carrier x) := by
  obtain ⟨m,hm⟩ := finalFinite_noAction.exists
  obtain ⟨C,hC,hfill⟩ := finalFinite_linear m
  exact ⟨finalFiniteComplex m,finalFiniteBasepoint m,C,inferInstance,finalFinite_aspherical m,
    inferInstance,hC,hfill,hm⟩

end IncidenceTemplate

/-! Elementary facts about WordLength and WordDistance for the four-point
characterization of hyperbolicity. -/
section
open Set
variable {G : Type*} [Group G]
namespace WordLength
variable (S : Finset G)

def Good (w : List G) : Prop := ∀ a ∈ w, a ∈ S ∨ a⁻¹ ∈ S

lemma good_nil : Good S [] := by simp [Good]
lemma good_append {u v : List G} (hu : Good S u) (hv : Good S v) : Good S (u++v) := by
  intro a ha
  rcases List.mem_append.mp ha with ha|ha
  · exact hu a ha
  · exact hv a ha
lemma good_inverse {w : List G} (hw : Good S w) : Good S ((w.map Inv.inv).reverse) := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  simpa only [inv_inv,or_comm] using hw b hb

lemma exists_word (hS : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    ∃ w : List G, Good S w ∧ w.prod = g := by
  have hg : g ∈ Subgroup.closure (S : Set G) := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨[x],by simpa [Good] using Or.inl hx,by simp⟩
  | one => exact ⟨[],good_nil S,rfl⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨u,hu,rfl⟩ := ihx
    obtain ⟨v,hv,rfl⟩ := ihy
    exact ⟨u++v,good_append S hu hv,List.prod_append⟩
  | inv x hx ih =>
    obtain ⟨u,hu,rfl⟩ := ih
    exact ⟨(u.map Inv.inv).reverse,good_inverse S hu,(List.prod_inv_reverse u).symm⟩

lemma le_length {w : List G} (hw : Good S w) : WordLength S w.prod ≤ w.length := by
  apply Nat.sInf_le
  exact ⟨w,rfl,hw,rfl⟩

lemma attained (hS : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    ∃ w : List G, w.length = WordLength S g ∧ Good S w ∧ w.prod = g := by
  change WordLength S g ∈ {n | ∃ w : List G, w.length = n ∧ Good S w ∧ w.prod = g}
  exact Nat.sInf_mem (by
    obtain ⟨w,hw,hg⟩ := exists_word S hS g
    exact ⟨w.length,w,rfl,hw,hg⟩)

@[simp] lemma one : WordLength S 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [List.prod_nil,List.length_nil] using le_length S (good_nil S)

lemma eq_zero_iff (hS : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    WordLength S g = 0 ↔ g=1 := by
  refine ⟨fun h => ?_,fun h => h ▸ one S⟩
  obtain ⟨w,hw,_,rfl⟩ := attained S hS g
  have he : w=[] := List.length_eq_zero_iff.mp (hw.trans h)
  simp [he]

lemma mul_le (hS : Subgroup.closure (S : Set G) = ⊤) (g h : G) :
    WordLength S (g*h) ≤ WordLength S g+WordLength S h := by
  obtain ⟨u,hu,hu',rfl⟩ := attained S hS g
  obtain ⟨v,hv,hv',rfl⟩ := attained S hS h
  have hh := le_length S (good_append S hu' hv')
  simpa only [List.prod_append,List.length_append,hu,hv] using hh

lemma inv_le (hS : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    WordLength S g⁻¹ ≤ WordLength S g := by
  obtain ⟨u,hu,hu',rfl⟩ := attained S hS g
  have hh := le_length S (good_inverse S hu')
  simpa only [←List.prod_inv_reverse,List.length_reverse,List.length_map,hu] using hh

@[simp] lemma inv (hS : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    WordLength S g⁻¹ = WordLength S g := by
  exact le_antisymm (inv_le S hS g) (by simpa only [inv_inv] using inv_le S hS g⁻¹)
end WordLength

namespace WordDistance
variable (S : Finset G) (hS : Subgroup.closure (S : Set G) = ⊤)
lemma nonneg (g h : G) : 0 ≤ WordDistance S g h := Nat.cast_nonneg _
@[simp] lemma self (g : G) : WordDistance S g g = 0 := by simp [WordDistance]
include hS
lemma comm (g h : G) : WordDistance S g h = WordDistance S h g := by
  rw [WordDistance,WordDistance,←WordLength.inv S hS (g⁻¹*h)]
  simp
lemma eq_zero_iff (g h : G) : WordDistance S g h=0 ↔ g=h := by
  simp only [WordDistance,Nat.cast_eq_zero,WordLength.eq_zero_iff S hS,inv_mul_eq_one]
lemma triangle (g h k : G) : WordDistance S g k ≤ WordDistance S g h+WordDistance S h k := by
  have hh := WordLength.mul_le S hS (g⁻¹*h) (h⁻¹*k)
  simp only [mul_assoc,mul_inv_cancel_left] at hh
  change (WordLength S (g⁻¹*k) : ℝ) ≤ (WordLength S (g⁻¹*h) : ℝ) + (WordLength S (h⁻¹*k) : ℝ)
  exact_mod_cast hh
omit hS in
lemma left (a g h : G) : WordDistance S (a*g) (a*h) = WordDistance S g h := by
  simp [WordDistance,mul_assoc]

/-- The canonical word metric agrees with WordDistance. -/
@[instance_reducible] def metric : MetricSpace G where
  dist := WordDistance S
  dist_self := self S
  dist_comm := comm S hS
  dist_triangle := triangle S hS
  eq_of_dist_eq_zero := (eq_zero_iff S hS _ _).mp

end WordDistance
end

/-! Cochains are evaluated on the actual area-counted word homotopies.
Free folds contribute exactly zero; each literal relator contributes its
own cochain integral. No planar realization hypothesis is needed. -/
namespace WordPictures
variable {A G : Type*} [Group G]
namespace Cochain
variable (φ : FreeGroup A →* G) (ω : G → G → ℝ)

def value (w : Word A) : G := φ (FreeGroup.mk w)
def letter (a : A × Bool) : G := value φ [a]
def integral : G → Word A → ℝ
  | _, [] => 0
  | g, a::w => ω g (g*letter φ a) + integral (g*letter φ a) w

@[simp] lemma value_nil : value φ [] = 1 := map_one φ
@[simp] lemma value_append (u v : Word A) : value φ (u++v)=value φ u*value φ v :=
  by simp only [value,←FreeGroup.mul_mk,map_mul]
@[simp] lemma value_cons (a : A × Bool) (w : Word A) :
    value φ (a::w)=letter φ a*value φ w := value_append φ [a] w
@[simp] lemma value_reverse (w : Word A) :
    value φ (FreeGroup.invRev w)=(value φ w)⁻¹ := by simp only [value,←FreeGroup.inv_mk,map_inv]
@[simp] lemma letter_flip (a : A) (b : Bool) : letter φ (a,!b)=(letter φ (a,b))⁻¹ := by
  change value φ (FreeGroup.invRev [(a,b)]) = _
  exact value_reverse φ _
@[simp] lemma integral_nil (g : G) : integral φ ω g []=0 := rfl
@[simp] lemma integral_cons (g : G) (a : A × Bool) (w : Word A) :
    integral φ ω g (a::w)=ω g (g*letter φ a)+integral φ ω (g*letter φ a) w := rfl
lemma integral_append (g : G) (u v : Word A) :
    integral φ ω g (u++v)=integral φ ω g u+integral φ ω (g*value φ u) v := by
  induction u generalizing g with
  | nil => simp
  | cons a u ih => simp only [List.cons_append,integral_cons,value_cons,ih,mul_assoc]; ring

variable (hω : ∀ x y, ω x y = -ω y x)
include hω
lemma integral_reverse (g : G) (w : Word A) :
    integral φ ω (g*value φ w) (FreeGroup.invRev w) = -integral φ ω g w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w a ih =>
    rcases a with ⟨a,b⟩
    simp only [FreeGroup.invRev_append,integral_append,value_append]
    rw [show FreeGroup.invRev [(a,b)]=[(a,!b)] by simp [FreeGroup.invRev]]
    simp only [integral_cons,integral_nil,value_cons,value_nil,mul_one,letter_flip]
    simp only [mul_assoc,mul_inv_cancel,mul_one,ih,add_zero]
    rw [hω]
    ring

lemma integral_reduction {u v : Word A} (h : FreeGroup.Red.Step u v) (g : G) :
    integral φ ω g u=integral φ ω g v := by
  cases h with
  | not =>
    simp only [integral_append,integral_cons,      letter_flip,mul_assoc,mul_inv_cancel,mul_one,mul_one]
    rw [hω]
    ring

variable {R : Set (Word A)}
include hω
lemma move_bound (hv : ∀ w ∈ R, value φ w=1) (D : ℝ)
    (hD : ∀ g w, w∈R → |integral φ ω g w| ≤ D)
    {u v : Word A} {n : ℕ} (h : Move R u v n) (g : G) :
    |integral φ ω g u-integral φ ω g v| ≤ n*D := by
  cases h with
  | free h => simp [integral_reduction φ ω hω h g]
  | face l r w hw =>
    simp only [integral_append,value_append,hv w hw,mul_one,Nat.cast_one,one_mul]
    convert hD (g*value φ l) w hw using 1; congr 1; ring
  | reverseFace l r w hw =>
    have hh : integral φ ω (g*value φ l) (FreeGroup.invRev w) =
        -integral φ ω (g*value φ l) w := by
      simpa only [hv w hw,mul_one] using integral_reverse φ ω hω (g*value φ l) w
    simp only [integral_append,value_append,value_reverse,hv w hw,inv_one,mul_one,
      Nat.cast_one,one_mul,hh]
    convert hD (g*value φ l) w hw using 1
    rw [show integral φ ω g l + -integral φ ω (g*value φ l) w + integral φ ω (g*value φ l) r -
      (integral φ ω g l+integral φ ω (g*value φ l) r) = -integral φ ω (g*value φ l) w by ring,
      abs_neg]

lemma homotopy_bound (hv : ∀ w ∈ R, value φ w=1) (D : ℝ) (_ : 0 ≤ D)
    (hD : ∀ g w, w∈R → |integral φ ω g w| ≤ D)
    {u v : Word A} {n : ℕ} (h : Homotopy R u v n) (g : G) :
    |integral φ ω g u-integral φ ω g v| ≤ n*D := by
  induction h with
  | refl => simp
  | move h => exact move_bound φ ω hω hv D hD h g
  | symm h ih => simpa only [abs_sub_comm] using ih
  | trans h h' ih ih' =>
    calc
      _ ≤ |integral φ ω g _-integral φ ω g _| +
          |integral φ ω g _-integral φ ω g _| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add ih ih'
      _ = _ := by push_cast; ring

end Cochain
end WordPictures

/-! Finite unit-speed vertex paths; all indices are bounded explicitly. -/
section
open Finset
structure VertexPath (X : Type*) where
  length : ℕ
  point : ℕ → X
namespace VertexPath
variable {X : Type*}
def start (p : VertexPath X) := p.point 0
def finish (p : VertexPath X) := p.point p.length
def integral (p : VertexPath X) (ω : X → X → ℝ) : ℝ :=
  ∑ i ∈ range p.length, ω (p.point i) (p.point (i+1))
def reverse (p : VertexPath X) : VertexPath X := ⟨p.length,fun i => p.point (p.length-i)⟩
def sub (p : VertexPath X) (i j : ℕ) : VertexPath X := ⟨j-i,fun k => p.point (i+k)⟩
def append (p q : VertexPath X) : VertexPath X :=
  ⟨p.length+q.length,fun i => if i  ≤  p.length then p.point i else q.point (i-p.length)⟩
@[simp] lemma reverse_length (p : VertexPath X) : p.reverse.length=p.length := rfl
@[simp] lemma reverse_at (p : VertexPath X) (i : ℕ) : p.reverse.point i=p.point (p.length-i) := rfl
@[simp] lemma reverse_start (p : VertexPath X) : p.reverse.start=p.finish := by simp [start,finish]
@[simp] lemma reverse_finish (p : VertexPath X) : p.reverse.finish=p.start := by simp [start,finish]
@[simp] lemma sub_length (p : VertexPath X) (i j : ℕ) : (p.sub i j).length=j-i := rfl
@[simp] lemma sub_at (p : VertexPath X) (i j k : ℕ) : (p.sub i j).point k=p.point (i+k) := rfl
@[simp] lemma sub_start (p : VertexPath X) (i j : ℕ) : (p.sub i j).start=p.point i := by simp [start]
lemma sub_finish (p : VertexPath X) {i j : ℕ} (hij : i ≤ j) : (p.sub i j).finish=p.point j := by
  simp [finish,Nat.add_sub_of_le hij]
@[simp] lemma append_length (p q : VertexPath X) : (p.append q).length=p.length+q.length := rfl
lemma append_at_left (p q : VertexPath X) {i : ℕ} (hi : i ≤ p.length) :
    (p.append q).point i=p.point i := ite_eq_left hi
lemma append_at_right (p q : VertexPath X) (h : p.finish=q.start) (j : ℕ) :
    (p.append q).point (p.length+j)=q.point j := by
  by_cases hj : j=0
  · simpa [hj,append,finish,start] using h
  · simp [append,show ¬p.length+j ≤ p.length by omega]
@[simp] lemma append_start (p q : VertexPath X) : (p.append q).start=p.start := by
  simp [start,append]
lemma append_finish (p q : VertexPath X) (h : p.finish=q.start) :
    (p.append q).finish=q.finish := append_at_right p q h _
lemma integral_append (p q : VertexPath X) (h : p.finish=q.start) (ω : X→X→ℝ) :
    (p.append q).integral ω=p.integral ω+q.integral ω := by
  unfold integral
  rw [append_length,Finset.sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro i hi
    rw [append_at_left p q (by simpa using le_of_lt (mem_range.mp hi)),
      append_at_left p q (by simpa [Nat.add_one_le_iff] using mem_range.mp hi)]
  · apply sum_congr rfl
    intro i hi
    rw [append_at_right p q h,show p.length+i+1=p.length+(i+1) by omega,
      append_at_right p q h]
lemma integral_reverse (p : VertexPath X) (ω : X→X→ℝ)
    (hω : ∀ x y, ω x y = -ω y x) : p.reverse.integral ω= -p.integral ω := by
  unfold integral
  rw [reverse_length,←Finset.sum_range_reflect (fun i => ω (p.reverse.point i) (p.reverse.point (i+1)))]
  simp only [reverse_at,←Finset.sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  have hi := mem_range.mp hi
  rw [show p.length-(p.length-1-i)=i+1 by omega,
    show p.length-(p.length-1-i+1)=i by omega]
  exact hω _ _

variable [MetricSpace X]
def Unit (p : VertexPath X) : Prop := ∀ i<p.length, dist (p.point i) (p.point (i+1))  ≤  1
def Quasi (p : VertexPath X) (c : ℝ) : Prop :=
  ∀ i ≤ p.length, ∀ j ≤ p.length, |(i:ℝ)-j|  ≤  c*dist (p.point i) (p.point j)
def Geodesic (p : VertexPath X) : Prop :=
  ∀ i ≤ p.length, ∀ j ≤ p.length, dist (p.point i) (p.point j)=|(i:ℝ)-j|
lemma unit_sub {p : VertexPath X} (hp : p.Unit) {i j : ℕ} (hj : j ≤ p.length) :
    (p.sub i j).Unit := by
  intro k hk
  change dist (p.point (i+k)) (p.point (i+(k+1)))  ≤  1
  rw [←Nat.add_assoc]
  exact hp _ (by change k<j-i at hk; omega)
lemma unit_reverse {p : VertexPath X} (hp : p.Unit) : p.reverse.Unit := by
  intro i hi
  change dist (p.point (p.length-i)) (p.point (p.length-(i+1)))  ≤  1
  rw [dist_comm,show p.length-i=p.length-(i+1)+1 by change i<p.length at hi; omega]
  exact hp _ (by change i<p.length at hi; omega)
lemma unit_append {p q : VertexPath X} (hp : p.Unit) (hq : q.Unit)
    (h : p.finish=q.start) : (p.append q).Unit := by
  intro i hi
  by_cases hip : i<p.length
  · rw [append_at_left p q (le_of_lt hip),append_at_left p q (by omega)]
    exact hp i hip
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (show p.length ≤ i by omega)
    rw [append_at_right p q h,show p.length+j+1=p.length+(j+1) by omega,
      append_at_right p q h]
    exact hq j (by change p.length+j<p.length+q.length at hi; omega)
lemma dist_le {p : VertexPath X} (hp : p.Unit) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    dist (p.point i) (p.point j)  ≤  (j:ℝ)-i := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero => simp
  | succ k ih =>
    have htri := dist_triangle (p.point i) (p.point (i+k)) (p.point (i+(k+1)))
    have hstep := hp (i+k) (by omega)
    have hrec := ih (by omega) (by omega)
    rw [←Nat.add_assoc] at htri
    simp only [Nat.add_assoc] at htri hstep
    push_cast at *
    linarith
lemma dist_le_abs {p : VertexPath X} (hp : p.Unit) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) : dist (p.point i) (p.point j)  ≤  |(i:ℝ)-j| := by
  rcases le_total i j with hij|hji
  · rw [abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (i:ℝ) ≤ j by exact_mod_cast hij))]
    linarith [dist_le hp hij hj]
  · rw [dist_comm,abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr (show (j:ℝ) ≤ i by exact_mod_cast hji))]
    exact dist_le hp hji hi
lemma geodesic_of_end {p : VertexPath X} (hp : p.Unit)
    (h : dist p.start p.finish=p.length) : p.Geodesic := by
  have hh : ∀ i ≤ p.length, ∀ j ≤ p.length, i ≤ j →
      dist (p.point i) (p.point j)=(j:ℝ)-i := by
    intro i hi j hj hij
    apply le_antisymm (dist_le hp hij hj)
    have h1:=dist_le hp (Nat.zero_le i) hi
    have h2:=dist_le hp hj (le_refl _)
    have ht:=dist_triangle4 (p.point 0) (p.point i) (p.point j) (p.point p.length)
    change dist (p.point 0) (p.point p.length)=(p.length:ℝ) at h
    simp only [Nat.cast_zero,sub_zero] at h1
    linarith
  intro i hi j hj
  rcases le_total i j with hij|hji
  · rw [hh i hi j hj hij,abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (i:ℝ) ≤ j by exact_mod_cast hij))]; ring
  · rw [dist_comm,hh j hj i hi hji,abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr (show (j:ℝ) ≤ i by exact_mod_cast hji))]
lemma geodesic_unit {p : VertexPath X} (hp : p.Geodesic) : p.Unit := by
  intro i hi
  rw [hp i (by omega) (i+1) (by omega)]
  norm_num
lemma geodesic_quasi {p : VertexPath X} (hp : p.Geodesic) {c : ℝ} (hc : 1 ≤ c) : p.Quasi c := by
  intro i hi j hj
  rw [hp i hi j hj]
  exact le_mul_of_one_le_left (abs_nonneg _) hc

end VertexPath
end

namespace WordPictures.Cochain
variable {A G : Type*} [Group G]
variable (φ : FreeGroup A →* G)
def path (g : G) (w : Word A) : VertexPath G :=
  ⟨w.length,fun i => g*value φ (w.take i)⟩
@[simp] lemma path_length (g : G) (w : Word A) : (path φ g w).length=w.length := rfl
@[simp] lemma path_point_zero (g : G) (w : Word A) : (path φ g w).point 0=g := by simp [path]
@[simp] lemma path_start (g : G) (w : Word A) : (path φ g w).start=g := path_point_zero φ g w
@[simp] lemma path_finish (g : G) (w : Word A) : (path φ g w).finish=g*value φ w := by
  simp [VertexPath.finish,path]
lemma path_cons_succ (g : G) (a : A×Bool) (w : Word A) (i : ℕ) :
    (path φ g (a::w)).point (i+1)=(path φ (g*letter φ a) w).point i := by
  simp only [path,List.take_succ_cons,value_cons,mul_assoc]
lemma path_integral (ω : G→G→ℝ) (g : G) (w : Word A) :
    (path φ g w).integral ω=integral φ ω g w := by
  induction w generalizing g with
  | nil => simp [VertexPath.integral,path]
  | cons a w ih =>
    simp only [VertexPath.integral,path_length,List.length_cons,Finset.sum_range_succ']
    simp only [path_cons_succ,path_point_zero,integral_cons]
    rw [show (∑ i∈Finset.range w.length,
      ω ((path φ (g*letter φ a) w).point i) ((path φ (g*letter φ a) w).point (i+1))) =
      (path φ (g*letter φ a) w).integral ω from rfl,ih]
    exact add_comm _ _

variable (S : Finset G) (hS : Subgroup.closure (S : Set G)=⊤)
variable [MetricSpace G] (hd : ∀ x y : G, dist x y=WordDistance S x y)
include hS hd
omit hS in
lemma path_unit (H : ∀ a, WordLength S (letter φ a) ≤ 1) (g : G) (w : Word A) :
    (path φ g w).Unit := by
  induction w generalizing g with
  | nil => intro i hi; simp at hi
  | cons a w ih =>
    intro i hi
    cases i with
    | zero =>
      rw [path_point_zero,path_cons_succ,path_point_zero]
      rw [hd]
      change (WordLength S (g⁻¹*(g*letter φ a)) : ℝ) ≤ 1
      simp only [inv_mul_cancel_left]
      exact_mod_cast H a
    | succ i =>
      rw [path_cons_succ,path_cons_succ]
      exact ih (g*letter φ a) i (by simpa using hi)

lemma edge_letter (H : ∀ a∈S, ∃ b : A, φ (FreeGroup.of b)=a)
    {x y : G} (h : dist x y ≤ 1) :
    x=y ∨ ∃ a : A×Bool, y=x*letter φ a := by
  rw [hd] at h
  change (WordLength S (x⁻¹*y):ℝ) ≤ 1 at h
  have hn : WordLength S (x⁻¹*y) ≤ 1 := by exact_mod_cast h
  obtain ⟨w,hw,hgood,he⟩ := WordLength.attained S hS (x⁻¹*y)
  have hwlen : w.length ≤ 1 := hw ▸ hn
  cases w with
  | nil => left; exact inv_mul_eq_one.mp (by simpa using he.symm)
  | cons a w =>
    have hw0 : w=[] := List.length_eq_zero_iff.mp (by simpa using hwlen)
    subst w
    have ha:=hgood a (by simp)
    simp only [List.prod_cons,List.prod_nil,mul_one] at he
    right
    rcases ha with ha|ha
    · obtain ⟨b,hb⟩:=H a ha
      refine ⟨(b,true),?_⟩
      have hletter : letter φ (b,true)=a := hb
      rw [hletter,he,mul_inv_cancel_left]
    · obtain ⟨b,hb⟩:=H a⁻¹ ha
      refine ⟨(b,false),?_⟩
      have hletter : letter φ (b,false)=a := by
        have hh:=letter_flip φ b true
        simpa only [Bool.not_true,show letter φ (b,true)=a⁻¹ from hb,inv_inv] using hh
      rw [hletter,he,mul_inv_cancel_left]

lemma represent_path (H : ∀ a∈S, ∃ b : A, φ (FreeGroup.of b)=a)
    (ω : G→G→ℝ) (hω : ∀ x, ω x x=0) (p : VertexPath G) (hp : p.Unit) :
    ∃ w : Word A, w.length ≤ p.length ∧ p.start*value φ w=p.finish ∧
      integral φ ω p.start w=p.integral ω := by
  have aux : ∀ (n : ℕ) (v : ℕ→G), (∀ i<n, dist (v i) (v (i+1)) ≤ 1) →
      ∃ w : Word A, w.length ≤ n ∧ v 0*value φ w=v n ∧
        integral φ ω (v 0) w=∑ i∈Finset.range n, ω (v i) (v (i+1)) := by
    intro n
    induction n with
    | zero => intro v hv; exact ⟨[],by simp,by simp,by simp⟩
    | succ n ih =>
      intro v hv
      obtain ⟨w,hw,hend,hint⟩:=ih v (fun i hi => hv i (by omega))
      rcases edge_letter φ S hS hd H (hv n (by omega)) with he|⟨a,ha⟩
      · refine ⟨w,by omega,hend.trans he,?_⟩
        rw [Finset.sum_range_succ,←hint,←he,hω,add_zero]
      · refine ⟨w++[a],by simp; omega,?_,?_⟩
        · simpa only [value_append,←mul_assoc,hend,letter] using ha.symm
        · rw [integral_append,hend,integral_cons,integral_nil,hint,Finset.sum_range_succ,←ha,
            add_zero]
  exact aux p.length p.point hp

omit hS hd in
omit [MetricSpace G] in
lemma represent_good (H : ∀ a∈S, ∃ b : A, φ (FreeGroup.of b)=a)
    (w : List G) (hw : WordLength.Good S w) :
    ∃ v : Word A, v.length=w.length ∧ value φ v=w.prod := by
  induction w with
  | nil => exact ⟨[],rfl,value_nil φ⟩
  | cons a w ih =>
    obtain ⟨v,hv,hprod⟩:=ih (fun b hb => hw b (List.mem_cons_of_mem a hb))
    have ha:=hw a (by simp)
    have hh : ∃ b : A×Bool, letter φ b=a := by
      rcases ha with ha|ha
      · obtain ⟨b,hb⟩:=H a ha
        exact ⟨(b,true),hb⟩
      · obtain ⟨b,hb⟩:=H a⁻¹ ha
        refine ⟨(b,false),?_⟩
        have hh:=letter_flip φ b true
        simpa only [Bool.not_true,show letter φ (b,true)=a⁻¹ from hb,inv_inv] using hh
    obtain ⟨b,hb⟩:=hh
    exact ⟨b::v,by simp [hv],by simp [hb,hprod]⟩

lemma geodesic_exists (H : ∀ a∈S, ∃ b : A, φ (FreeGroup.of b)=a)
    (Hstep : ∀ a, WordLength S (letter φ a) ≤ 1) (x y : G) :
    ∃ p : VertexPath G, p.start=x ∧ p.finish=y ∧ p.Geodesic := by
  obtain ⟨w,hlen,hgood,hprod⟩:=WordLength.attained S hS (x⁻¹*y)
  obtain ⟨v,hv,hvprod⟩:=represent_good φ S H w hgood
  let p:=path φ x v
  have hp:=path_unit φ S hd Hstep x v
  have hs : p.start=x := path_start φ x v
  have he : p.finish=y := by simp [p,hvprod,hprod]
  refine ⟨p,hs,he,VertexPath.geodesic_of_end hp ?_⟩
  rw [hs,he,hd]
  change (WordLength S (x⁻¹*y):ℝ)=v.length
  rw [hv,hlen]

end WordPictures.Cochain

section
open Finset
open scoped NNReal
namespace VertexPath
variable {X : Type*} [MetricSpace X]
def tentWeight (f u : X→ℝ) (x y : X) : ℝ :=
  (f x+f y)/2*(u y-u x)
omit [MetricSpace X] in
lemma tentWeight_antisymm (f u : X→ℝ) (x y : X) :
    tentWeight f u x y= -tentWeight f u y x := by unfold tentWeight; ring
omit [MetricSpace X] in
lemma integral_shift (p : VertexPath X) (f u : X→ℝ) (c : ℝ) :
    p.integral (tentWeight (fun x => f x-c) u)=p.integral (tentWeight f u)-
      c*(u p.finish-u p.start) := by
  have he : ∀ i, tentWeight (fun x => f x-c) u (p.point i) (p.point (i+1)) =
      tentWeight f u (p.point i) (p.point (i+1)) - c*(u (p.point (i+1))-u (p.point i)) := by
    intro i; unfold tentWeight; ring
  simp only [integral,he]
  rw [sum_sub_distrib,←mul_sum,Finset.sum_range_sub (fun i => u (p.point i))]
  rfl

lemma quadratic_bound (p : VertexPath X) (hp : p.Unit) (hc : p.finish=p.start)
    (f u : X→ℝ) {K : ℝ≥0} (hf : LipschitzWith 1 f) (hu : LipschitzWith K u) :
    |p.integral (tentWeight f u)| ≤ K*(p.length:ℝ)^2 := by
  have hs:=integral_shift p f u (f p.start)
  rw [hc,sub_self,mul_zero,sub_zero] at hs
  rw [←hs]
  let F := fun x => f x-f p.start
  have hb : ∀ i ≤ p.length, |F (p.point i)| ≤ p.length := by
    intro i hi
    have hh:=hf.dist_le_mul (p.point i) p.start
    have hd:=dist_le hp (Nat.zero_le i) hi
    simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hh
    dsimp only [F]
    simp only [Nat.cast_zero,sub_zero] at hd
    rw [dist_comm] at hd
    have hiR : (i:ℝ) ≤ p.length := by exact_mod_cast hi
    exact hh.trans (by change dist (p.point i) (p.point 0) ≤ _; linarith)
  have he : ∀ i∈range p.length,
      |tentWeight F u (p.point i) (p.point (i+1))| ≤ K*p.length := by
    intro i hi
    have hi:=mem_range.mp hi
    have h1:=hb i (by omega)
    have h2:=hb (i+1) (by omega)
    have h3:=hu.dist_le_mul (p.point (i+1)) (p.point i)
    have h4:=hp i hi
    rw [dist_comm] at h4
    simp only [Real.dist_eq] at h3
    have hu' : |u (p.point (i+1))-u (p.point i)| ≤ K := by
      exact h3.trans (by simpa using mul_le_mul_of_nonneg_left h4 K.coe_nonneg)
    unfold tentWeight
    rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ ((|F (p.point i)|+|F (p.point (i+1))|)/2)*|u (p.point (i+1))-u (p.point i)| := by
        gcongr; exact abs_add_le _ _
      _ ≤ (((p.length:ℝ)+p.length)/2)*K := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ i∈range p.length, |tentWeight F u (p.point i) (p.point (i+1))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i∈range p.length, (K:ℝ)*p.length := sum_le_sum he
    _ = _ := by simp; ring

end VertexPath
end
section

open scoped NNReal
/-- A quantitative consequence of actual linear word filling, tested by
Lipschitz cochains. This property makes no geometric conclusion an assumption. -/
def CochainLinear (X : Type*) [MetricSpace X] (K : ℝ) : Prop :=
  ∀ p : VertexPath X, p.Unit → p.finish=p.start → ∀ f u : X→ℝ,
    LipschitzWith 1 f → LipschitzWith 3 u →
    |p.integral (VertexPath.tentWeight f u)| ≤ K*p.length
namespace WordPictures.Cochain
variable {A G : Type*} [Group G] [MetricSpace G]
variable (φ : FreeGroup A →* G) (S : Finset G)
    (hS : Subgroup.closure (S : Set G)=⊤)
    (hd : ∀ x y : G, dist x y=WordDistance S x y)

include hS hd
lemma linear_of_filling {R : Set (Word A)} {C : ℝ} (hC : 0 ≤ C) {L : ℕ}
    (H : ∀ a∈S, ∃ b : A, φ (FreeGroup.of b)=a)
    (Hstep : ∀ a, WordLength S (letter φ a) ≤ 1)
    (hv : ∀ w∈R, value φ w=1) (hL : ∀ w∈R, w.length ≤ L)
    (hfill : ∀ w, value φ w=1 → ∃ a, Homotopy R w [] a ∧ (a:ℝ) ≤ C*w.length) :
    CochainLinear G (3*(L:ℝ)^2*C) := by
  intro p hp hc f u hf hu
  let ω:=VertexPath.tentWeight f u
  have hω : ∀ x y, ω x y= -ω y x := VertexPath.tentWeight_antisymm f u
  have hω0 : ∀x, ω x x=0 := by intro x; simp [ω,VertexPath.tentWeight]
  have hD : ∀ g w, w∈R → |integral φ ω g w| ≤ 3*(L:ℝ)^2 := by
    intro g w hw
    have huPath:=path_unit φ S hd Hstep g w
    have hcPath : (path φ g w).finish=(path φ g w).start := by simp [hv w hw]
    have hb:=VertexPath.quadratic_bound (path φ g w) huPath hcPath f u hf hu
    rw [path_integral,path_length] at hb
    apply hb.trans
    have hle : (w.length:ℝ) ≤ L := by exact_mod_cast hL w hw
    norm_num only [NNReal.coe_ofNat] at *
    gcongr
  obtain ⟨w,hlen,hend,hint⟩:=represent_path φ S hS hd H ω hω0 p hp
  have he : value φ w=1 := by
    apply mul_left_cancel (a:=p.start)
    simpa only [mul_one,hc] using hend
  obtain ⟨a,ha,harea⟩:=hfill w he
  have hb:=homotopy_bound φ ω hω hv (3*(L:ℝ)^2) (by positivity) hD ha p.start
  simp only [integral_nil,sub_zero,hint] at hb
  have hlenR : (w.length:ℝ) ≤ p.length := by exact_mod_cast hlen
  have harea' : (a:ℝ) ≤ C*p.length := harea.trans (mul_le_mul_of_nonneg_left hlenR hC)
  calc
    _ ≤ (a:ℝ)*(3*(L:ℝ)^2) := hb
    _ ≤ (C*p.length)*(3*(L:ℝ)^2) := mul_le_mul_of_nonneg_right harea' (by positivity)
    _ = _ := by ring

end WordPictures.Cochain
end

namespace VertexPath

section
open Finset Set
open scoped NNReal
variable {X : Type*} [MetricSpace X]
lemma quasi_injective {p : VertexPath X} {c : ℝ} (hp : p.Quasi c) :
    Function.Injective (fun i : Fin (p.length+1) => p.point i) := by
  intro i j he
  dsimp only at he
  have hh:=hp i (by omega) j (by omega)
  rw [he,dist_self,mul_zero] at hh
  have hh0:=abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  apply Fin.ext
  exact_mod_cast sub_eq_zero.mp hh0
lemma quasi_extension {p : VertexPath X} {c : ℝ≥0} (hp : p.Quasi c) :
    ∃ u : X→ℝ, LipschitzWith c u ∧ ∀ i ≤ p.length, u (p.point i)=i := by
  let P : Fin (p.length+1)→X:=fun i => p.point i
  let v : X→ℝ:=fun x => (Function.invFun P x).val
  have hP:=quasi_injective hp
  have hv : ∀ i : Fin (p.length+1), v (P i)=i.val := by
    intro i
    dsimp only [v]
    rw [Function.leftInverse_invFun hP]
  have hvl : LipschitzOnWith c v (Set.range P) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    rw [hv,hv,Real.dist_eq]
    exact hp i (by omega) j (by omega)
  obtain ⟨u,hu,he⟩:=hvl.extend_real
  refine ⟨u,hu,fun i hi => ?_⟩
  exact (he ⟨⟨i,by omega⟩,rfl⟩).symm.trans (hv ⟨i,by omega⟩)

lemma tent_lipschitz (b : X) (R : ℝ) :
    LipschitzWith 1 (fun x => max 0 (R-dist b x)) := by
  apply LipschitzWith.const_max
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  rw [show R-dist b x-(R-dist b y)=dist b y-dist b x by ring]
  simpa only [dist_comm] using abs_dist_sub_le y x b

lemma nearest (p : VertexPath X) (x : X) :
    ∃ i ≤ p.length, ∀ j ≤ p.length, dist x (p.point i) ≤ dist x (p.point j) := by
  obtain ⟨i,hi,hmin⟩:=Finset.exists_min_image (Finset.range (p.length+1))
    (fun i => dist x (p.point i)) (by simp)
  exact ⟨i,by simpa using hi,fun j hj => hmin j (by simpa using hj)⟩

lemma maximum_nearest (p q : VertexPath X)
    (hint : ∀ x y : X, ∃ n : ℕ, dist x y=n) :
    ∃ k ≤ p.length, ∃ R : ℕ,
      (∀ j ≤ q.length, (R:ℝ) ≤ dist (p.point k) (q.point j)) ∧
      (∀ i ≤ p.length, ∃ j ≤ q.length, dist (p.point i) (q.point j) ≤ R) := by
  choose j hj hmin using fun i : ℕ => nearest q (p.point i)
  obtain ⟨k,hk,hmax⟩:=Finset.exists_max_image (Finset.range (p.length+1))
    (fun i => dist (p.point i) (q.point (j i))) (by simp)
  obtain ⟨R,hR⟩:=hint (p.point k) (q.point (j k))
  refine ⟨k,by simpa using hk,R,?_,?_⟩
  · intro t ht
    rw [←hR]
    exact hmin k t ht
  · intro i hi
    exact ⟨j i,hj i,hR ▸ hmax i (by simpa using hi)⟩

lemma geodesic_length {p : VertexPath X} (hp : p.Geodesic) :
    dist p.start p.finish=p.length := by simpa [start,finish] using hp 0 (by omega) p.length (le_refl _)
lemma geodesic_sub {p : VertexPath X} (hp : p.Geodesic) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    (p.sub i j).Geodesic := by
  intro k hk l hl
  change dist (p.point (i+k)) (p.point (i+l))=|(k:ℝ)-l|
  rw [hp _ (by change k ≤ j-i at hk; omega) _ (by change l ≤ j-i at hl; omega)]
  push_cast
  congr 1
  ring
lemma quasi_reverse {p : VertexPath X} {c : ℝ} (hp : p.Quasi c) : p.reverse.Quasi c := by
  intro i hi j hj
  have hi' : i ≤ p.length := hi
  have hj' : j ≤ p.length := hj
  have hh:=hp (p.length-i) (by omega) (p.length-j) (by omega)
  rw [Nat.cast_sub hi',Nat.cast_sub hj',show (p.length:ℝ)-i-(p.length-j)= -((i:ℝ)-j) by ring,
    abs_neg] at hh
  exact hh

end

section
open Finset
variable {X : Type*} [MetricSpace X]
omit [MetricSpace X] in
lemma integral_sub_eq (p : VertexPath X) (ω : X→X→ℝ) (s t : ℕ) :
    (p.sub s t).integral ω=∑ i∈Ico s t, ω (p.point i) (p.point (i+1)) := by
  rw [sum_Ico_eq_sum_range]
  simp only [integral,sub_length,sub_at,Nat.add_assoc]
omit [MetricSpace X] in
lemma integral_sub_mono (p : VertexPath X) (ω : X→X→ℝ) {a b s t : ℕ}
    (hsa : s ≤ a) (hbt : b ≤ t)
    (hω : ∀ i∈Ico s t, 0 ≤ ω (p.point i) (p.point (i+1))) :
    (p.sub a b).integral ω ≤ (p.sub s t).integral ω := by
  rw [integral_sub_eq,integral_sub_eq]
  apply sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [mem_Ico] at *
    omega
  · intro i hi _
    exact hω i hi
omit [MetricSpace X] in
lemma integral_tent_zero (p : VertexPath X) (f u : X→ℝ)
    (hf : ∀ i ≤ p.length, f (p.point i)=0) : p.integral (tentWeight f u)=0 := by
  apply sum_eq_zero
  intro i hi
  have hi:=mem_range.mp hi
  simp [tentWeight,hf i (by omega),hf (i+1) (by omega)]
lemma arithmetic_tent_sum (n : ℕ) :
    (∑ i∈range n, ((n:ℝ)-i-1/2))=(n:ℝ)^2/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have he : ∀ i, ((n+1:ℕ):ℝ)-i-1/2=((n:ℝ)-i-1/2)+1 := by intro i; push_cast; ring
    simp only [he,sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one,ih]
    push_cast
    ring

/-- A tent centered on a long unit path sees a quadratic amount of integral.
The coordinate function is the actual Lipschitz index extension. -/
lemma integral_tent_lower (p : VertexPath X) (hp : p.Unit) (u : X→ℝ)
    (hu : ∀ i ≤ p.length, u (p.point i)=i) {R k s t : ℕ}
    (hs : s ≤ k) (ht : k+R ≤ t) (htp : t ≤ p.length) :
    (R:ℝ)^2/2 ≤ (p.sub s t).integral (tentWeight
      (fun x => max 0 ((R:ℝ)-dist (p.point k) x)) u) := by
  let f:=fun x => max 0 ((R:ℝ)-dist (p.point k) x)
  have hn : ∀ i∈Ico s t, 0 ≤ tentWeight f u (p.point i) (p.point (i+1)) := by
    intro i hi
    have hi:=mem_Ico.mp hi
    unfold tentWeight
    rw [hu i (by omega),hu (i+1) (by omega)]
    have he : ((i+1:ℕ):ℝ)-(i:ℝ)=1 := by simp
    rw [he,mul_one]
    exact div_nonneg (add_nonneg (le_max_left _ _) (le_max_left _ _)) (by norm_num)
  have hb : ∀ i ≤ R, (R:ℝ)-i ≤ f (p.point (k+i)) := by
    intro i hi
    have hd:=dist_le hp (show k ≤ k+i by omega) (show k+i ≤ p.length by omega)
    have hm:=le_max_right (0:ℝ) ((R:ℝ)-dist (p.point k) (p.point (k+i)))
    dsimp only [f]
    push_cast at hd
    linarith
  have hsmall : (R:ℝ)^2/2 ≤ (p.sub k (k+R)).integral (tentWeight f u) := by
    rw [integral,sub_length,Nat.add_sub_cancel_left,←arithmetic_tent_sum R]
    apply sum_le_sum
    intro i hi
    have hi:=mem_range.mp hi
    simp only [sub_at,tentWeight]
    rw [hu (k+i) (by omega),hu (k+(i+1)) (by omega)]
    have h1:=hb i (by omega)
    have h2:=hb (i+1) (by omega)
    push_cast at *
    nlinarith
  exact hsmall.trans (integral_sub_mono p (tentWeight f u) hs ht hn)

end

section
variable {X : Type*} [MetricSpace X]
def between (p : VertexPath X) (i j : ℕ) : VertexPath X :=
  if i ≤ j then p.sub i j else (p.sub j i).reverse
omit [MetricSpace X] in
lemma between_start (p : VertexPath X) (i j : ℕ) : (p.between i j).start=p.point i := by
  unfold between
  split_ifs with h
  · exact sub_start p i j
  · rw [reverse_start,sub_finish p (by omega)]
omit [MetricSpace X] in
lemma between_finish (p : VertexPath X) (i j : ℕ) : (p.between i j).finish=p.point j := by
  unfold between
  split_ifs with h
  · exact sub_finish p h
  · rw [reverse_finish,sub_start]
lemma between_unit {p : VertexPath X} (hp : p.Unit) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) : (p.between i j).Unit := by
  unfold between
  split_ifs
  · exact unit_sub hp hj
  · exact unit_reverse (unit_sub hp hi)
omit [MetricSpace X] in
lemma between_length_real (p : VertexPath X) (i j : ℕ) :
    ((p.between i j).length:ℝ)=|(i:ℝ)-j| := by
  unfold between
  split_ifs with h
  · rw [sub_length,Nat.cast_sub h,abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (i:ℝ) ≤ j by exact_mod_cast h))]
    ring
  · rw [reverse_length,sub_length,Nat.cast_sub (by omega),abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr (show (j:ℝ) ≤ i by exact_mod_cast (show j ≤ i by omega))) ]
lemma between_length_le {p : VertexPath X} {c : ℝ} (hp : p.Quasi c) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) :
    ((p.between i j).length:ℝ) ≤ c*dist (p.point i) (p.point j) := by
  rw [between_length_real]
  exact hp i hi j hj
omit [MetricSpace X] in
lemma between_point (p : VertexPath X) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    {k : ℕ} (hk : k ≤ (p.between i j).length) :
    ∃ l ≤ p.length, (p.between i j).point k=p.point l := by
  unfold between at *
  split_ifs at * with h
  · exact ⟨i+k,by change k ≤ j-i at hk; omega,rfl⟩
  · exact ⟨j+(i-j-k),by change k ≤ i-j at hk; omega,rfl⟩

/-- A connector of length at most R stays outside the R-tent whenever its
initial vertex is 2R away, or is already on the comparison path. -/
lemma outside_connector
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    (q : VertexPath X) (b x : X) (R : ℝ) (hR : 0 ≤ R)
    (hq : ∀ j ≤ q.length, R ≤ dist b (q.point j))
    (hnear : ∃ j ≤ q.length, dist x (q.point j) ≤ R)
    (hfar : (∃ j ≤ q.length, x=q.point j) ∨ 2*R ≤ dist b x) :
    ∃ j ≤ q.length, ∃ c : VertexPath X,
      c.start=x ∧ c.finish=q.point j ∧ c.Unit ∧ (c.length:ℝ) ≤ R ∧
        ∀ i ≤ c.length, R ≤ dist b (c.point i) := by
  rcases hfar with ⟨j,hj,hx⟩|hfar
  · refine ⟨j,hj,⟨0,fun _ => x⟩,rfl,hx,?_,?_,?_⟩
    · intro i hi; exact (Nat.not_lt_zero i hi).elim
    · simpa using hR
    · intro i hi
      simpa only [hx] using hq j hj
  · obtain ⟨j,hj,hjR⟩:=hnear
    obtain ⟨c,hs,he,hc⟩:=hgeo x (q.point j)
    have hlen : (c.length:ℝ) ≤ R := by rw [←geodesic_length hc,hs,he]; exact hjR
    refine ⟨j,hj,c,hs,he,geodesic_unit hc,hlen,?_⟩
    intro i hi
    have hd:=dist_le (geodesic_unit hc) (Nat.zero_le i) hi
    have hiR : (i:ℝ) ≤ c.length := by exact_mod_cast hi
    have ht:=dist_triangle b (c.point i) x
    change c.point 0=x at hs
    simp only [Nat.cast_zero,sub_zero,hs] at hd
    rw [dist_comm (c.point i) x] at ht
    linarith

end

variable {X : Type*} [MetricSpace X]
lemma end_dist_le {p : VertexPath X} (hp : p.Unit) : dist p.start p.finish ≤ p.length := by
  simpa [start,finish] using dist_le hp (Nat.zero_le p.length) (le_refl _)

/-- Localized-loop proof of uniform Morse stability. The loop has length at
most 56R and its tent integral at least R²/2. -/
lemma cochain_morse_max {K : ℝ} (hK : 0 ≤ K) (hco : CochainLinear X K)
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    (p q : VertexPath X) (hp : p.Unit) (hqp : p.Quasi 3) (hq : q.Unit) (hqq : q.Quasi 3)
    (hstart : p.start=q.start) (hfinish : p.finish=q.finish)
    {k R : ℕ} (hk : k ≤ p.length)
    (hfarq : ∀ j ≤ q.length, (R:ℝ) ≤ dist (p.point k) (q.point j))
    (hnear : ∀ i ≤ p.length, ∃ j ≤ q.length, dist (p.point i) (q.point j) ≤ R) :
    (R:ℝ) ≤ 112*K := by
  let s:=k-6*R
  let t:=min p.length (k+6*R)
  have hs : s ≤ k := Nat.sub_le _ _
  have hslen : s ≤ p.length := hs.trans hk
  have htlen : t ≤ p.length := min_le_left _ _
  have hkt : k ≤ t := le_min hk (by omega)
  have hst : s ≤ t := hs.trans hkt
  have hkR : k+R ≤ p.length := by
    have hh:=hfarq q.length (le_refl _)
    have hd:=dist_le hp hk (le_refl _)
    change p.point p.length=q.point q.length at hfinish
    rw [←hfinish] at hh
    have hr : (k:ℝ)+R ≤ p.length := by linarith
    exact_mod_cast hr
  have hRt : k+R ≤ t := le_min hkR (by omega)
  have hslength : t-s ≤ 12*R := by dsimp only [s,t]; omega
  have hsfar : (∃ j ≤ q.length, p.point s=q.point j) ∨
      2*(R:ℝ) ≤ dist (p.point k) (p.point s) := by
    by_cases hs0 : s=0
    · left
      exact ⟨0,Nat.zero_le _,by simpa only [hs0,start] using hstart⟩
    · right
      have he : k=s+6*R := by dsimp only [s] at *; omega
      have her : (k:ℝ)=(s:ℝ)+6*R := by exact_mod_cast he
      have hh:=hqp k hk s hslen
      have ha:=le_abs_self ((k:ℝ)-s)
      linarith
  have htfar : (∃ j ≤ q.length, p.point t=q.point j) ∨
      2*(R:ℝ) ≤ dist (p.point k) (p.point t) := by
    by_cases hte : t=p.length
    · left
      exact ⟨q.length,le_refl _,by simpa only [hte,finish] using hfinish⟩
    · right
      have he : t=k+6*R := by
        change min p.length (k+6*R)=k+6*R
        by_cases hh : p.length ≤ k+6*R
        · exact False.elim (hte (min_eq_left hh))
        · exact min_eq_right (le_of_not_ge hh)
      have her : (t:ℝ)=(k:ℝ)+6*R := by exact_mod_cast he
      have hh:=hqp k hk t htlen
      have ha:=neg_le_abs ((k:ℝ)-t)
      linarith
  obtain ⟨js,hjs,cs,hcss,hcse,hcs,hcslen,hcsfar⟩:=
    outside_connector hgeo q (p.point k) (p.point s) R (Nat.cast_nonneg R)
      hfarq (hnear s hslen) hsfar
  obtain ⟨jt,hjt,ct,hcts,hcte,hct,hctlen,hctfar⟩:=
    outside_connector hgeo q (p.point k) (p.point t) R (Nat.cast_nonneg R)
      hfarq (hnear t htlen) htfar
  let a:=p.sub s t
  let b:=q.between jt js
  have haUnit : a.Unit:=unit_sub hp htlen
  have hbUnit : b.Unit:=between_unit hq hjt hjs
  have has : a.start=p.point s:=sub_start p s t
  have hae : a.finish=p.point t:=sub_finish p hst
  have hbs : b.start=q.point jt:=between_start q jt js
  have hbe : b.finish=q.point js:=between_finish q jt js
  have h1 : a.finish=ct.start:=hae.trans hcts.symm
  have h2 : (a.append ct).finish=b.start :=
    (append_finish a ct h1).trans (hcte.trans hbs.symm)
  have h3 : ((a.append ct).append b).finish=cs.reverse.start := by
    rw [append_finish _ _ h2,hbe,reverse_start,hcse]
  let loop:=((a.append ct).append b).append cs.reverse
  have hloop : loop.Unit:=unit_append (unit_append (unit_append haUnit hct h1) hbUnit h2)
    (unit_reverse hcs) h3
  have hclosed : loop.finish=loop.start := by
    rw [show loop.finish=cs.reverse.finish from append_finish _ _ h3,reverse_finish,hcss]
    simp only [loop,append_start,has]
  have haLen : (a.length:ℝ) ≤ 12*R := by exact_mod_cast hslength
  have hbLen : (b.length:ℝ) ≤ 3*((ct.length:ℝ)+a.length+cs.length) := by
    have hd:=dist_triangle4 (q.point jt) (p.point t) (p.point s) (q.point js)
    have hdct:=end_dist_le hct
    have hda:=end_dist_le haUnit
    have hdcs:=end_dist_le hcs
    rw [hcts,hcte,dist_comm] at hdct
    rw [has,hae,dist_comm] at hda
    rw [hcss,hcse] at hdcs
    have hh:=between_length_le hqq hjt hjs
    change (b.length:ℝ) ≤ _ at hh
    linarith
  have hlen : (loop.length:ℝ) ≤ 56*R := by
    simp only [loop,append_length,reverse_length,Nat.cast_add]
    linarith
  obtain ⟨u,hu,huindex⟩:=quasi_extension (c:=(3:NNReal)) hqp
  let f:=fun x => max 0 ((R:ℝ)-dist (p.point k) x)
  let ω:=tentWeight f u
  have hf : LipschitzWith 1 f:=tent_lipschitz _ _
  have hcs0 : cs.integral ω=0 := integral_tent_zero cs f u (fun i hi =>
    max_eq_left (sub_nonpos.mpr (hcsfar i hi)))
  have hct0 : ct.integral ω=0 := integral_tent_zero ct f u (fun i hi =>
    max_eq_left (sub_nonpos.mpr (hctfar i hi)))
  have hb0 : b.integral ω=0 := by
    apply integral_tent_zero b f u
    intro i hi
    obtain ⟨j,hj,hij⟩:=between_point q hjt hjs hi
    change max 0 ((R:ℝ)-dist (p.point k) (b.point i))=0
    rw [hij]
    exact max_eq_left (sub_nonpos.mpr (hfarq j hj))
  have hint : loop.integral ω=a.integral ω := by
    rw [show loop.integral ω=(((a.append ct).append b).integral ω+cs.reverse.integral ω)
      from integral_append _ _ h3 ω,
      integral_append _ _ h2,integral_append _ _ h1,
      integral_reverse cs ω (tentWeight_antisymm f u),hcs0,hct0,hb0]
    ring
  have hlo:=integral_tent_lower p hp u huindex hs hRt htlen
  change (R:ℝ)^2/2 ≤ a.integral ω at hlo
  have hupper:=hco loop hloop hclosed f u hf hu
  change |loop.integral ω| ≤ K*loop.length at hupper
  rw [hint] at hupper
  have hupp : a.integral ω ≤ K*(56*R) :=
    (le_abs_self _).trans (hupper.trans (mul_le_mul_of_nonneg_left hlen hK))
  have hR : 0 ≤ (R:ℝ):=Nat.cast_nonneg _
  by_cases hR0 : R=0
  · simp only [hR0,Nat.cast_zero]; positivity
  · have hRp : 0 < (R:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hR0
    nlinarith

lemma cochain_morse {K : ℝ} (hK : 0 ≤ K) (hco : CochainLinear X K)
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    (hint : ∀ x y : X, ∃ n : ℕ, dist x y=n)
    (p q : VertexPath X) (hp : p.Unit) (hqp : p.Quasi 3) (hq : q.Unit) (hqq : q.Quasi 3)
    (hstart : p.start=q.start) (hfinish : p.finish=q.finish) :
    ∀ i ≤ p.length, ∃ j ≤ q.length, dist (p.point i) (q.point j) ≤ 112*K := by
  obtain ⟨k,hk,R,hfar,hnear⟩:=maximum_nearest p q hint
  have hb:=cochain_morse_max hK hco hgeo p q hp hqp hq hqq hstart hfinish hk hfar hnear
  intro i hi
  obtain ⟨j,hj,hij⟩:=hnear i hi
  exact ⟨j,hj,hij.trans hb⟩

lemma geodesic_reverse {p : VertexPath X} (hp : p.Geodesic) : p.reverse.Geodesic := by
  apply geodesic_of_end (unit_reverse (geodesic_unit hp))
  rw [reverse_start,reverse_finish,dist_comm,geodesic_length hp,reverse_length]

/-- Joining at a nearest vertex produces a 3-quasigeodesic, with no additive
error. This avoids any planar-diagram or simple-boundary assumption. -/
lemma nearest_append_quasi {p q : VertexPath X} (hp : p.Geodesic) (hq : q.Geodesic)
    (he : p.finish=q.start)
    (hnear : ∀ i ≤ p.length, dist p.finish q.finish ≤ dist (p.point i) q.finish) :
    (p.append q).Quasi 3 := by
  have cross : ∀ i ≤ p.length, ∀ j ≤ q.length,
      (p.length:ℝ)-i+j ≤ 3*dist (p.point i) (q.point j) := by
    intro i hi j hj
    have h1:=dist_triangle (p.point i) (q.point j) q.finish
    have h2:=dist_triangle (p.point i) (q.point j) q.start
    have hn:=hnear i hi
    have hqp : dist q.start q.finish=q.length := geodesic_length hq
    have hjR : (j:ℝ) ≤ q.length := by exact_mod_cast hj
    have hiR : (i:ℝ) ≤ p.length := by exact_mod_cast hi
    have hqj : dist (q.point j) q.finish=(q.length:ℝ)-j := by
      rw [finish,hq j hj q.length (le_refl _),abs_of_nonpos (by linarith)]; ring
    have hjq : dist (q.point j) q.start=(j:ℝ) := by
      rw [start,hq j hj 0 (Nat.zero_le _),Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg _)]
    have hpi : dist (p.point i) q.start=(p.length:ℝ)-i := by
      rw [←he,finish,hp i hi p.length (le_refl _),abs_of_nonpos (by linarith)]; ring
    rw [he] at hn
    rw [hqp] at hn
    rw [hqj] at h1
    rw [hpi,hjq] at h2
    linarith
  have ordered : ∀ i ≤ (p.append q).length, ∀ j ≤ (p.append q).length, i ≤ j →
      (j:ℝ)-i ≤ 3*dist ((p.append q).point i) ((p.append q).point j) := by
    intro i hi j hj hij
    by_cases hip : i ≤ p.length
    · rw [append_at_left p q hip]
      by_cases hjp : j ≤ p.length
      · rw [append_at_left p q hjp,hp i hip j hjp,
          abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (i:ℝ) ≤ j by exact_mod_cast hij))]
        have : (i:ℝ) ≤ j := by exact_mod_cast hij
        linarith
      · obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le (show p.length ≤ j by omega)
        rw [append_at_right p q he]
        have hh:=cross i hip k (by change p.length+k ≤ p.length+q.length at hj; omega)
        push_cast
        linarith
    · obtain ⟨s,rfl⟩:=Nat.exists_eq_add_of_le (show p.length ≤ i by omega)
      obtain ⟨t,rfl⟩:=Nat.exists_eq_add_of_le (show p.length ≤ j by omega)
      have hs : s ≤ q.length := by change p.length+s ≤ p.length+q.length at hi; omega
      have ht : t ≤ q.length := by change p.length+t ≤ p.length+q.length at hj; omega
      rw [append_at_right p q he,append_at_right p q he,hq s hs t ht,
        abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (s:ℝ) ≤ t by exact_mod_cast (show s ≤ t by omega)))]
      push_cast
      have : (s:ℝ) ≤ t := by exact_mod_cast (show s ≤ t by omega)
      linarith
  intro i hi j hj
  rcases le_total i j with hij|hji
  · rw [abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (i:ℝ) ≤ j by exact_mod_cast hij))]
    linarith [ordered i hi j hj hij]
  · rw [abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr (show (j:ℝ) ≤ i by exact_mod_cast hji)),dist_comm]
    exact ordered j hj i hi hji

/-- Literal vertex thin triangles. -/
def ThinTriangles (X : Type*) [MetricSpace X] (D : ℝ) : Prop :=
  ∀ p q r : VertexPath X, p.Geodesic → q.Geodesic → r.Geodesic →
    p.start=q.start → p.finish=r.start → q.finish=r.finish →
    ∀ i ≤ p.length, (∃ j ≤ q.length, dist (p.point i) (q.point j) ≤ D) ∨
      (∃ j ≤ r.length, dist (p.point i) (r.point j) ≤ D)

lemma cochain_thin {K : ℝ} (hK : 0 ≤ K) (hco : CochainLinear X K)
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    (hint : ∀ x y : X, ∃ n : ℕ, dist x y=n) : ThinTriangles X (112*K) := by
  intro p q r hp hq hr hps hpe hqe i hi
  obtain ⟨k,hk,hmin⟩:=nearest p q.finish
  obtain ⟨s,hss,hse,hs⟩:=hgeo (p.point k) q.finish
  by_cases hik : i ≤ k
  · let a:=p.sub 0 k
    have ha : a.Geodesic:=geodesic_sub hp (Nat.zero_le _) hk
    have hae : a.finish=s.start := (sub_finish p (Nat.zero_le k)).trans hss.symm
    have hnear : ∀ j ≤ a.length, dist a.finish s.finish ≤ dist (a.point j) s.finish := by
      intro j hj
      rw [sub_finish p (Nat.zero_le k),hse,dist_comm (p.point k),dist_comm (a.point j)]
      simpa only [a,sub_at,Nat.zero_add] using hmin j (by change j ≤ k-0 at hj; omega)
    have hstart : (a.append s).start=q.start := by
      rw [append_start]; exact hps
    have hfinish : (a.append s).finish=q.finish := (append_finish a s hae).trans hse
    obtain ⟨j,hj,hij⟩:=cochain_morse hK hco hgeo hint (a.append s) q
      (unit_append (geodesic_unit ha) (geodesic_unit hs) hae)
      (nearest_append_quasi ha hs hae hnear) (geodesic_unit hq) (geodesic_quasi hq (by norm_num))
      hstart hfinish i (by change i ≤ (k-0)+s.length; omega)
    left
    refine ⟨j,hj,?_⟩
    simpa only [append_at_left a s (show i ≤ a.length by exact hik),a,sub_at,Nat.zero_add] using hij
  · let a:=(p.sub k p.length).reverse
    have ha : a.Geodesic:=geodesic_reverse (geodesic_sub hp hk (le_refl _))
    have hae : a.finish=s.start := by simp only [a,reverse_finish,sub_start]; exact hss.symm
    have hnear : ∀ j ≤ a.length, dist a.finish s.finish ≤ dist (a.point j) s.finish := by
      intro j hj
      simp only [a,reverse_finish,sub_start,reverse_at,sub_at,sub_length,hse]
      rw [dist_comm (p.point k),dist_comm (p.point _)]
      exact hmin _ (by omega)
    have hstart : (a.append s).start=r.start := by
      rw [append_start,show a.start=p.finish by
        exact (reverse_start (p.sub k p.length)).trans (sub_finish p hk)]
      exact hpe
    have hfinish : (a.append s).finish=r.finish := (append_finish a s hae).trans (hse.trans hqe)
    let j:=p.length-i
    have hj : j ≤ a.length := by change p.length-i ≤ p.length-k; omega
    obtain ⟨l,hl,hil⟩:=cochain_morse hK hco hgeo hint (a.append s) r
      (unit_append (geodesic_unit ha) (geodesic_unit hs) hae)
      (nearest_append_quasi ha hs hae hnear) (geodesic_unit hr) (geodesic_quasi hr (by norm_num))
      hstart hfinish j (hj.trans (Nat.le_add_right _ _))
    right
    refine ⟨l,hl,?_⟩
    rw [append_at_left a s hj] at hil
    simpa only [a,reverse_at,sub_at,sub_length,j,show k+(p.length-k-(p.length-i))=i by omega] using hil

def product (o x y : X) : ℝ := (dist o x+dist o y-dist x y)/2
lemma product_nonneg (o x y : X) : 0 ≤ product o x y := by
  have h:=dist_triangle x o y
  rw [dist_comm x o] at h
  unfold product; linarith
lemma product_le_left (o x y : X) : product o x y ≤ dist o x := by
  have h:=dist_triangle o x y
  unfold product; linarith
lemma product_le_right (o x y : X) : product o x y ≤ dist o y := by
  have h:=dist_triangle o y x
  rw [dist_comm y x] at h
  unfold product; linarith
lemma geodesic_start_dist {p : VertexPath X} (hp : p.Geodesic) {i : ℕ} (hi : i ≤ p.length) :
    dist p.start (p.point i)=i := by
  rw [start,hp 0 (Nat.zero_le _) i hi]
  simp
lemma geodesic_finish_dist {p : VertexPath X} (hp : p.Geodesic) {i : ℕ} (hi : i ≤ p.length) :
    dist (p.point i) p.finish=(p.length:ℝ)-i := by
  rw [finish,hp i hi p.length (le_refl _),abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (i:ℝ) ≤ p.length by exact_mod_cast hi))]
  ring

lemma thin_initial_close {D : ℝ} (hD : 0 ≤ D) (hthin : ThinTriangles X D)
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    {p q : VertexPath X} (hp : p.Geodesic) (hq : q.Geodesic) (he : p.start=q.start)
    {i : ℕ} (hi : (i:ℝ)+D < product p.start p.finish q.finish) :
    i ≤ p.length ∧ i ≤ q.length ∧ dist (p.point i) (q.point i) ≤ 2*D := by
  have hip : i ≤ p.length := by
    have hh:=product_le_left p.start p.finish q.finish
    rw [geodesic_length hp] at hh
    have h : (i:ℝ) ≤ p.length := by linarith
    exact_mod_cast h
  have hiq : i ≤ q.length := by
    have hh:=product_le_right p.start p.finish q.finish
    rw [he,geodesic_length hq] at hh
    have hi' := hi
    rw [he] at hi'
    have h : (i:ℝ) ≤ q.length := by linarith
    exact_mod_cast h
  refine ⟨hip,hiq,?_⟩
  obtain ⟨r,hrs,hre,hr⟩:=hgeo p.finish q.finish
  rcases hthin p q r hp hq hr he hrs.symm hre.symm i hip with ⟨j,hj,hxy⟩|⟨j,hj,hxy⟩
  · have hdist : |(i:ℝ)-j| ≤ D := by
      have hh:=abs_dist_sub_le (p.point i) (q.point j) p.start
      rw [dist_comm (p.point i),geodesic_start_dist hp hip,
        dist_comm (q.point j),he,geodesic_start_dist hq hj] at hh
      exact hh.trans hxy
    have ht:=dist_triangle (p.point i) (q.point j) (q.point i)
    rw [hq j hj i hiq,abs_sub_comm] at ht
    linarith
  · have h1:=dist_triangle p.start (p.point i) (r.point j)
    have h2:=dist_triangle p.start (r.point j) q.finish
    have h3:=dist_triangle (p.point i) (r.point j) p.finish
    have hpstart:=geodesic_start_dist hp hip
    have hpend:=geodesic_finish_dist hp hip
    have hrstart:=geodesic_start_dist hr hj
    have hrend:=geodesic_finish_dist hr hj
    have hpLen:=geodesic_length hp
    have hrLen:=geodesic_length hr
    rw [hrs,dist_comm] at hrstart
    rw [hre] at hrend
    rw [hrs,hre] at hrLen
    unfold product at hi
    linarith

lemma thin_product {D : ℝ} (hD : 0 ≤ D) (hthin : ThinTriangles X D)
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    (o a b c : X) :
    min (product o a b) (product o b c) ≤ product o a c+(3*D+2) := by
  let R:=min (product o a b) (product o b c)
  by_cases hsmall : R ≤ D+1
  · have hn:=product_nonneg o a c
    change R ≤ _
    linarith
  · have hpos : 0 ≤ R-D-1 := by linarith
    let i:=⌊R-D-1⌋₊
    have hile : (i:ℝ) ≤ R-D-1 := Nat.floor_le hpos
    have hir : R-D-1 < (i:ℝ)+1 := Nat.lt_floor_add_one _
    obtain ⟨p,hps,hpe,hp⟩:=hgeo o a
    obtain ⟨q,hqs,hqe,hq⟩:=hgeo o b
    obtain ⟨r,hrs,hre,hr⟩:=hgeo o c
    have hab : (i:ℝ)+D < product p.start p.finish q.finish := by
      rw [hps,hpe,hqe]
      have hh:=min_le_left (product o a b) (product o b c)
      change R ≤ _ at hh
      linarith
    have hbc : (i:ℝ)+D < product q.start q.finish r.finish := by
      rw [hqs,hqe,hre]
      have hh:=min_le_right (product o a b) (product o b c)
      change R ≤ _ at hh
      linarith
    obtain ⟨hip,hiq,hpq⟩:=thin_initial_close hD hthin hgeo hp hq (hps.trans hqs.symm) hab
    obtain ⟨_,hir',hqr⟩:=thin_initial_close hD hthin hgeo hq hr (hqs.trans hrs.symm) hbc
    have hpr:=dist_triangle (p.point i) (q.point i) (r.point i)
    have ht:=dist_triangle4 a (p.point i) (r.point i) c
    have hpa:=geodesic_finish_dist hp hip
    have hrc:=geodesic_finish_dist hr hir'
    have hpLen:=geodesic_length hp
    have hrLen:=geodesic_length hr
    rw [hpe,dist_comm] at hpa
    rw [hre] at hrc
    rw [hps,hpe] at hpLen
    rw [hrs,hre] at hrLen
    change R ≤ _
    unfold product
    linarith

lemma thin_fourpoint {D : ℝ} (hD : 0 ≤ D) (hthin : ThinTriangles X D)
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    (a b c d : X) :
    dist a c+dist b d ≤ max (dist a b+dist c d) (dist a d+dist b c)+2*(3*D+2) := by
  have hh:=thin_product hD hthin hgeo a b c d
  unfold product at hh
  rcases le_total ((dist a b+dist a c-dist b c)/2) ((dist a c+dist a d-dist c d)/2) with h|h
  · rw [min_eq_left h] at hh
    have hmax:=le_max_right (dist a b+dist c d) (dist a d+dist b c)
    linarith
  · rw [min_eq_right h] at hh
    have hmax:=le_max_left (dist a b+dist c d) (dist a d+dist b c)
    linarith

end VertexPath

/-! A quantitative proof that linear word-homotopy filling bounds imply
four-point hyperbolicity. -/
namespace WordPictures
open Cochain
variable {A G : Type*} [Group G] [Finite A]
lemma wordHyperbolic_of_linear (φ : FreeGroup A →* G) (hφ : Function.Surjective φ)
    {R : Set (Word A)} {C : ℝ} (hC : 0 ≤ C) {L : ℕ}
    (hv : ∀ w∈R, φ (FreeGroup.mk w)=1) (hL : ∀ w∈R, w.length ≤ L)
    (hfill : ∀ w, φ (FreeGroup.mk w)=1 → ∃ a, Homotopy R w [] a ∧ (a:ℝ) ≤ C*w.length) :
    WordHyperbolic G := by
  classical
  let := Fintype.ofFinite A
  let S : Finset G:=Finset.univ.image (fun a : A => φ (FreeGroup.of a))
  have hSrange : (S:Set G)=Set.range (fun a : A => φ (FreeGroup.of a)) := by
    simp only [S,Finset.coe_image,Finset.coe_univ,Set.image_univ]
  have hS : Subgroup.closure (S:Set G)=⊤ := by
    rw [hSrange,←FreeGroup.lift_surjective_iff_closure_range_eq_top]
    have he : FreeGroup.lift (fun a : A => φ (FreeGroup.of a))=φ := by
      ext a; simp
    rw [he]
    exact hφ
  have H : ∀ a∈S, ∃ b : A, φ (FreeGroup.of b)=a := by
    intro a ha
    exact Finset.mem_image.mp ha |>.imp (fun b hb => hb.2)
  have Hstep : ∀ a : A×Bool, WordLength S (letter φ a) ≤ 1 := by
    rintro ⟨a,b⟩
    have ha : φ (FreeGroup.of a)∈S := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
    have hh : letter φ (a,b)∈S ∨ (letter φ (a,b))⁻¹∈S := by
      cases b
      · right
        have he:=letter_flip φ a true
        rw [Bool.not_true] at he
        rw [he,inv_inv]
        exact ha
      · exact Or.inl ha
    simpa only [List.prod_singleton,List.length_singleton] using
      WordLength.le_length S (w:=[letter φ (a,b)]) (by
        intro g hg; simpa only [List.mem_singleton.mp hg] using hh)
  let := WordDistance.metric S hS
  have hd : ∀ x y : G, dist x y=WordDistance S x y := fun _ _ => rfl
  have hgeo:=geodesic_exists φ S hS hd H Hstep
  have hint : ∀ x y : G, ∃ n : ℕ, dist x y=n := fun x y => ⟨WordLength S (x⁻¹*y),rfl⟩
  have hco:=linear_of_filling φ S hS hd hC H Hstep hv hL hfill
  let K : ℝ:=3*(L:ℝ)^2*C
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hthin:=VertexPath.cochain_thin hK hco hgeo hint
  refine ⟨S,hS,3*(112*K)+2,by positivity,?_⟩
  intro a b c d
  exact VertexPath.thin_fourpoint (by positivity) hthin hgeo a b c d

end WordPictures

/-! All clauses of the exact main except exclusion of compatible locally
CAT(-1) finite homotopy models. The complete literal hyperbolicity consequence
is now unconditional, on the SAME finite aspherical complex. -/
namespace IncidenceTemplate
open CoreGeometry LetterPresentation ConeSkeleton
universe u

lemma finalFinite_hyperbolic (m : ℕ) :
    WordHyperbolic (FundamentalGroup (finalFiniteComplex m).Carrier (finalFiniteBasepoint m)) := by
  let p:=PresentedGroup.mk (Relator (finalSize m) (finalMaster m) (finalSix m))
  let e:=finalFinitePiOneEquiv m
  let φ:=e.toMonoidHom.comp p
  obtain ⟨C,hC,hfill⟩:=finalDiagramStage_linear m
  apply WordPictures.wordHyperbolic_of_linear φ
    (e.surjective.comp (PresentedGroup.mk_surjective _)) hC.le (L:=18)
    (R:=SimpleWordRelator (finalSize m) (finalMaster m) (finalSix m))
  · intro w hw
    change e (p (FreeGroup.mk w))=1
    have hh : p (FreeGroup.mk w)=1 := by
      apply PresentedGroup.one_of_mem
      rw [←wordRelator_image]
      exact ⟨w,simpleWordRelator_original _ _ _ hw,rfl⟩
    rw [hh,map_one]
  · exact fun w hw => simpleWordRelator_length _ _ _ hw
  · intro w hw
    apply hfill w
    apply e.injective
    change e (p (FreeGroup.mk w))=1 at hw
    rw [map_one]
    exact hw

/-- SAME-model complete construction and word-hyperbolicity. It deliberately
omits, rather than assumes, the remaining Cartan-Hadamard/deck consequence. -/
theorem exists_finite_aspherical_hyperbolic_noAction :
    ∃ K : FiniteComplex, ∃ x : K.Carrier, ∃ C : ℝ,
    ConnectedSpace K.Carrier ∧ K.Aspherical x ∧ Infinite (FundamentalGroup K.Carrier x) ∧
      0 ≤ C ∧ K.LinearDiskFilling C ∧
      NoGeometricCATZeroAction.{u} (FundamentalGroup K.Carrier x) ∧
      WordHyperbolic (FundamentalGroup K.Carrier x) := by
  obtain ⟨m,hm⟩:=finalFinite_noAction.exists
  obtain ⟨C,hC,hfill⟩:=finalFinite_linear m
  exact ⟨finalFiniteComplex m,finalFiniteBasepoint m,C,inferInstance,finalFinite_aspherical m,
    inferInstance,hC,hfill,hm,finalFinite_hyperbolic m⟩

end IncidenceTemplate

/-! The real comparison inequality needed to pass the manuscript's exact
cosh-midpoint CAT(-1) definition to the Euclidean CN midpoint inequality. -/
namespace CurvatureComparison

section
open Set Real

lemma sinh_cosh_bound {x : ℝ} (hx : 0 ≤ x) : x ≤ sinh x * cosh x := by
  have h := (Real.self_le_sinh_iff).mpr (show 0 ≤ 2*x by positivity)
  rw [Real.sinh_two_mul] at h
  nlinarith

lemma tanhOver_antitone : AntitoneOn (fun x : ℝ => sinh x / (x * cosh x)) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact continuous_sinh.continuousOn.div
      (continuous_id.mul continuous_cosh).continuousOn
      (fun x hx => mul_ne_zero (ne_of_gt hx) (cosh_pos x).ne')
  · intro x hx
    simp only [interior_Ioi,mem_Ioi] at hx
    exact (((hasDerivAt_sinh x).div
      ((hasDerivAt_id x).mul (hasDerivAt_cosh x)) (mul_ne_zero hx.ne' (cosh_pos x).ne')).differentiableAt).differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi,mem_Ioi] using hx
    have hd := (hasDerivAt_sinh x).div
      ((hasDerivAt_id x).mul (hasDerivAt_cosh x)) (by positivity : x * cosh x ≠ 0)
    change deriv (sinh / (id * cosh)) x ≤ 0
    rw [hd.deriv]
    simp only [Pi.mul_apply,id_eq]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have h := sinh_cosh_bound hx'.le
    have hsq := Real.cosh_sq_sub_sinh_sq x
    have hh := congrArg (fun t : ℝ => x*t) hsq
    nlinarith

lemma deriv_logCoshSqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => log (cosh (sqrt t)))
      (sinh (sqrt x) / (2 * sqrt x * cosh (sqrt x))) x := by
  convert ((Real.hasDerivAt_cosh (sqrt x)).comp x (Real.hasDerivAt_sqrt hx.ne')).log
    (by positivity : cosh (sqrt x) ≠ 0) using 1 <;> simp only [Function.comp_def]
  field_simp

lemma logCoshSqrt_concave : ConcaveOn ℝ (Ici 0) (fun x : ℝ => log (cosh (sqrt x))) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
  · fun_prop (disch := intros; positivity)
  · rw [interior_Ici]
    intro x hx
    exact (deriv_logCoshSqrt hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx y hy hxy
    rw [(deriv_logCoshSqrt hx).deriv,(deriv_logCoshSqrt hy).deriv]
    have h := tanhOver_antitone (sqrt_pos.mpr hx) (sqrt_pos.mpr hy) (sqrt_le_sqrt hxy)
    convert div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 2) using 1 <;> ring

lemma concave_balance {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Ici 0) f)
    {a b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (hca : c ≤ a) :
    f a + f b ≤ f c + f (a+b-c) := by
  by_cases he : a = b
  · have hc : c = b := le_antisymm (he ▸ hca) hbc
    subst a; subst c; simp
  have hba : b < a := lt_of_le_of_ne (hbc.trans hca) (Ne.symm he)
  let t := (c-b)/(a-b)
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hba.le)
  have ht' : t ≤ 1 := (div_le_one (sub_pos.mpr hba)).mpr (by linarith)
  have h1 := hf.2 hb (hb.trans hba.le) (show 0 ≤ 1-t by linarith) ht (by ring : (1-t)+t=1)
  have h2 := hf.2 hb (hb.trans hba.le) ht (show 0 ≤ 1-t by linarith) (by ring : t+(1-t)=1)
  have he1 : (1-t)*b+t*a = c := by dsimp [t]; field_simp; ring
  have he2 : t*b+(1-t)*a = a+b-c := by dsimp [t]; field_simp; ring
  simp only [smul_eq_mul,he1,he2] at h1 h2
  nlinarith

lemma cosh_balance {x y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) (hzx : z ≤ x) :
    cosh x * cosh y / cosh z ≤ cosh (sqrt (x^2+y^2-z^2)) := by
  have hz := hy.trans hyz
  have hx := hz.trans hzx
  have h := concave_balance logCoshSqrt_concave (sq_nonneg y)
    (sq_le_sq₀ hy hz |>.mpr hyz) (sq_le_sq₀ hz hx |>.mpr hzx)
  simp only [sqrt_sq hx,sqrt_sq hy,sqrt_sq hz] at h
  rw [←log_mul (cosh_pos x).ne' (cosh_pos y).ne',
    ←log_mul (cosh_pos z).ne' (cosh_pos _).ne'] at h
  have hp := (log_le_log_iff (mul_pos (cosh_pos x) (cosh_pos y))
    (mul_pos (cosh_pos z) (cosh_pos _))).mp h
  exact (div_le_iff₀ (cosh_pos z)).mpr (by simpa only [mul_comm] using hp)

lemma cosh_triangle_comparison {a b c : ℝ} (_ : 0 ≤ a) (_ : 0 ≤ b) (_ : 0 ≤ c)
    (hab : a ≤ b+c) (hba : b ≤ a+c) (hca : c ≤ a+b) :
    (cosh a+cosh b)/(2*cosh (c/2)) ≤
      cosh (sqrt ((a^2+b^2)/2-c^2/4)) := by
  have h := cosh_balance (show 0 ≤ |a-b|/2 by positivity)
    (show |a-b|/2 ≤ c/2 by
      rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)]
      exact abs_le.mpr ⟨by linarith,by linarith⟩)
    (show c/2 ≤ (a+b)/2 by linarith)
  have hs : ((a+b)/2)^2+(|a-b|/2)^2-(c/2)^2 = (a^2+b^2)/2-c^2/4 := by
    simp only [div_pow, sq_abs]; ring
  have hh : cosh ((a+b)/2)*cosh (|a-b|/2) = (cosh a+cosh b)/2 := by
    rw [show |a-b|/2 = |(a-b)/2| by rw [abs_div]; norm_num,cosh_abs]
    have h1 := cosh_add ((a+b)/2) ((a-b)/2)
    have h2 := cosh_sub ((a+b)/2) ((a-b)/2)
    rw [show (a+b)/2+(a-b)/2=a by ring] at h1
    rw [show (a+b)/2-(a-b)/2=b by ring] at h2
    linarith
  rw [hs,hh] at h
  convert h using 1; ring

end

/-! A continuous midpoint-convex function on the unit interval lies below
its endpoint chord. The elementary maximum-principle proof avoids invoking
any curvature globalization theorem. -/
open Set
lemma midpoint_nonpos {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hmid : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
      f ((s+t)/2) ≤ (f s+f t)/2) (h0 : f 0 ≤ 0) (h1 : f 1 ≤ 0) :
    ∀ t ∈ Icc (0:ℝ) 1, f t ≤ 0 := by
  intro t ht
  by_contra! hpos
  let ε := f t / 2
  have he : 0 < ε := by dsimp [ε]; positivity
  let g : ℝ → ℝ := fun s => f s+ε*s^2
  have hg : ContinuousOn g (Icc 0 1) :=
    hf.add ((continuous_const.mul (continuous_id.pow 2)).continuousOn)
  obtain ⟨x,hx,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1)) hg
  have hlarge : ε < g x := by
    have h := hm ht
    have hn : 0 ≤ ε*t^2 := mul_nonneg he.le (sq_nonneg t)
    dsimp [g,ε] at *
    linarith
  have hx0 : 0 < x := by
    by_contra hh
    have heq : x=0 := le_antisymm (not_lt.mp hh) hx.1
    subst x
    simp only [g,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at hlarge
    linarith
  have hx1 : x < 1 := by
    by_contra hh
    have heq : x=1 := le_antisymm hx.2 (not_lt.mp hh)
    subst x
    simp only [g,one_pow,mul_one] at hlarge
    linarith
  let r := min x (1-x) / 2
  have hr : 0 < r := by dsimp [r]; exact div_pos (lt_min hx0 (sub_pos.mpr hx1)) (by norm_num)
  have hrx : r ≤ x := by
    have h := min_le_left x (1-x)
    dsimp [r]
    linarith
  have hr1 : r ≤ 1-x := by
    have h := min_le_right x (1-x)
    dsimp [r]
    linarith
  have hl : x-r ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hu : x+r ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hcv := hmid (x-r) hl (x+r) hu
  rw [show ((x-r)+(x+r))/2=x by ring] at hcv
  have hml := hm hl
  have hmu := hm hu
  have hp : 0 < ε*r^2 := mul_pos he (sq_pos_of_pos hr)
  dsimp [g] at hml hmu
  nlinarith

end CurvatureComparison

/-! The global cosh-midpoint comparison implies whole-segment CAT(0)
comparison. No completeness or globalization
hypothesis is hidden in this elementary curvature-monotonicity step. -/
section
open Set Real CurvatureComparison
variable {X : Type*} [MetricSpace X]

lemma IsSegment.continuousOn {γ : ℝ → X} {x y : X} (h : IsSegment γ x y) :
    ContinuousOn γ (Icc 0 1) := by
  apply LipschitzOnWith.continuousOn (K := ⟨dist x y,dist_nonneg⟩)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [h.2.2 s hs t ht,Real.dist_eq]
  exact le_of_eq (mul_comm _ _)

lemma CATNegOne.midpoint_cn (h : CATNegOne X) (x y : X) :
    ∃ γ, IsSegment γ x y ∧ ∀ z : X,
      dist z (γ (1/2))^2 ≤ (dist z x^2+dist z y^2)/2 - dist x y^2/4 := by
  obtain ⟨γ,hγ,hcosh⟩ := h x y
  refine ⟨γ,hγ,fun z => ?_⟩
  have hc := cosh_triangle_comparison (dist_nonneg (x:=z) (y:=x))
    (dist_nonneg (x:=z) (y:=y)) (dist_nonneg (x:=x) (y:=y))
    (by simpa only [dist_comm y x] using dist_triangle z y x)
    (dist_triangle z x y) (by simpa only [dist_comm x z] using dist_triangle x z y)
  have hm := (cosh_le_cosh).mp ((hcosh z).trans hc)
  rw [abs_of_nonneg dist_nonneg,abs_of_nonneg (sqrt_nonneg _)] at hm
  have htri : dist x y ≤ dist z x+dist z y := by
    simpa only [dist_comm x z] using dist_triangle x z y
  have hr : 0 ≤ (dist z x^2+dist z y^2)/2-dist x y^2/4 := by
    have hs := sq_le_sq₀ (dist_nonneg (x:=x) (y:=y))
      (add_nonneg (dist_nonneg (x:=z) (y:=x)) (dist_nonneg (x:=z) (y:=y))) |>.mpr htri
    nlinarith [sq_nonneg (dist z x-dist z y)]
  have hsq := sq_le_sq₀ (dist_nonneg (x:=z) (y:=γ (1/2))) (sqrt_nonneg _) |>.mpr hm
  rwa [sq_sqrt hr] at hsq

lemma CATNegOne.cn_of_midpoint (h : CATNegOne X) (x y m : X)
    (hx : dist x m = dist x y/2) (hy : dist y m = dist x y/2) (z : X) :
    dist z m^2 ≤ (dist z x^2+dist z y^2)/2 - dist x y^2/4 := by
  obtain ⟨γ,hγ,hcn⟩ := h.midpoint_cn x y
  have hm := hcn m
  rw [dist_comm m x,dist_comm m y,hx,hy] at hm
  have he : γ (1/2) = m := by
    apply dist_eq_zero.mp
    have hd := dist_nonneg (x:=m) (y:=γ (1/2))
    have hz : dist m (γ (1/2))=0 := by nlinarith [sq_nonneg (dist m (γ (1/2)))]
    simpa only [dist_comm] using hz
  simpa only [he] using hcn z

lemma IsSegment.midpoint_dist {γ : ℝ → X} {x y : X} (h : IsSegment γ x y)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    dist (γ s) (γ ((s+t)/2)) = dist (γ s) (γ t)/2 := by
  have hm : (s+t)/2 ∈ Icc (0:ℝ) 1 := ⟨by linarith [hs.1,ht.1],by linarith [hs.2,ht.2]⟩
  rw [h.2.2 s hs ((s+t)/2) hm,h.2.2 s hs t ht,
    show s-(s+t)/2=(s-t)/2 by ring,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  ring

/-- Curvature monotonicity for the exact definitions used in the main. -/
theorem CATNegOne.catZero (h : CATNegOne X) : CATZero X := by
  intro x y
  obtain ⟨γ,hγ,hmid⟩ := h.midpoint_cn x y
  refine ⟨γ,hγ,fun z t ht => ?_⟩
  let F : ℝ → ℝ := fun s => dist z (γ s)^2 -
    ((1-s)*dist z x^2+s*dist z y^2-s*(1-s)*dist x y^2)
  have hF : ContinuousOn F (Icc 0 1) := by
    apply ContinuousOn.sub
    · exact (continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγ.continuousOn)).pow 2
    · fun_prop
  have hF0 : F 0 ≤ 0 := by simp [F,hγ.1]
  have hF1 : F 1 ≤ 0 := by simp [F,hγ.2.1]
  have hm : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
      F ((s+t)/2) ≤ (F s+F t)/2 := by
    intro s hs t ht
    have hl := hγ.midpoint_dist hs ht
    have hr := hγ.midpoint_dist ht hs
    rw [add_comm t s,dist_comm (γ t) (γ s)] at hr
    have hh := h.cn_of_midpoint (γ s) (γ t) (γ ((s+t)/2)) hl hr z
    rw [hγ.2.2 s hs t ht,mul_pow,sq_abs] at hh
    dsimp [F]
    nlinarith
  have hh := midpoint_nonpos hF hm hF0 hF1 t ht
  dsimp [F] at hh
  linarith

end

section

/-! Uniform local comparison, extracted from compactness and the precise
hypothetical metric in the main. The midpoint is an actual ambient midpoint;
its local uniqueness and estimates are proved, not postulated. -/
open Set Metric
variable {X : Type*} [MetricSpace X]

namespace IsGeodesic

def midpoint (h : IsGeodesic X) (x y : X) : X := (h x y).choose (1/2)

lemma dist_left_midpoint (h : IsGeodesic X) (x y : X) :
    dist x (h.midpoint x y) = dist x y / 2 := by
  have hh := (h x y).choose_spec.2.2 0 (by norm_num) (1/2) (by norm_num)
  rw [(h x y).choose_spec.1] at hh
  simpa [midpoint,div_eq_mul_inv,mul_comm] using hh

lemma dist_midpoint_right (h : IsGeodesic X) (x y : X) :
    dist (h.midpoint x y) y = dist x y / 2 := by
  have hh := (h x y).choose_spec.2.2 (1/2) (by norm_num) 1 (by norm_num)
  rw [(h x y).choose_spec.2.1] at hh
  norm_num at hh
  simpa [midpoint,div_eq_mul_inv,mul_comm] using hh

end IsGeodesic

/-- A uniform ambient neighborhood lies in a CAT(0) subspace. -/
def UniformLocalCATZero (r : ℝ) : Prop :=
  ∀ x : X, ∃ U : Set X, ball x r ⊆ U ∧ CATZero U

lemma uniformLocalCATZero_of_compact [CompactSpace X]
    (h : ∀ x : X, ∃ r : ℝ, 0 < r ∧ CATNegOne (ball x r)) :
    ∃ r : ℝ, 0 < r ∧ UniformLocalCATZero (X:=X) r := by
  choose r hr hc using h
  obtain ⟨δ,hδ,hd⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun x : X => isOpen_ball (x:=x) (ε:=r x))
    (show (univ : Set X) ⊆ ⋃ x : X, ball x (r x) from by
      intro x _; exact mem_iUnion.mpr ⟨x,mem_ball_self (hr x)⟩)
  refine ⟨δ,hδ,fun x => ?_⟩
  obtain ⟨y,hy⟩ := hd x (mem_univ x)
  exact ⟨ball y (r y),hy,(hc y).catZero⟩

lemma midpoint_eq_subtype {U : Set X} (hU : CATZero U) (g : IsGeodesic X)
    {a b : X} (ha : a ∈ U) (hb : b ∈ U) (hm : g.midpoint a b ∈ U) :
    (⟨g.midpoint a b,hm⟩ : U) = CATZero.mid hU ⟨a,ha⟩ ⟨b,hb⟩ := by
  apply CATZero.eq_segment_of_dist hU (by norm_num : (1/2:ℝ) ∈ Icc 0 1)
  · change dist a (g.midpoint a b) = (1/2)*dist a b
    rw [g.dist_left_midpoint]
    simp [div_eq_mul_inv,mul_comm]
  · change dist (g.midpoint a b) b = (1-1/2)*dist a b
    rw [g.dist_midpoint_right]
    norm_num
    ring

lemma IsGeodesic.midpoint_mem_ball (g : IsGeodesic X) {o a b : X} {r : ℝ}
    (ha : a ∈ ball o (r/3)) (hb : b ∈ ball o (r/3)) :
    g.midpoint a b ∈ ball o r := by
  rw [mem_ball] at *
  have hab := dist_triangle a o b
  rw [dist_comm o b] at hab
  have hm := dist_triangle (g.midpoint a b) a o
  rw [dist_comm (g.midpoint a b) a,g.dist_left_midpoint] at hm
  have hr : 0 < r := by linarith [dist_nonneg (x:=a) (y:=o)]
  linarith

lemma UniformLocalCATZero.midpoint_lipschitz {r : ℝ} (h : UniformLocalCATZero (X:=X) r)
    (g : IsGeodesic X) {o a b c d : X}
    (ha : a ∈ ball o (r/3)) (hb : b ∈ ball o (r/3))
    (hc : c ∈ ball o (r/3)) (hd : d ∈ ball o (r/3)) :
    dist (g.midpoint a b) (g.midpoint c d) ≤ (dist a c+dist b d)/2 := by
  have hr : 0 < r := by have hh := dist_nonneg (x:=a) (y:=o); rw [mem_ball] at ha; linarith
  obtain ⟨U,hU,hcat⟩ := h o
  have sub : ball o (r/3) ⊆ U := (ball_subset_ball (by linarith)).trans hU
  have hm₁ := midpoint_eq_subtype hcat g (sub ha) (sub hb) (hU (g.midpoint_mem_ball ha hb))
  have hm₂ := midpoint_eq_subtype hcat g (sub hc) (sub hd) (hU (g.midpoint_mem_ball hc hd))
  have hh := CATZero.dist_mid_mid_le hcat (⟨a,sub ha⟩ : U) ⟨b,sub hb⟩ ⟨c,sub hc⟩ ⟨d,sub hd⟩
  rw [←hm₁,←hm₂] at hh
  exact hh

lemma UniformLocalCATZero.midpoint_cn {r : ℝ} (h : UniformLocalCATZero (X:=X) r)
    (g : IsGeodesic X) {o a b z : X}
    (ha : a ∈ ball o (r/3)) (hb : b ∈ ball o (r/3)) (hz : z ∈ ball o (r/3)) :
    dist z (g.midpoint a b)^2 ≤ (dist z a^2+dist z b^2)/2-dist a b^2/4 := by
  have hr : 0 < r := by have hh := dist_nonneg (x:=a) (y:=o); rw [mem_ball] at ha; linarith
  obtain ⟨U,hU,hcat⟩ := h o
  have sub : ball o (r/3) ⊆ U := (ball_subset_ball (by linarith)).trans hU
  have hm := midpoint_eq_subtype hcat g (sub ha) (sub hb) (hU (g.midpoint_mem_ball ha hb))
  have hh := CATZero.mid_cn hcat (⟨a,sub ha⟩ : U) ⟨b,sub hb⟩ ⟨z,sub hz⟩
  rw [←hm] at hh
  exact hh

end

section

/-! Compact, finite Dirichlet midpoint problems have a unique stationary
polygon whenever their common local comparison gives the midpoint contraction.
The proof minimizes a weighted residual, not an unproved fixed-point premise. -/
open Set
namespace FiniteMidpointFixedPoint
variable {X P : Type*} [MetricSpace X] [TopologicalSpace P] [CompactSpace P]

abbrev left {n : ℕ} (i : Fin n) : Fin (n+2) := i.castSucc.castSucc
abbrev center {n : ℕ} (i : Fin n) : Fin (n+2) := i.castSucc.succ
abbrev right {n : ℕ} (i : Fin n) : Fin (n+2) := i.succ.succ

def weight (n : ℕ) (i : Fin (n+2)) : ℝ := 1+(i:ℝ)*((n+1:ℕ)-i)

lemma weight_pos (n : ℕ) (i : Fin (n+2)) : 0 < weight n i := by
  have hi : (i:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (show i.val ≤ n+1 from by omega)
  have hn : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  dsimp [weight]
  nlinarith

lemma weight_le (n : ℕ) (i : Fin (n+2)) : weight n i ≤ (n+2:ℝ)^2+1 := by
  have hi : (i:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (show i.val ≤ n+1 from by omega)
  have hn : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  have hnn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  dsimp [weight]
  push_cast at *
  nlinarith

lemma weight_neighbors (n : ℕ) (i : Fin n) :
    weight n (left i)+weight n (right i)=2*weight n (center i)-2 := by
  dsimp [weight,left,right,center]
  push_cast
  ring

/-- The compact finite Dirichlet problem. Boundary values are fixed, and
all interior coordinates satisfy the ordinary one-half neighbor estimate. -/
theorem exists_fixed [Nonempty P] (n : ℕ) (u : P → Fin (n+2) → X)
    (hu : ∀ i, Continuous (fun p => u p i)) (hinj : Function.Injective u)
    (T : P → P) (hT : ∀ i, Continuous (fun p => u (T p) i))
    (hleft : ∀ p q, u (T p) 0=u (T q) 0)
    (hright : ∀ p q, u (T p) (Fin.last (n+1))=u (T q) (Fin.last (n+1)))
    (hmid : ∀ p q (i : Fin n),
      dist (u (T p) (center i)) (u (T q) (center i)) ≤
        (dist (u p (left i)) (u q (left i))+dist (u p (right i)) (u q (right i)))/2) :
    ∃ p, T p=p := by
  let D : P → P → ℝ := fun p q => Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin (n+2) => dist (u p i) (u q i)/weight n i)
  have hD (p q : P) (i : Fin (n+2)) : dist (u p i) (u q i) ≤ weight n i*D p q := by
    have hh := Finset.le_sup' (s:=Finset.univ) (f:=fun i : Fin (n+2) =>
      dist (u p i) (u q i)/weight n i) (Finset.mem_univ i)
    change dist (u p i) (u q i)/weight n i ≤ D p q at hh
    simpa [mul_comm] using (div_le_iff₀ (weight_pos n i)).mp hh
  have hDn (p q : P) : 0 ≤ D p q := by
    have hh := hD p q 0
    have hn := dist_nonneg (x:=u p 0) (y:=u q 0)
    nlinarith [weight_pos n 0]
  let W : ℝ := (n+2:ℝ)^2+1
  have hW : 1 < W := by dsimp [W]; nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]
  let q : ℝ := 1-1/W
  have hq0 : 0 ≤ q := by dsimp [q]; have := (div_le_one (by linarith : 0<W)).mpr hW.le; linarith
  have hq1 : q<1 := by dsimp [q]; have := one_div_pos.mpr (by linarith : 0<W); linarith
  have hcontract (p s : P) : D (T p) (T s) ≤ q*D p s := by
    apply Finset.sup'_le
    intro i _
    apply (div_le_iff₀ (weight_pos n i)).mpr
    by_cases h0 : i=0
    · subst i
      rw [hleft,dist_self]
      exact mul_nonneg (mul_nonneg hq0 (hDn p s)) (weight_pos n 0).le
    by_cases hn : i=Fin.last (n+1)
    · subst i
      rw [hright,dist_self]
      exact mul_nonneg (mul_nonneg hq0 (hDn p s)) (weight_pos n _).le
    have hi0 : 0 < i.val := by by_contra hh; apply h0; apply Fin.ext; simp only [Fin.val_zero]; omega
    have hin : i.val < n+1 := by by_contra hh; apply hn; apply Fin.ext; simp; omega
    let j : Fin n := ⟨i.val-1,by omega⟩
    have hj : center j=i := by apply Fin.ext; dsimp [center,j]; omega
    have hb := hmid p s j
    have h1 := hD p s (left j)
    have h2 := hD p s (right j)
    have hw := weight_neighbors n j
    rw [hj] at hb hw
    have hsum : dist (u (T p) i) (u (T s) i) ≤ (weight n i-1)*D p s := by
      have he := congrArg (fun a : ℝ => a*D p s) hw
      nlinarith
    have hiW : weight n i≤W := weight_le n i
    have hwq : weight n i-1 ≤ q*weight n i := by
      dsimp [q]
      have hh := (div_le_one (by linarith : 0<W)).mpr hiW
      nlinarith [show (1/W)*weight n i=weight n i/W by ring]
    exact hsum.trans (by nlinarith [mul_le_mul_of_nonneg_right hwq (hDn p s)])
  have hcont : Continuous (fun p => D p (T p)) := by
    apply Continuous.finset_sup'_apply
    intro i _
    exact ((hu i).dist (hT i)).div_const _
  obtain ⟨p,_,hp⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set P).Nonempty)
    hcont.continuousOn
  have hh : D p (T p) ≤ D (T p) (T (T p)) := hp (mem_univ (T p))
  have hc := hcontract p (T p)
  have hd0 : D p (T p)=0 := by nlinarith [hDn p (T p)]
  refine ⟨p,hinj ?_⟩
  funext i
  have hf := hD p (T p) i
  rw [hd0,mul_zero] at hf
  exact (dist_eq_zero.mp (le_antisymm hf dist_nonneg)).symm

end FiniteMidpointFixedPoint
end

/-! The finite difference maximum principle required for local geodesic
continuation. Endpoint estimates are literal, with no convergence assumption. -/
namespace DiscreteHarmonic

lemma maximum (N : ℕ) (f : ℕ → ℝ)
    (hf : ∀ i, i+2 ≤ N → 2*f (i+1) ≤ f i+f (i+2))
    {i : ℕ} (hi : i ≤ N) : f i ≤ max (f 0) (f N) := by
  obtain ⟨j,hj,hm⟩ := Finset.exists_max_image (Finset.range (N+1)) f (by simp)
  have hjN : j ≤ N := by simpa using hj
  have hall (k : ℕ) (hk : k ≤ N) : f k ≤ f j := hm k (by simpa using hk)
  have prop (k : ℕ) : k ≤ N → f k = f j → f 0 = f j ∨ f N = f j := by
    induction k with
    | zero => exact fun _ hk => Or.inl hk
    | succ k ih =>
      intro hk he
      by_cases hl : k+1=N
      · exact Or.inr (hl ▸ he)
      · have hstep := hf k (by omega)
        have hnext := hall (k+2) (by omega)
        have hprev := hall k (by omega)
        apply ih (by omega)
        change f (k+1)=f j at he
        linarith
  rcases prop j hjN rfl with h0|hN
  · exact (hall i hi).trans (h0 ▸ le_max_left _ _)
  · exact (hall i hi).trans (hN ▸ le_max_right _ _)

lemma chord (N : ℕ) (hN : 0<N) (f : ℕ → ℝ)
    (hf : ∀ i, i+2 ≤ N → 2*f (i+1) ≤ f i+f (i+2))
    {i : ℕ} (hi : i ≤ N) :
    f i ≤ (1-(i:ℝ)/N)*f 0 + ((i:ℝ)/N)*f N := by
  let g : ℕ → ℝ := fun k => f k-((1-(k:ℝ)/N)*f 0+((k:ℝ)/N)*f N)
  have hg : ∀ k, k+2 ≤ N → 2*g (k+1) ≤ g k+g (k+2) := by
    intro k hk
    have hh := hf k hk
    have he : 2*g (k+1)-(g k+g (k+2)) = 2*f (k+1)-(f k+f (k+2)) := by
      dsimp [g]
      push_cast
      ring
    linarith
  have hh := maximum N g hg hi
  have hz : g 0=0 := by simp [g]
  have hn : g N=0 := by simp [g,ne_of_gt hN]
  rw [hz,hn,max_self] at hh
  dsimp [g] at hh
  linarith

end DiscreteHarmonic

section

/-! Actual finite local-geodesic continuation. Uniform local comparison and
compactness produce, rather than assume, stationary polygons with perturbed
endpoints, and the finite maximum principle produces their uniqueness. -/
open Metric
namespace LocalPolygonContinuation
open FiniteMidpointFixedPoint
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  {r : ℝ} (hr : 0<r) (hcat : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
  {n : ℕ} (q : Fin (n+2) → X)
  (hnear : ∀ i : Fin n, dist (q (left i)) (q (center i))<r/10 ∧
    dist (q (right i)) (q (center i))<r/10)
  (hmid : ∀ i : Fin n, q (center i)=g.midpoint (q (left i)) (q (right i)))

def Box (a b : X) : Set (Fin (n+2) → X) :=
  {p | p 0=a ∧ p (Fin.last (n+1))=b ∧ ∀ i, dist (p i) (q i)≤r/20}

omit [CompactSpace X] in
lemma box_closed (a b : X) : IsClosed (Box (r:=r) q a b) := by
  apply IsClosed.inter
  · exact isClosed_eq (continuous_apply 0) continuous_const
  · apply IsClosed.inter
    · exact isClosed_eq (continuous_apply _) continuous_const
    · change IsClosed {p : Fin (n+2) → X | ∀ i, dist (p i) (q i) ≤ r/20}
      have hh : IsClosed (⋂ i : Fin (n+2), {p : Fin (n+2) → X | dist (p i) (q i) ≤ r/20}) :=
        isClosed_iInter (fun i => isClosed_le ((continuous_apply i).dist continuous_const) continuous_const)
      simpa only [Set.iInter_ofPred] using hh

include hr in
omit [CompactSpace X] in
lemma box_nonempty {a b : X} (ha : dist a (q 0)≤r/20)
    (hb : dist b (q (Fin.last (n+1)))≤r/20) : (Box (r:=r) q a b).Nonempty := by
  classical
  let p : Fin (n+2) → X := fun i => if i=0 then a else if i=Fin.last (n+1) then b else q i
  have hn : (Fin.last (n+1) : Fin (n+2))≠0 := by intro he; have := congrArg Fin.val he; simp at this
  refine ⟨p,by simp [p],by simp [p,hn],?_⟩
  intro i
  by_cases h0 : i=0
  · subst i; simpa [p] using ha
  by_cases hl : i=Fin.last (n+1)
  · subst i; simpa [p,hn] using hb
  simp only [p,ite_eq_right h0,ite_eq_right hl,dist_self]
  linarith

include hr hnear in
omit [CompactSpace X] in
lemma neighbors_in_ball {a b : X} (p : Box (r:=r) q a b) (i : Fin n) :
    p.val (left i) ∈ ball (q (center i)) (r/3) ∧
    p.val (right i) ∈ ball (q (center i)) (r/3) := by
  constructor
  · rw [mem_ball]
    have hh := dist_triangle (p.val (left i)) (q (left i)) (q (center i))
    have hp := p.property.2.2 (left i)
    have hq := (hnear i).1
    linarith
  · rw [mem_ball]
    have hh := dist_triangle (p.val (right i)) (q (right i)) (q (center i))
    have hp := p.property.2.2 (right i)
    have hq := (hnear i).2
    linarith

private def node {a b : X} (p : Box (r:=r) q a b) (i : Fin (n+2)) : X :=
  if h0 : i=0 then a else if hn : i=Fin.last (n+1) then b else
    g.midpoint (p.val ⟨i.val-1,by omega⟩) (p.val ⟨i.val+1,by
      have h : i.val < n+1 := by by_contra h; apply hn; apply Fin.ext; simp; omega
      omega⟩)

omit [CompactSpace X] in
private lemma node_zero {a b : X} (p : Box (r:=r) q a b) : node g q p 0=a := by simp [node]
omit [CompactSpace X] in
private lemma node_last {a b : X} (p : Box (r:=r) q a b) : node g q p (Fin.last (n+1))=b := by simp [node]
omit [CompactSpace X] in
private lemma node_center {a b : X} (p : Box (r:=r) q a b) (i : Fin n) :
    node g q p (center i)=g.midpoint (p.val (left i)) (p.val (right i)) := by
  have h0 : center i≠0 := by intro he; have := congrArg Fin.val he; simp [center] at this
  have hl : center i≠Fin.last (n+1) := by
    intro he; have hh := congrArg Fin.val he; dsimp [center] at hh; omega
  simp only [node,dite_eq_right h0,dite_eq_right hl]
  congr 2

include hr hcat hnear hmid in
omit [CompactSpace X] in
private lemma node_mem {a b : X} (ha : dist a (q 0)≤r/20)
    (hb : dist b (q (Fin.last (n+1)))≤r/20) (p : Box (r:=r) q a b) :
    node g q p ∈ Box (r:=r) q a b := by
  refine ⟨node_zero g q p,node_last g q p,fun i => ?_⟩
  by_cases h0 : i=0
  · subst i; simpa only [node_zero] using ha
  by_cases hl : i=Fin.last (n+1)
  · subst i; simpa only [node_last] using hb
  have hi0 : 0 < i.val := by by_contra hh; apply h0; apply Fin.ext; simp only [Fin.val_zero]; omega
  have hin : i.val < n+1 := by by_contra hh; apply hl; apply Fin.ext; simp; omega
  let j : Fin n := ⟨i.val-1,by omega⟩
  have he : center j=i := by apply Fin.ext; dsimp [center,j]; omega
  rw [←he,node_center,hmid j]
  have hp := neighbors_in_ball hr q hnear p j
  have hq₁ : q (left j) ∈ ball (q (center j)) (r/3) := by rw [mem_ball]; linarith [(hnear j).1]
  have hq₂ : q (right j) ∈ ball (q (center j)) (r/3) := by rw [mem_ball]; linarith [(hnear j).2]
  have hh := hcat.midpoint_lipschitz g hp.1 hp.2 hq₁ hq₂
  linarith [p.property.2.2 (left j),p.property.2.2 (right j)]

include hr hcat hnear hmid in
/-- Small endpoint perturbations have an actual midpoint-stationary polygon
in the prescribed box. Compactness is used only for a genuine finite minimum. -/
theorem exists_stationary {a b : X} (ha : dist a (q 0)≤r/20)
    (hb : dist b (q (Fin.last (n+1)))≤r/20) :
    ∃ p : Fin (n+2) → X, p ∈ Box (r:=r) q a b ∧
      ∀ i : Fin n, p (center i)=g.midpoint (p (left i)) (p (right i)) := by
  let B := Box (r:=r) q a b
  have : CompactSpace B := isCompact_iff_compactSpace.mp (box_closed q a b).isCompact
  have : Nonempty B := Set.nonempty_coe_sort.mpr (box_nonempty hr q ha hb)
  let T : B → B := fun p => ⟨node g q p,node_mem hr hcat g q hnear hmid ha hb p⟩
  have hT (i : Fin (n+2)) : Continuous (fun p : B => (T p).val i) := by
    by_cases h0 : i=0
    · subst i; simpa [T,node_zero] using (continuous_const : Continuous (fun _ : B => a))
    by_cases hn : i=Fin.last (n+1)
    · subst i; simpa [T,node_last] using (continuous_const : Continuous (fun _ : B => b))
    have hil : 0 < i.val := by by_contra hh; apply h0; apply Fin.ext; simp only [Fin.val_zero]; omega
    have hin : i.val < n+1 := by by_contra hh; apply hn; apply Fin.ext; simp; omega
    let j : Fin n := ⟨i.val-1,by omega⟩
    have he : center j=i := by apply Fin.ext; dsimp [center,j]; omega
    have hLip : LipschitzWith 1 (fun p : B => (T p).val i) := by
      apply LipschitzWith.of_dist_le_mul
      intro p s
      change dist (node g q p i) (node g q s i) ≤ _
      rw [←he,node_center,node_center]
      have hp := neighbors_in_ball hr q hnear p j
      have hs := neighbors_in_ball hr q hnear s j
      have hh := hcat.midpoint_lipschitz g hp.1 hp.2 hs.1 hs.2
      have h1 : dist (p.val (left j)) (s.val (left j))≤dist p s := dist_le_pi_dist p.val s.val _
      have h2 : dist (p.val (right j)) (s.val (right j))≤dist p s := dist_le_pi_dist p.val s.val _
      norm_num
      linarith
    exact hLip.continuous
  obtain ⟨p,hp⟩ := FiniteMidpointFixedPoint.exists_fixed n (fun p : B => p.val)
    (fun i => (continuous_apply i).comp continuous_subtype_val) Subtype.val_injective T hT
    (fun p s => by simp [T,node_zero]) (fun p s => by simp [T,node_last])
    (fun p s i => by
      change dist (node g q p (center i)) (node g q s (center i))≤_
      rw [node_center,node_center]
      have hp := neighbors_in_ball hr q hnear p i
      have hs := neighbors_in_ball hr q hnear s i
      exact hcat.midpoint_lipschitz g hp.1 hp.2 hs.1 hs.2)
  refine ⟨p.val,p.property,fun i => ?_⟩
  have hh := congrArg (fun p : B => p.val (center i)) hp
  simpa only [T,node_center] using hh.symm

end LocalPolygonContinuation
end

section

/-! Local CAT(0) comparison globalizes once the geodesic producer has supplied
radial Busemann contraction. This is the exact small-scale CN argument; it does
not assume global CAT(0), properness, or a Cartan--Hadamard theorem. -/
open Set
variable {X : Type*} [MetricSpace X]

lemma IsSegment.reparam {γ : ℝ → X} {x y : X} (h : IsSegment γ x y)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    IsSegment (fun u => γ ((1-u)*s+u*t)) (γ s) (γ t) := by
  refine ⟨by simp,by simp,?_⟩
  intro u hu v hv
  have hm (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) : (1-a)*s+a*t ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg (by linarith [ha.2]) hs.1) (mul_nonneg ha.1 ht.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hs.2),
        mul_nonneg ha.1 (sub_nonneg.mpr ht.2)]
  rw [h.2.2 _ (hm u hu) _ (hm v hv),h.2.2 s hs t ht]
  rw [show (1-u)*s+u*t-((1-v)*s+v*t)=(u-v)*(t-s) by ring,abs_mul,abs_sub_comm t s]
  ring

lemma IsSegment.dist_from_source {γ : ℝ → X} {x y : X} (h : IsSegment γ x y)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : dist x (γ t)=t*dist x y := by
  have hh := h.2.2 0 (by norm_num) t ht
  simpa only [h.1,zero_sub,abs_neg,abs_of_nonneg ht.1] using hh

lemma catZero_of_segment_midpoint (g : IsGeodesic X)
    (h : ∀ {γ : ℝ → X} {x y : X}, IsSegment γ x y → ∀ z : X,
      dist z (γ (1/2))^2 ≤ (dist z x^2+dist z y^2)/2-dist x y^2/4) : CATZero X := by
  intro x y
  obtain ⟨γ,hγ⟩ := g x y
  refine ⟨γ,hγ,fun z t ht => ?_⟩
  let F : ℝ → ℝ := fun s => dist z (γ s)^2-
    ((1-s)*dist z x^2+s*dist z y^2-s*(1-s)*dist x y^2)
  have hF : ContinuousOn F (Icc 0 1) := by
    apply ContinuousOn.sub
    · exact (continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγ.continuousOn)).pow 2
    · fun_prop
  have hf0 : F 0≤0 := by simp [F,hγ.1]
  have hf1 : F 1≤0 := by simp [F,hγ.2.1]
  have hm : ∀ a ∈ Icc (0:ℝ) 1, ∀ b ∈ Icc (0:ℝ) 1, F ((a+b)/2)≤(F a+F b)/2 := by
    intro a ha b hb
    have hh := h (hγ.reparam ha hb) z
    simp only [show (1-(1/2:ℝ))*a+(1/2)*b=(a+b)/2 by ring] at hh
    rw [hγ.2.2 a ha b hb,mul_pow,sq_abs] at hh
    dsimp [F]
    nlinarith
  have hh := CurvatureComparison.midpoint_nonpos hF hm hf0 hf1 t ht
  dsimp [F] at hh
  linarith

/-- Radial comparison for any two constant-speed geodesics with common start. -/
def RadialBusemann (X : Type*) [MetricSpace X] : Prop :=
  ∀ (o x y : X) (α β : ℝ → X), IsSegment α o x → IsSegment β o y →
    ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t) ≤ t*dist x y

/-- Small-scale comparison plus the constructed global radial contraction is
sufficient for the literal whole-segment CAT(0) definition. -/
theorem catZero_of_local_radial (g : IsGeodesic X) (hb : RadialBusemann X)
    (hl : ∀ x : X, ∃ r : ℝ, 0<r ∧ CATZero (Metric.ball x r)) : CATZero X := by
  apply catZero_of_segment_midpoint g
  intro γ x y hγ z
  let m := γ (1/2)
  obtain ⟨r,hr,hcat⟩ := hl m
  let α : ℝ → X := fun u => γ ((1-u)*(1/2)+u*0)
  let β : ℝ → X := fun u => γ ((1-u)*(1/2)+u*1)
  have hα : IsSegment α m x := by simpa [α,m,hγ.1] using hγ.reparam (by norm_num : (1/2:ℝ) ∈ Icc 0 1) (by norm_num : (0:ℝ) ∈ Icc 0 1)
  have hβ : IsSegment β m y := by simpa [β,m,hγ.2.1] using hγ.reparam (by norm_num : (1/2:ℝ) ∈ Icc 0 1) (by norm_num : (1:ℝ) ∈ Icc 0 1)
  obtain ⟨δ,hδ⟩ := g m z
  have hmx : dist m x=dist x y/2 := by
    have hh := hγ.2.2 (1/2) (by norm_num) 0 (by norm_num)
    simpa [m,hγ.1,div_eq_mul_inv,mul_comm] using hh
  have hmy : dist m y=dist x y/2 := by
    have hh := hγ.2.2 (1/2) (by norm_num) 1 (by norm_num)
    norm_num at hh
    simpa [m,hγ.2.1,div_eq_mul_inv,mul_comm] using hh
  let R : ℝ := 1+dist x y+dist m z
  have hR : 0<R := by dsimp [R]; linarith [dist_nonneg (x:=x) (y:=y),dist_nonneg (x:=m) (y:=z)]
  let t : ℝ := min (1/2) (r/(2*R))
  have ht0 : 0<t := lt_min (by norm_num) (div_pos hr (by positivity))
  have ht1 : t≤1 := (min_le_left _ _).trans (by norm_num)
  have ht : t ∈ Icc (0:ℝ) 1 := ⟨ht0.le,ht1⟩
  have htR : t*R≤r/2 := by
    have hh := (le_div_iff₀ (by positivity : 0<2*R)).mp (min_le_right (1/2:ℝ) (r/(2*R)))
    change t*(2*R)≤r at hh
    linarith
  have hdx : dist m (α t)=t*dist x y/2 := by rw [hα.dist_from_source ht,hmx]; ring
  have hdy : dist m (β t)=t*dist x y/2 := by rw [hβ.dist_from_source ht,hmy]; ring
  have hdz : dist m (δ t)=t*dist m z := hδ.dist_from_source ht
  have hxy : dist (α t) (β t)=t*dist x y := by
    have htlo : (1-t)*(1/2)+t*0 ∈ Icc (0:ℝ) 1 := ⟨by nlinarith [ht.2],by nlinarith [ht.1]⟩
    have hthi : (1-t)*(1/2)+t*1 ∈ Icc (0:ℝ) 1 := ⟨by nlinarith [ht.1],by nlinarith [ht.2]⟩
    dsimp [α,β]
    rw [hγ.2.2 _ htlo _ hthi,show (1-t)*(1/2)+t*0-((1-t)*(1/2)+t*1) = -t by ring,
      abs_neg,abs_of_nonneg ht0.le]
  have ha : α t ∈ Metric.ball m r := by
    rw [Metric.mem_ball,dist_comm,hdx]
    have hh : dist x y≤R := by dsimp [R]; linarith [dist_nonneg (x:=m) (y:=z)]
    nlinarith [mul_le_mul_of_nonneg_left hh ht0.le,dist_nonneg (x:=x) (y:=y)]
  have hc : β t ∈ Metric.ball m r := by
    rw [Metric.mem_ball,dist_comm,hdy]
    have hh : dist x y≤R := by dsimp [R]; linarith [dist_nonneg (x:=m) (y:=z)]
    nlinarith [mul_le_mul_of_nonneg_left hh ht0.le,dist_nonneg (x:=x) (y:=y)]
  have hz : δ t ∈ Metric.ball m r := by
    rw [Metric.mem_ball,dist_comm,hdz]
    have hh : dist m z≤R := by dsimp [R]; linarith [dist_nonneg (x:=x) (y:=y)]
    linarith [mul_le_mul_of_nonneg_left hh ht0.le]
  have hm : m ∈ Metric.ball m r := Metric.mem_ball_self hr
  have hcn := CATZero.cn_of_dist hcat (x:=⟨α t,ha⟩) (y:=⟨β t,hc⟩) (p:=⟨m,hm⟩) ⟨δ t,hz⟩
    (t:=1/2) (by norm_num)
    (show dist (α t) m=(1/2)*dist (α t) (β t) by rw [dist_comm,hdx,hxy]; ring)
    (show dist m (β t)=(1-1/2)*dist (α t) (β t) by rw [hdy,hxy]; ring)
  change dist (δ t) m^2 ≤ (1-1/2)*dist (δ t) (α t)^2+(1/2)*dist (δ t) (β t)^2-
    (1/2)*(1-1/2)*dist (α t) (β t)^2 at hcn
  rw [dist_comm (δ t) m,hdz,hxy] at hcn
  have hxa := hb m z x δ α hδ hα t ht
  have hya := hb m z y δ β hδ hβ t ht
  have hx2 := (sq_le_sq₀ (dist_nonneg (x:=δ t) (y:=α t)) (by positivity)).mpr hxa
  have hy2 := (sq_le_sq₀ (dist_nonneg (x:=δ t) (y:=β t)) (by positivity)).mpr hya
  have hres : t^2*(dist m z^2-((dist z x^2+dist z y^2)/2-dist x y^2/4))≤0 := by
    nlinarith
  have hh : dist m z^2-((dist z x^2+dist z y^2)/2-dist x y^2/4)≤0 := by
    by_contra! hpos
    exact (not_lt_of_ge hres) (mul_pos (sq_pos_of_pos ht0) hpos)
  dsimp [m] at hh
  rw [dist_comm (γ (1/2)) z] at hh
  linarith

end

namespace CurvatureComparison
open Set
lemma local_midpoint_nonpos {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    {δ : ℝ} (hδ : 0<δ)
    (hmid : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s-t|<δ →
      f ((s+t)/2) ≤ (f s+f t)/2) (h0 : f 0≤0) (h1 : f 1≤0) :
    ∀ t ∈ Icc (0:ℝ) 1, f t≤0 := by
  intro t ht
  by_contra! hpos
  let ε := f t/2
  have he : 0<ε := by dsimp [ε]; positivity
  let g : ℝ → ℝ := fun s => f s+ε*s^2
  have hg : ContinuousOn g (Icc 0 1) :=
    hf.add ((continuous_const.mul (continuous_id.pow 2)).continuousOn)
  obtain ⟨x,hx,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1)) hg
  have hlarge : ε<g x := by
    have hh := hm ht
    have hn : 0≤ε*t^2 := mul_nonneg he.le (sq_nonneg t)
    dsimp [g,ε] at *
    linarith
  have hx0 : 0<x := by
    by_contra hh
    have heq : x=0 := le_antisymm (not_lt.mp hh) hx.1
    subst x
    simp only [g,zero_pow (by decide : 2≠0),mul_zero,add_zero] at hlarge
    linarith
  have hx1 : x<1 := by
    by_contra hh
    have heq : x=1 := le_antisymm hx.2 (not_lt.mp hh)
    subst x
    simp only [g,one_pow,mul_one] at hlarge
    linarith
  let r := min (min x (1-x)) δ/4
  have hr : 0<r := by dsimp [r]; exact div_pos (lt_min (lt_min hx0 (sub_pos.mpr hx1)) hδ) (by norm_num)
  have hrx : r≤x := by
    have hh := (min_le_left (min x (1-x)) δ).trans (min_le_left x (1-x))
    dsimp [r]; linarith
  have hr1 : r≤1-x := by
    have hh := (min_le_left (min x (1-x)) δ).trans (min_le_right x (1-x))
    dsimp [r]; linarith
  have hrδ : 2*r<δ := by have hh := min_le_right (min x (1-x)) δ; dsimp [r]; linarith
  have hl : x-r ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hu : x+r ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have ha : |(x-r)-(x+r)|<δ := by rw [show (x-r)-(x+r)=-(2*r) by ring,abs_neg,abs_of_pos (by positivity)]; exact hrδ
  have hcv := hmid (x-r) hl (x+r) hu ha
  rw [show ((x-r)+(x+r))/2=x by ring] at hcv
  have hml := hm hl
  have hmu := hm hu
  have hp : 0<ε*r^2 := mul_pos he (sq_pos_of_pos hr)
  dsimp [g] at hml hmu
  nlinarith

lemma local_midpoint_chord {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    {δ : ℝ} (hδ : 0<δ)
    (hmid : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s-t|<δ →
      f ((s+t)/2)≤(f s+f t)/2) :
    ∀ t ∈ Icc (0:ℝ) 1, f t≤(1-t)*f 0+t*f 1 := by
  let g : ℝ → ℝ := fun t => f t-((1-t)*f 0+t*f 1)
  have hg : ContinuousOn g (Icc 0 1) := hf.sub (by fun_prop)
  have hm : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s-t|<δ →
      g ((s+t)/2)≤(g s+g t)/2 := by
    intro s hs t ht hst
    have hh := hmid s hs t ht hst
    dsimp [g]
    linarith
  intro t ht
  have hh := local_midpoint_nonpos hg hδ hm (by simp [g]) (by simp [g]) t ht
  dsimp [g] at hh
  linarith
end CurvatureComparison

section

/-! Constant-speed local geodesics and their genuine nearby uniqueness.
No covering, global comparison, or globalization conclusion is assumed. -/
open Set Metric
variable {X : Type*} [MetricSpace X]

/-- A uniformly locally constant-speed geodesic on the unit interval. -/
structure IsLocalSegment (γ : ℝ → X) (L : ℝ) : Prop where
  nonneg : 0≤L
  continuousOn : ContinuousOn γ (Icc 0 1)
  local_dist : ∃ ε : ℝ, 0<ε ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
    |s-t|<ε → dist (γ s) (γ t)=|s-t| *L

lemma IsSegment.isLocalSegment {γ : ℝ → X} {a b : X} (h : IsSegment γ a b) :
    IsLocalSegment γ (dist a b) :=
  ⟨dist_nonneg,h.continuousOn,1,by norm_num,fun s hs t ht _ => h.2.2 s hs t ht⟩

lemma UniformLocalCATZero.eq_midpoint_of_dist {r : ℝ} (h : UniformLocalCATZero (X:=X) r)
    (g : IsGeodesic X) {o a b p : X}
    (ha : a ∈ ball o (r/3)) (hb : b ∈ ball o (r/3)) (hp : p ∈ ball o (r/3))
    (hpa : dist a p=dist a b/2) (hpb : dist p b=dist a b/2) : p=g.midpoint a b := by
  have hr : 0<r := by rw [mem_ball] at ha; linarith [dist_nonneg (x:=a) (y:=o)]
  obtain ⟨U,hU,hcat⟩ := h o
  have sub : ball o (r/3) ⊆ U := (ball_subset_ball (by linarith)).trans hU
  have he : (⟨p,sub hp⟩ : U)=CATZero.mid hcat ⟨a,sub ha⟩ ⟨b,sub hb⟩ := by
    apply CATZero.eq_segment_of_dist hcat (by norm_num : (1/2:ℝ) ∈ Icc 0 1)
    · change dist a p=(1/2)*dist a b
      rw [hpa]; ring
    · change dist p b=(1-1/2)*dist a b
      rw [hpb]; ring
  have hm := midpoint_eq_subtype hcat g (sub ha) (sub hb) (hU (g.midpoint_mem_ball ha hb))
  exact congrArg Subtype.val (he.trans hm.symm)

lemma IsLocalSegment.close_chord {α β : ℝ → X} {A B r : ℝ}
    (hα : IsLocalSegment α A) (hβ : IsLocalSegment β B)
    (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
    (hclose : ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t)<r/10) :
    ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t)≤
      (1-t)*dist (α 0) (β 0)+t*dist (α 1) (β 1) := by
  obtain ⟨εa,hea,hda⟩ := hα.local_dist
  obtain ⟨εb,heb,hdb⟩ := hβ.local_dist
  let R := 1+A+B
  have hR : 0<R := by dsimp [R]; linarith [hα.nonneg,hβ.nonneg]
  let δ := min εa (min εb (r/(20*R)))
  have hδ : 0<δ := lt_min hea (lt_min heb (div_pos hr (by positivity)))
  apply CurvatureComparison.local_midpoint_chord (continuous_dist.comp_continuousOn (hα.continuousOn.prodMk hβ.continuousOn)) hδ
  intro s hs t ht hst
  let m := (s+t)/2
  have hm : m ∈ Icc (0:ℝ) 1 := ⟨by dsimp [m]; linarith [hs.1,ht.1],by dsimp [m]; linarith [hs.2,ht.2]⟩
  have hsm : |s-m|=|s-t|/2 := by rw [show s-m=(s-t)/2 by dsimp [m]; ring,abs_div]; norm_num
  have hmt : |m-t|=|s-t|/2 := by rw [show m-t=(s-t)/2 by dsimp [m]; ring,abs_div]; norm_num
  have hsta : |s-t|<εa := hst.trans_le (min_le_left _ _)
  have hstb : |s-t|<εb := hst.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hstr : |s-t| *R<r/20 := by
    have hh := hst.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (lt_div_iff₀ (by positivity : 0<20*R)).mp hh
    linarith
  have haa : |s-t| *A<r/20 := by
    have he : A≤R := by dsimp [R]; linarith [hβ.nonneg]
    nlinarith [mul_le_mul_of_nonneg_left he (abs_nonneg (s-t))]
  have hbb : |s-t| *B<r/20 := by
    have he : B≤R := by dsimp [R]; linarith [hα.nonneg]
    nlinarith [mul_le_mul_of_nonneg_left he (abs_nonneg (s-t))]
  have ha₁ : dist (α s) (α m)=|s-t|/2*A := by
    rw [hda s hs m hm (by rw [hsm]; linarith [abs_nonneg (s-t)]),hsm]
  have ha₂ : dist (α m) (α t)=|s-t|/2*A := by
    rw [hda m hm t ht (by rw [hmt]; linarith [abs_nonneg (s-t)]),hmt]
  have hb₁ : dist (β s) (β m)=|s-t|/2*B := by
    rw [hdb s hs m hm (by rw [hsm]; linarith [abs_nonneg (s-t)]),hsm]
  have hb₂ : dist (β m) (β t)=|s-t|/2*B := by
    rw [hdb m hm t ht (by rw [hmt]; linarith [abs_nonneg (s-t)]),hmt]
  have has : α s ∈ ball (α m) (r/3) := by rw [mem_ball,ha₁]; nlinarith [mul_nonneg (abs_nonneg (s-t)) hα.nonneg]
  have hat : α t ∈ ball (α m) (r/3) := by rw [mem_ball,dist_comm,ha₂]; nlinarith [mul_nonneg (abs_nonneg (s-t)) hα.nonneg]
  have hbs : β s ∈ ball (α m) (r/3) := by
    rw [mem_ball]
    have hh := dist_triangle (β s) (β m) (α m)
    rw [hb₁,dist_comm (β m) (α m)] at hh
    nlinarith [hclose m hm,mul_nonneg (abs_nonneg (s-t)) hβ.nonneg]
  have hbt : β t ∈ ball (α m) (r/3) := by
    rw [mem_ball]
    have hh := dist_triangle (β t) (β m) (α m)
    rw [dist_comm (β t) (β m),hb₂,dist_comm (β m) (α m)] at hh
    nlinarith [hclose m hm,mul_nonneg (abs_nonneg (s-t)) hβ.nonneg]
  have ham : α m ∈ ball (α m) (r/3) := mem_ball_self (by positivity)
  have hbm : β m ∈ ball (α m) (r/3) := by rw [mem_ball,dist_comm]; linarith [hclose m hm]
  have hemα : α m=g.midpoint (α s) (α t) := hc.eq_midpoint_of_dist g has hat ham
    (by rw [ha₁,hda s hs t ht hsta]; ring) (by rw [ha₂,hda s hs t ht hsta]; ring)
  have hemβ : β m=g.midpoint (β s) (β t) := hc.eq_midpoint_of_dist g hbs hbt hbm
    (by rw [hb₁,hdb s hs t ht hstb]; ring) (by rw [hb₂,hdb s hs t ht hstb]; ring)
  change dist (α m) (β m)≤_
  rw [hemα,hemβ]
  exact hc.midpoint_lipschitz g has hat hbs hbt

lemma IsLocalSegment.close_unique {α β : ℝ → X} {A B r : ℝ}
    (hα : IsLocalSegment α A) (hβ : IsLocalSegment β B)
    (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
    (hclose : ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t)<r/10)
    (h0 : α 0=β 0) (h1 : α 1=β 1) : Set.EqOn α β (Icc 0 1) := by
  intro t ht
  have hh := hα.close_chord hβ hr hc g hclose t ht
  rw [h0,h1,dist_self,dist_self,mul_zero,mul_zero,add_zero] at hh
  exact dist_eq_zero.mp (le_antisymm hh dist_nonneg)

end

/-! Literal equal-time interpolation of finite geodesic polygons. -/
open Set Metric
namespace SegmentChain
variable {X : Type*} [MetricSpace X] {N : ℕ} (hN : 0 < N)

include hN

lemma interval_cover {t : ℝ} (ht : t ∈ Icc (0:ℝ) N) :
    ∃ i : Fin N, t ∈ Icc (i:ℝ) ((i:ℝ)+1) := by
  by_cases hl : t < (N:ℝ)
  · have hi : ⌊t⌋₊ < N := by
      have hh := Nat.floor_le ht.1
      exact_mod_cast lt_of_le_of_lt hh hl
    exact ⟨⟨⌊t⌋₊,hi⟩,Nat.floor_le ht.1,(Nat.lt_floor_add_one t).le⟩
  · have he : t=(N:ℝ) := le_antisymm ht.2 (not_lt.mp hl)
    have hi : N-1 < N := by omega
    refine ⟨⟨N-1,hi⟩,?_⟩
    have hn : ((N-1:ℕ):ℝ)+1=N := by exact_mod_cast (show N-1+1=N by omega)
    change (N-1:ℕ) ≤ t ∧ t ≤ (N-1:ℕ)+1
    rw [he]
    constructor  <;>  linarith

lemma interval_union : (⋃ i : Fin N, Icc (i:ℝ) ((i:ℝ)+1))=Icc (0:ℝ) N := by
  ext t
  constructor
  · intro ht
    obtain ⟨i,hi⟩ := mem_iUnion.mp ht
    have h0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
    have h1 : (i:ℝ)+1 ≤ N := by exact_mod_cast (show i.val+1 ≤ N from i.isLt)
    exact ⟨le_trans h0 hi.1,le_trans hi.2 h1⟩
  · intro ht
    obtain ⟨i,hi⟩ := interval_cover hN ht
    exact mem_iUnion.mpr ⟨i,hi⟩

variable (p : ℕ → X) (γ : ℕ → ℝ → X)
  (hg : ∀ i, i < N → IsSegment (γ i) (p i) (p (i+1)))

private def cell (t : ℝ) (ht : t ∈ Icc (0:ℝ) N) : Fin N := (interval_cover hN ht).choose
private lemma cell_mem (t : ℝ) (ht : t ∈ Icc (0:ℝ) N) :
    t ∈ Icc ((cell hN t ht):ℝ) ((cell hN t ht:ℝ)+1) := (interval_cover hN ht).choose_spec

def curve (t : ℝ) : X :=
  if ht : t ∈ Icc (0:ℝ) N then γ (cell hN t ht) (t-(cell hN t ht:ℝ)) else p 0

include hg

omit hN in
lemma compatible (i j : Fin N) {t : ℝ}
    (hi : t ∈ Icc (i:ℝ) ((i:ℝ)+1)) (hj : t ∈ Icc (j:ℝ) ((j:ℝ)+1)) :
    γ i (t-(i:ℝ))=γ j (t-(j:ℝ)) := by
  rcases lt_trichotomy i.val j.val with hlt|he|hgt
  · have hle : (i:ℝ)+1 ≤ j := by exact_mod_cast (show i.val+1 ≤ j.val from hlt)
    have ht : t=(j:ℝ) := by linarith [hi.2,hj.1]
    have hei : (j:ℝ)=(i:ℝ)+1 := by linarith [hi.2,hj.1]
    have heij : j.val=i.val+1 := by exact_mod_cast hei
    rw [ht,sub_self,(hg j j.isLt).1,hei,show (i:ℝ)+1-(i:ℝ)=1 by ring,(hg i i.isLt).2.1,heij]
  · have he' : i=j := Fin.ext he
    rw [he']
  · have hle : (j:ℝ)+1 ≤ i := by exact_mod_cast (show j.val+1 ≤ i.val from hgt)
    have ht : t=(i:ℝ) := by linarith [hj.2,hi.1]
    have hej : (i:ℝ)=(j:ℝ)+1 := by linarith [hj.2,hi.1]
    have heji : i.val=j.val+1 := by exact_mod_cast hej
    rw [ht,sub_self,(hg i i.isLt).1,hej,show (j:ℝ)+1-(j:ℝ)=1 by ring,(hg j j.isLt).2.1,heji]

lemma curve_eq (i : Fin N) {t : ℝ} (hi : t ∈ Icc (i:ℝ) ((i:ℝ)+1)) :
    curve hN p γ t=γ i (t-(i:ℝ)) := by
  have ht : t ∈ Icc (0:ℝ) N := by
    rw [←interval_union hN]
    exact mem_iUnion.mpr ⟨i,hi⟩
  rw [curve,dite_eq_left ht]
  exact compatible p γ hg (cell hN t ht) i (cell_mem hN t ht) hi

lemma curve_continuousOn : ContinuousOn (curve hN p γ) (Icc (0:ℝ) N) := by
  rw [←interval_union hN]
  apply (locallyFinite_of_finite (fun i : Fin N =>  Icc (i:ℝ) ((i:ℝ)+1))).continuousOn_iUnion
    (fun _ =>  isClosed_Icc)
  intro i
  have hh : ContinuousOn (fun t : ℝ =>  γ i (t-(i:ℝ))) (Icc (i:ℝ) ((i:ℝ)+1)) :=
    (hg i i.isLt).continuousOn.comp (continuous_id.sub continuous_const).continuousOn
      (fun t ht =>  ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  apply hh.congr
  intro t ht
  exact curve_eq hN p γ hg i ht

lemma curve_zero : curve hN p γ 0=p 0 := by
  let i : Fin N := ⟨0,hN⟩
  rw [curve_eq hN p γ hg i (by simp [i])]
  simpa [i] using (hg 0 hN).1

lemma curve_last : curve hN p γ N=p N := by
  let i : Fin N := ⟨N-1,by omega⟩
  have he : (N-1:ℕ)+1=N := by omega
  have her : ((N-1:ℕ):ℝ)+1=N := by exact_mod_cast he
  have hi : (N:ℝ) ∈ Icc (i:ℝ) ((i:ℝ)+1) := by change (N-1:ℕ) ≤ (N:ℝ) ∧ (N:ℝ) ≤ (N-1:ℕ)+1; constructor  <;>  linarith
  rw [curve_eq hN p γ hg i hi]
  have harg : (N:ℝ)-(i:ℝ)=1 := by dsimp [i]; linarith
  rw [harg,(hg i i.isLt).2.1]
  exact congrArg p he

lemma curve_node (j : ℕ) (hj : j ≤ N) : curve hN p γ j=p j := by
  by_cases hlt : j < N
  · let i : Fin N := ⟨j,hlt⟩
    rw [curve_eq hN p γ hg i (by simp [i])]
    simpa [i] using (hg j hlt).1
  · have he : j=N := by omega
    rw [he,curve_last hN p γ hg]

/-- The literal interpolation on the unit interval. -/
def unitCurve (t : ℝ) : X := curve hN p γ ((N:ℝ)*t)

lemma unitCurve_continuousOn : ContinuousOn (unitCurve hN p γ) (Icc (0:ℝ) 1) := by
  apply (curve_continuousOn hN p γ hg).comp (continuous_const.mul continuous_id).continuousOn
  intro t ht
  change 0 ≤ (N:ℝ)*t ∧ (N:ℝ)*t ≤ N
  exact ⟨mul_nonneg (Nat.cast_nonneg _) ht.1,by nlinarith [(Nat.cast_pos.mpr hN : (0:ℝ) < N),ht.2]⟩

lemma unitCurve_zero : unitCurve hN p γ 0=p 0 := by simpa [unitCurve] using curve_zero hN p γ hg
lemma unitCurve_one : unitCurve hN p γ 1=p N := by simpa [unitCurve] using curve_last hN p γ hg

end SegmentChain

end HyperbolicObstruction

end

end OAI
