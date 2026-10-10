import Mathlib
import OAI.Algebra.GroupRing.ChunkComparisons

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainActiveStages
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open StageSubgraphs
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "col" => color Γ mark h2 paths
local notation "e" => ListStageExponents.edge paths
local notation "m" => StageSubgraphs.multiplicity (S) e
abbrev ActiveChain (j : ℕ) := {c : R // j < ChunkComparisons.multiplicity col c}
local notation "A" => ActiveChain Γ mark h2 paths

/-- Literal active chain orientations, with no padding by inactive chains. -/
def activeOrientation (j : ℕ) : ActiveD m j ≃ A j × Bool where
  toFun d := (⟨representative Γ mark h2 d.val,by
    rw [←multiplicity_at Γ mark h2 paths]; exact d.property⟩,reversed Γ mark h2 d.val)
  invFun c := ⟨orientation Γ mark h2 (c.1.val,c.2),by
    rw [multiplicity_at Γ mark h2 paths]
    change j < ChunkComparisons.multiplicity col (((orientation Γ mark h2).symm ((orientation Γ mark h2) (c.1.val,c.2))).1)
    rw [Equiv.symm_apply_apply]
    exact c.1.property⟩
  left_inv d := by
    apply Subtype.ext
    exact (orientation Γ mark h2).apply_symm_apply d.val
  right_inv c := by
    apply Prod.ext
    · apply Subtype.ext
      change ((orientation Γ mark h2).symm ((orientation Γ mark h2) (c.1.val,c.2))).1=c.1.val
      rw [Equiv.symm_apply_apply]
    · change ((orientation Γ mark h2).symm ((orientation Γ mark h2) (c.1.val,c.2))).2=c.2
      rw [Equiv.symm_apply_apply]

variable [Fintype V]

omit [Fintype V] in
lemma edges_card (j : ℕ) :
    (edges (stage (S) m (multiplicity_reverse (S) e) j)).card=Fintype.card (A j) := by
  have ha := Fintype.card_congr (activeOrientation Γ mark h2 paths j)
  rw [Fintype.card_prod,Fintype.card_bool] at ha
  have he := two_edges (stage (S) m (multiplicity_reverse (S) e) j)
  omega

def first (j : ℕ) (c : A j) : ActiveV (S) m j :=
  ⟨ChainIsomorphism.first Γ mark h2 c.val,c.val.val,rfl,by
    rw [multiplicity_eq Γ mark h2 paths]; exact c.property⟩

def last (j : ℕ) (c : A j) : ActiveV (S) m j :=
  ⟨ChainIsomorphism.last Γ mark h2 c.val,(S).reverse c.val.val,rfl,by
    rw [multiplicity_reverse,multiplicity_eq Γ mark h2 paths]; exact c.property⟩

omit [Fintype V] in
lemma incident (j : ℕ) (v : ActiveV (S) m j) :
    ∃ c : A j, first Γ mark h2 paths j c=v ∨ last Γ mark h2 paths j c=v := by
  rcases v.property with ⟨d,hd,hm⟩
  let c : A j := ⟨representative Γ mark h2 d,by rwa [←multiplicity_at Γ mark h2 paths]⟩
  refine ⟨c,?_⟩
  have h := oriented Γ mark h2 d
  cases hr : reversed Γ mark h2 d
  · left
    apply Subtype.ext
    change (S).origin c.val.val=v.val
    simp only [hr,Bool.false_eq_true,ite_false] at h
    change d=c.val.val at h
    rw [←h,hd]
  · right
    apply Subtype.ext
    change (S).origin ((S).reverse c.val.val)=v.val
    simp only [hr,ite_true] at h
    change d=(S).reverse c.val.val at h
    rw [←h,hd]

/-- The signed exponent counted by the chain expectation is exactly the one
bounded by immersed path incidence, including the first-stage root saving. -/
theorem exponent_nonpos (hp : ∀ i,paths i≠[]) (cyclic : P → Bool)
    (hc : ∀ i,(paths i).IsChain (WeightedMoore.PortWalk.step (S).origin (S).reverse))
    (hclose : ∀ i,cyclic i=true → ∀ᵉ (x∈(paths i).getLast?) (y∈(paths i).head?),
      WeightedMoore.PortWalk.step (S).origin (S).reverse x y)
    (M : ℕ) (hM : 0<M) (hm : ∀ c : R,ChunkComparisons.multiplicity col c ≤ M) :
    (∑ j : Fin M, ((Fintype.card (ActiveV (S) m j.val):ℤ)-Fintype.card (A j.val)-
      if j.val=0 then Fintype.card {i : P // cyclic i=false} else 0)) ≤ 0 := by
  have hd : ∀ d,m d ≤ M := by
    intro d
    rw [multiplicity_at Γ mark h2 paths]
    exact hm _
  have h := ListStageExponents.exponent_nonpos (S) paths hp cyclic hc hclose M hM hd
  simpa only [ListStageExponents.mult,edges_card Γ mark h2 paths] using h

end TorsionFreeZeroDivisors.ChainActiveStages

namespace TorsionFreeZeroDivisors.SubdivisionRestriction
open scoped Classical
open ChainSubdivision
variable {C V : Type*} (len : C → ℕ) (first last : C → V)
    (active : C → Prop) (incident : V → Prop)
    (hf : ∀ c,active c → incident (first c))
    (hl : ∀ c,active c → incident (last c))

abbrev length : {c // active c} → ℕ := fun c => len c.val
def firstPoint (c : {c // active c}) : {v // incident v} := ⟨first c.val,hf _ c.property⟩
def lastPoint (c : {c // active c}) : {v // incident v} := ⟨last c.val,hl _ c.property⟩

local notation "P" => graph len first last
local notation "Q" => graph (length len active) (firstPoint first active incident hf) (lastPoint last active incident hl)

def vertex : Vertex (length len active) (V := {v // incident v}) → Vertex len (V := V)
  | .inl v => .inl v.val
  | .inr ⟨c,i⟩ => .inr ⟨c.val,i⟩

def dart : Dart (length len active) → Dart len := fun d => (⟨d.1.1.val,d.1.2⟩,d.2)

lemma vertex_injective : Function.Injective (vertex len active incident) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
    | inr w => cases h
  | inr v =>
    cases w with
    | inl w => cases h
    | inr w =>
      rcases v with ⟨⟨c,hc⟩,i⟩
      rcases w with ⟨⟨d,hd⟩,k⟩
      have h' := Sum.inr.inj h
      have hcd := congrArg Sigma.fst h'
      cases hcd
      have hik : i=k := eq_of_heq (Sigma.mk.inj_iff.mp h').2
      cases hik
      rfl

lemma dart_injective : Function.Injective (dart len active) := by
  rintro ⟨⟨⟨c,hc⟩,i⟩,r⟩ ⟨⟨⟨d,hd⟩,k⟩,s⟩ h
  have hrs := congrArg Prod.snd h
  cases hrs
  have h' := congrArg Prod.fst h
  have hcd := congrArg Sigma.fst h'
  cases hcd
  have hik : i=k := eq_of_heq (Sigma.mk.inj_iff.mp h').2
  cases hik
  rfl

lemma point_map (c : {c // active c}) (k : Fin ((length len active) c+1)) :
    vertex len active incident
      (point (length len active) (firstPoint first active incident hf) (lastPoint last active incident hl) c k) =
      point len first last c.val k := by
  unfold point
  split_ifs <;> rfl

lemma origin_map (d : Dart (length len active)) :
    vertex len active incident ((Q).origin d)=(P).origin (dart len active d) := by
  rcases d with ⟨⟨c,i⟩,r⟩
  cases r
  · simpa only [dart,origin_forward] using
      point_map len first last active incident hf hl c ⟨i.val,by have h:=i.isLt; omega⟩
  · simpa only [dart,origin_backward] using
      point_map len first last active incident hf hl c ⟨i.val+1,by have h:=i.isLt; omega⟩

lemma reverse_map (d : Dart (length len active)) :
    dart len active ((Q).reverse d)=(P).reverse (dart len active d) := rfl

end TorsionFreeZeroDivisors.SubdivisionRestriction

namespace TorsionFreeZeroDivisors.ChainStageEmbedding
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open StageSubgraphs
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "col" => color Γ mark h2 paths
local notation "e" => ListStageExponents.edge paths
local notation "m" => StageSubgraphs.multiplicity (S) e
local notation "A" => ChainActiveStages.ActiveChain Γ mark h2 paths j
local notation "W" => ActiveV (S) m j

abbrev length : A → ℕ := fun c => repLength Γ mark h2 c.val
abbrev graph := ChainSubdivision.graph (length Γ mark h2 paths j)
  (ChainActiveStages.first Γ mark h2 paths j) (ChainActiveStages.last Γ mark h2 paths j)
local notation "Q" => graph Γ mark h2 paths j

abbrev active (c : R) : Prop := j<ChunkComparisons.multiplicity col c
def marked (v : W) : Mark mark := ⟨v.val,by
  rcases v.property with ⟨d,hd,_⟩
  rw [←hd]
  exact (turn_fixed_iff Γ.origin mark h2 d.val).mp d.property⟩

lemma marked_injective : Injective (marked Γ mark h2 paths j) := by
  intro v w h
  apply Subtype.ext
  exact congrArg (fun z : Mark mark => z.val) h

def vertexLift : ChainSubdivision.Vertex (length Γ mark h2 paths j) (V := W) →
    ChainSubdivision.Vertex (repLength Γ mark h2) (V := Mark mark)
  | .inl v => .inl (marked Γ mark h2 paths j v)
  | .inr ⟨c,i⟩ => .inr ⟨c.val,i⟩

lemma vertexLift_injective : Injective (vertexLift Γ mark h2 paths j) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w => exact congrArg Sum.inl (marked_injective Γ mark h2 paths j (Sum.inl.inj h))
    | inr w => cases h
  | inr v =>
    cases w with
    | inl w => cases h
    | inr w =>
      rcases v with ⟨⟨c,hc⟩,i⟩
      rcases w with ⟨⟨d,hd⟩,k⟩
      have h' := Sum.inr.inj h
      have hcd := congrArg Sigma.fst h'
      cases hcd
      have hik : i=k := eq_of_heq (Sigma.mk.inj_iff.mp h').2
      cases hik
      rfl

lemma point_lift (c : A) (k : Fin ((length Γ mark h2 paths j) c+1)) :
    vertexLift Γ mark h2 paths j
      (ChainSubdivision.point (length Γ mark h2 paths j)
        (ChainActiveStages.first Γ mark h2 paths j) (ChainActiveStages.last Γ mark h2 paths j) c k) =
      ChainSubdivision.point (repLength Γ mark h2) (ChainIsomorphism.first Γ mark h2)
        (ChainIsomorphism.last Γ mark h2) c.val k := by
  unfold ChainSubdivision.point
  split_ifs <;> rfl

def vertexMap : ChainSubdivision.Vertex (length Γ mark h2 paths j) (V := W) → V :=
  ChainIsomorphism.vertexMap Γ mark h2 ∘ vertexLift Γ mark h2 paths j

def dartMap : ChainSubdivision.Dart (length Γ mark h2 paths j) → D :=
  ChainIsomorphism.dartMap Γ mark h2 ∘ SubdivisionRestriction.dart (repLength Γ mark h2)
    (active Γ mark h2 paths j)

lemma vertexMap_injective : Injective (vertexMap Γ mark h2 paths j) :=
  (ChainIsomorphism.vertexMap_injective Γ mark h2).comp
    (vertexLift_injective Γ mark h2 paths j)

lemma dartMap_injective : Injective (dartMap Γ mark h2 paths j) :=
  (ChainIsomorphism.dartMap_injective Γ mark h2).comp
    (SubdivisionRestriction.dart_injective _ _)

lemma origin_map (d : ChainSubdivision.Dart (length Γ mark h2 paths j)) :
    vertexMap Γ mark h2 paths j ((Q).origin d)=Γ.origin (dartMap Γ mark h2 paths j d) := by
  unfold vertexMap dartMap
  dsimp only [Function.comp_apply]
  have h : vertexLift Γ mark h2 paths j ((Q).origin d) =
      (ChainSubdivision.graph (repLength Γ mark h2) (ChainIsomorphism.first Γ mark h2)
        (ChainIsomorphism.last Γ mark h2)).origin
        (SubdivisionRestriction.dart (repLength Γ mark h2) (active Γ mark h2 paths j) d) := by
    rcases d with ⟨⟨c,i⟩,r⟩
    cases r
    · simpa only [SubdivisionRestriction.dart,ChainSubdivision.origin_forward] using
        point_lift Γ mark h2 paths j c ⟨i.val,by have h:=i.isLt; omega⟩
    · simpa only [SubdivisionRestriction.dart,ChainSubdivision.origin_backward] using
        point_lift Γ mark h2 paths j c ⟨i.val+1,by have h:=i.isLt; omega⟩
  rw [h]
  exact ChainIsomorphism.origin_map Γ mark h2 _

lemma reverse_map (d : ChainSubdivision.Dart (length Γ mark h2 paths j)) :
    dartMap Γ mark h2 paths j ((Q).reverse d)=Γ.reverse (dartMap Γ mark h2 paths j d) := by
  unfold dartMap
  dsimp only [Function.comp_apply]
  rw [show SubdivisionRestriction.dart (repLength Γ mark h2) (active Γ mark h2 paths j) ((Q).reverse d)=
      (ChainSubdivision.graph (repLength Γ mark h2) (ChainIsomorphism.first Γ mark h2)
        (ChainIsomorphism.last Γ mark h2)).reverse
        (SubdivisionRestriction.dart (repLength Γ mark h2) (active Γ mark h2 paths j) d) from rfl]
  exact ChainIsomorphism.dartMap_reverse Γ mark h2 _

/-- Restricting an immersed realization keeps every active chain vertex and
port injective, without ever trying to embed inactive marked vertices. -/
theorem immersed {T : Type*} (label : D → T)
    (hlabel : Injective (fun d => (Γ.origin d,label d))) :
    Injective (fun d => ((Q).origin d,label (dartMap Γ mark h2 paths j d))) := by
  intro a b h
  apply dartMap_injective Γ mark h2 paths j
  apply hlabel
  apply Prod.ext
  · change Γ.origin (dartMap Γ mark h2 paths j a) = Γ.origin (dartMap Γ mark h2 paths j b)
    rw [←origin_map,←origin_map]
    exact congrArg (vertexMap Γ mark h2 paths j) (congrArg Prod.fst h)
  · change label (dartMap Γ mark h2 paths j a) = label (dartMap Γ mark h2 paths j b)
    exact congrArg Prod.snd h

end TorsionFreeZeroDivisors.ChainStageEmbedding

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical BigOperators
variable {V T : Type*} [Fintype V]

/-- At most one prescribed root. All other vertices remain unpinned. -/
def pin (root : Option V) (target : T) (v : V) : Option T :=
  if root=some v then some target else none

def free (root : Option V) (target : T) : ℕ :=
  (Finset.univ.filter fun v => pin root target v=none).card

lemma free_none (target : T) : free (V:=V) none target=Fintype.card V := by
  simp [free,pin]

lemma free_some (root : V) (target : T) : free (some root) target+1=Fintype.card V := by
  have h : (Finset.univ.filter fun v => pin (some root) target v=none) = Finset.univ.erase root := by
    ext v
    simp [pin,eq_comm]
  unfold free
  rw [h,Finset.card_erase_add_one (Finset.mem_univ root),Finset.card_univ]

lemma free_cast (root : Option V) (target : T) :
    (free root target : ℤ)=(Fintype.card V:ℤ)-(if root.isSome then 1 else 0) := by
  cases root with
  | none => simp only [free_none,Option.isSome_none,Bool.false_eq_true,ite_false,sub_zero]
  | some v =>
    have h := free_some v target
    simp only [Option.isSome_some,ite_true]
    omega

omit [Fintype V] in
lemma respects {root : Option V} {target : T} (f : V → T)
    (h : ∀ v,root=some v → f v=target) :
    ∀ v y,pin root target v=some y → f v=y := by
  intro v y hy
  unfold pin at hy
  split_ifs at hy with hv
  · cases Option.some.inj hy
    exact h v hv

end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.ActiveRoot
open scoped Classical
open PortSubdivision StageSubgraphs
variable {V D P : Type*} [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (paths : P → List D) (hp : ∀ p,paths p≠[])

omit [Fintype D] in
lemma occurrence_positive (p : P) (i : Fin (paths p).length) :
    0<ListStageExponents.mult Γ paths ((paths p).get i) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨p,i,false⟩,rfl⟩⟩

/-- The actual initial vertex belongs to the first active stage. -/
def vertex (p : P) : ActiveV Γ (ListStageExponents.mult Γ paths) 0 :=
  let i : Fin (paths p).length := ⟨0,List.length_pos_iff.mpr (hp p)⟩
  ⟨Γ.origin ((paths p).get i),(paths p).get i,rfl,occurrence_positive Γ paths p i⟩

omit [Fintype D] in
@[simp] lemma vertex_val (p : P) :
    (vertex Γ paths hp p).val=Γ.origin ((paths p).head (hp p)) := by
  simp [vertex,List.head_eq_getElem]

end TorsionFreeZeroDivisors.ActiveRoot

end

end OAI
