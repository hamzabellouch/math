import Mathlib
import OAI.Algebra.GroupRing.Iso

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ComparisonCoding
open scoped Classical
open PatternCoding

/-- Full integer affine comparison geometry. The offset uses [-2H,2H]. -/
structure Data (P E : Type*) (H : ℕ) where
  flip : E → E
  source : E → P
  lower : E → Fin (H+1)
  upper : E → Fin (H+1)
  reverse : E → Bool
  offset : E → Fin (4*H+1)

abbrev Code (K I H : ℕ) := (Fin I → Fin I) × (Fin I → Fin K) ×
  (Fin I → Fin (H+1)) × (Fin I → Fin (H+1)) ×
  (Fin I → Bool) × (Fin I → Fin (4*H+1))

def coefficient (K I : ℕ) := (8*I*K)^I

lemma card_code (K I H : ℕ) : Fintype.card (Code K I H) =
    I^I*K^I*(H+1)^(2*I)*2^I*(4*H+1)^I := by
  simp only [Code,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  rw [show 2*I=I+I by omega, pow_add]
  ring

lemma card_code_bound (K I H : ℕ) : Fintype.card (Code K I H) ≤
    coefficient K I*(H+1)^(3*I) := by
  rw [card_code]
  have h : (4*H+1)^I≤(4*(H+1))^I := Nat.pow_le_pow_left (by omega) I
  apply le_trans (Nat.mul_le_mul_left _ h)
  apply le_of_eq
  simp only [coefficient,mul_pow,show 2*I=I+I by omega,
    show 3*I=I+(I+I) by omega,pow_add]
  rw [show (8:ℕ)^I=2^I*4^I by rw [←mul_pow]; norm_num]
  ring

variable {P E P' E' : Type*} [Fintype P] [Fintype E] [Fintype P'] [Fintype E']
    (K I H : ℕ) (hK : 0<K) (hI : 0<I)
    (hP : Fintype.card P≤K) (hE : Fintype.card E≤I)

def encode (a : Data P E H) : Code K I H :=
  (pad I hE ⟨0,hI⟩ (fun e => names I hE (a.flip e)),
   pad I hE ⟨0,hK⟩ (fun e => names K hP (a.source e)),
   pad I hE 0 a.lower,pad I hE 0 a.upper,
   pad I hE false a.reverse,pad I hE 0 a.offset)

structure Isomorphism (a : Data P E H) (b : Data P' E' H) where
  path : P ≃ P'
  comparison : E ≃ E'
  flip_eq : ∀ e,comparison (a.flip e)=b.flip (comparison e)
  source_eq : ∀ e,path (a.source e)=b.source (comparison e)
  lower_eq : ∀ e,a.lower e=b.lower (comparison e)
  upper_eq : ∀ e,a.upper e=b.upper (comparison e)
  reverse_eq : ∀ e,a.reverse e=b.reverse (comparison e)
  offset_eq : ∀ e,a.offset e=b.offset (comparison e)

variable (hP' : Fintype.card P'≤K) (hE' : Fintype.card E'≤I)

theorem encode_complete (a : Data P E H) (b : Data P' E' H)
    (cP : Fintype.card P=Fintype.card P') (cE : Fintype.card E=Fintype.card E')
    (he : encode K I H hK hI hP hE a=encode K I H hK hI hP' hE' b) :
    ∃ f : Isomorphism H a b, f.path=rename cP ∧ f.comparison=rename cE := by
  simp only [encode,Prod.mk.injEq] at he
  obtain ⟨hf,hs,hl,hu,hr,ho⟩ := he
  have hflip (e : E) : rename cE (a.flip e)=b.flip (rename cE e) := by
    apply names_injective hE'
    rw [rename_names I hE hE']
    exact same_pad I hE hE' cE (⟨0,hI⟩ : Fin I) _ _ hf e
  have hsource (e : E) : rename cP (a.source e)=b.source (rename cE e) := by
    apply names_injective hP'
    rw [rename_names K hP hP']
    exact same_pad I hE hE' cE (⟨0,hK⟩ : Fin K) _ _ hs e
  exact ⟨⟨rename cP,rename cE,hflip,hsource,
    same_pad I hE hE' cE 0 _ _ hl,same_pad I hE hE' cE 0 _ _ hu,
    same_pad I hE hE' cE false _ _ hr,same_pad I hE hE' cE 0 _ _ ho⟩,rfl,rfl⟩

end TorsionFreeZeroDivisors.ComparisonCoding

namespace TorsionFreeZeroDivisors.SubdivisionIso
open scoped Classical
open ChainSubdivision PortSubdivision
variable {C V C' V' : Type*} (len : C → ℕ) (len' : C' → ℕ)
    (first last : C → V) (first' last' : C' → V')
    (eC : C ≃ C') (eV : V ≃ V') (hl : ∀ c,len c=len' (eC c))

def edge : Edge len ≃ Edge len' := Equiv.sigmaCongr eC (fun c => finCongr (hl c))
def interior : Interior len ≃ Interior len' := Equiv.sigmaCongr eC (fun c => finCongr (congrArg (fun n => n-1) (hl c)))
def vertex : Vertex len (V:=V) ≃ Vertex len' (V:=V') := Equiv.sumCongr eV (interior len len' eC hl)
def dart : Dart len ≃ Dart len' := Equiv.prodCongr (edge len len' eC hl) (Equiv.refl Bool)

variable (hf : ∀ c,eV (first c)=first' (eC c)) (ht : ∀ c,eV (last c)=last' (eC c))

include hf ht in
lemma point_eq (c : C) (k : Fin (len c+1)) :
    vertex len len' eC eV hl (point len first last c k)=
      point len' first' last' (eC c) ⟨k.val,by rw [←hl c]; exact k.isLt⟩ := by
  by_cases hz : k.val=0
  · simp [point,hz,vertex,hf]
  · by_cases ht' : k.val=len c
    · have hn : k.val=len' (eC c) := ht'.trans (hl c)
      simp only [point,dite_eq_right hz,dite_eq_left ht',dite_eq_left hn]
      exact congrArg Sum.inl (ht c)
    · have hn : k.val≠len' (eC c) := by rwa [←hl c]
      simp only [point,dite_eq_right hz,dite_eq_right ht',dite_eq_right hn]
      rfl

include hf ht in
lemma origin_eq (d : Dart len) :
    vertex len len' eC eV hl ((graph len first last).origin d)=
      (graph len' first' last').origin (dart len len' eC hl d) := by
  exact point_eq len len' first last first' last' eC eV hl hf ht d.1.1 _

omit eV in
lemma reverse_eq (d : Dart len) :
    dart len len' eC hl ((graph len first last).reverse d)=
      (graph len' first' last').reverse (dart len len' eC hl d) := rfl

end TorsionFreeZeroDivisors.SubdivisionIso

namespace TorsionFreeZeroDivisors.RankedSuppressionIso

section
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D V' D' : Type*} [Fintype D] [Fintype D']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
def skeleton : PortGraph (Mark mark) {d : D // turn Γ.origin mark h2 d=d} where
  origin d := ⟨Γ.origin d.val,(turn_fixed_iff Γ.origin mark h2 _).mp d.property⟩
  reverse := (suppressed Γ mark h2).reverse
  reverse_reverse := (suppressed Γ mark h2).reverse_reverse
  reverse_ne := (suppressed Γ mark h2).reverse_ne

local notation "S" => skeleton Γ mark h2
local notation "S'" => skeleton Γ' mark' h2'
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "B'" => {d : D' // turn Γ'.origin mark' h2' d=d}
local notation "R" => Rep Γ mark h2
local notation "R'" => Rep Γ' mark' h2'

lemma chosen_iff (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val) (d : B) : InvolutionOrientation.Chosen (S).reverse d ↔
    InvolutionOrientation.Chosen (S').reverse (f.dart d) := by
  unfold InvolutionOrientation.Chosen InvolutionOrientation.rank
  change (Fintype.equivFin B d).val < (Fintype.equivFin B ((S).reverse d)).val ↔
    (Fintype.equivFin B' (f.dart d)).val < (Fintype.equivFin B' ((S').reverse (f.dart d))).val
  rw [←f.reverse_eq,hrank,hrank]

def rep (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val) : R ≃ R' :=
  f.dart.subtypeEquiv (chosen_iff Γ mark h2 Γ' mark' h2' f hrank)

lemma rep_length (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,chainLength Γ mark h2 d=chainLength Γ' mark' h2' (f.dart d)) (c : R) : repLength Γ mark h2 c=
    repLength Γ' mark' h2' (rep Γ mark h2 Γ' mark' h2' f hrank c) := hlen c.val

lemma first_eq (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val) (c : R) : f.vertex (first Γ mark h2 c)=
    first Γ' mark' h2' (rep Γ mark h2 Γ' mark' h2' f hrank c) := f.origin_eq c.val

lemma last_eq (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val) (c : R) : f.vertex (last Γ mark h2 c)=
    last Γ' mark' h2' (rep Γ mark h2 Γ' mark' h2' f hrank c) := by
  change f.vertex ((S).origin ((S).reverse c.val))=(S').origin ((S').reverse (f.dart c.val))
  rw [f.origin_eq,f.reverse_eq]

/-- Exact canonical-rank suppression isomorphisms lift to actual subdivisions. -/
def subdivided (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,chainLength Γ mark h2 d=chainLength Γ' mark' h2' (f.dart d)) :
    Iso (ChainSubdivision.graph (repLength Γ mark h2) (first Γ mark h2) (last Γ mark h2))
      (ChainSubdivision.graph (repLength Γ' mark' h2') (first Γ' mark' h2') (last Γ' mark' h2')) where
  vertex := SubdivisionIso.vertex _ _ (rep Γ mark h2 Γ' mark' h2' f hrank) f.vertex
    (rep_length Γ mark h2 Γ' mark' h2' f hrank hlen)
  dart := SubdivisionIso.dart _ _ (rep Γ mark h2 Γ' mark' h2' f hrank)
    (rep_length Γ mark h2 Γ' mark' h2' f hrank hlen)
  origin_eq := SubdivisionIso.origin_eq _ _ _ _ _ _ _ _ _
    (first_eq Γ mark h2 Γ' mark' h2' f hrank) (last_eq Γ mark h2 Γ' mark' h2' f hrank)
  reverse_eq := SubdivisionIso.reverse_eq _ _ _ _ _ _ _ _

variable (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
    Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d)
  (hcovered' : ∀ d,ChainCoverage.Covered Γ'.reverse (turn Γ'.origin mark' h2')
    Γ'.reverse_reverse (turn_involutive Γ'.origin mark' h2') d)

def actual (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
    Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) :
    Iso (ChainSubdivision.graph (repLength Γ mark h2) (first Γ mark h2) (last Γ mark h2)) Γ where
  vertex := vertexEquiv Γ mark h2 hcovered
  dart := dartEquiv Γ mark h2 hcovered
  origin_eq := origin_map Γ mark h2
  reverse_eq := dartMap_reverse Γ mark h2

include hcovered hcovered' in
/-- No vertex or dart names survive, but all actual graph incidence does. -/
def full (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,chainLength Γ mark h2 d=chainLength Γ' mark' h2' (f.dart d)) : Iso Γ Γ' :=
  ((actual Γ mark h2 hcovered).symm.trans (subdivided Γ mark h2 Γ' mark' h2' f hrank hlen)).trans
    (actual Γ' mark' h2' hcovered')

end

section
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D V' D' : Type*} [Fintype D] [Fintype D']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
    (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
      Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d)
    (hcovered' : ∀ d,ChainCoverage.Covered Γ'.reverse (turn Γ'.origin mark' h2')
      Γ'.reverse_reverse (turn_involutive Γ'.origin mark' h2') d)
local notation "S" => skeleton Γ mark h2
local notation "S'" => skeleton Γ' mark' h2'
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "B'" => {d : D' // turn Γ'.origin mark' h2' d=d}
local notation "R" => Rep Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "F'" => next Γ'.reverse (turn Γ'.origin mark' h2')
local notation "len" => chainLength Γ mark h2
local notation "len'" => chainLength Γ' mark' h2'

lemma full_dartMap (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,len d=len' (f.dart d)) (d : ChainSubdivision.Dart (repLength Γ mark h2)) :
    (full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen).dart (dartMap Γ mark h2 d)=
      dartMap Γ' mark' h2' ((subdivided Γ mark h2 Γ' mark' h2' f hrank hlen).dart d) := by
  change (dartEquiv Γ' mark' h2' hcovered')
    ((subdivided Γ mark h2 Γ' mark' h2' f hrank hlen).dart
      ((dartEquiv Γ mark h2 hcovered).symm ((dartEquiv Γ mark h2 hcovered) d))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma full_forward (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,len d=len' (f.dart d)) (c : R) (i : Fin (len c.val)) :
    (full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen).dart (F^[i.val] c.val.val)=
      F'^[i.val] (f.dart c.val).val :=
  full_dartMap Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen (⟨c,i⟩,false)

lemma full_iter (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,len d=len' (f.dart d)) (d : B) (i : ℕ) (hi : i<len d) :
    (full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen).dart (F^[i] d.val)=
      F'^[i] (f.dart d).val := by
  rcases InvolutionOrientation.chosen_or_reverse (S).reverse (S).reverse_reverse (S).reverse_ne d with hd|hd
  · exact full_forward Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen ⟨d,hd⟩ ⟨i,hi⟩
  · have hj : len d-i-1<len ((S).reverse d) := by
      change len d-i-1<len ((suppressed Γ mark h2).reverse d)
      rw [chainLength_reverse]
      omega
    have hj' : i<len' (f.dart d) := by rwa [←hlen d]
    apply Γ'.reverse_reverse.injective
    rw [←(full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen).reverse_eq]
    rw [←ChainChunkTransport.reverse_iter Γ mark h2 d i hi,
      ←ChainChunkTransport.reverse_iter Γ' mark' h2' (f.dart d) i hj']
    have h := full_forward Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen
      ⟨(S).reverse d,hd⟩ ⟨len d-i-1,hj⟩
    have hrev : f.dart ((suppressed Γ mark h2).reverse d)=
        (suppressed Γ' mark' h2').reverse (f.dart d) := f.reverse_eq d
    simpa only [skeleton,hlen d,hrev] using h

lemma full_word (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,len d=len' (f.dart d)) (d : B) :
    (word Γ mark h2 d).map (full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen).dart =
      word Γ' mark' h2' (f.dart d) := by
  rw [word_eq_range,word_eq_range,List.map_map,←hlen d]
  apply List.map_congr_left
  intro i hi
  exact full_iter Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen d i (List.mem_range.mp hi)

end

open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D V' D' : Type} [Fintype D] [Fintype D']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
    (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
      Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d)
    (hcovered' : ∀ d,ChainCoverage.Covered Γ'.reverse (turn Γ'.origin mark' h2')
      Γ'.reverse_reverse (turn_involutive Γ'.origin mark' h2') d)
local notation "S" => skeleton Γ mark h2
local notation "S'" => skeleton Γ' mark' h2'
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "B'" => {d : D' // turn Γ'.origin mark' h2' d=d}
local notation "len" => chainLength Γ mark h2
local notation "len'" => chainLength Γ' mark' h2'
variable (f : Iso (skeleton Γ mark h2) (skeleton Γ' mark' h2'))
    (hrank : ∀ d,(Fintype.equivFin {d : D' // turn Γ'.origin mark' h2' d=d} (f.dart d)).val=
      (Fintype.equivFin {d : D // turn Γ.origin mark h2 d=d} d).val)
    (hlen : ∀ d,chainLength Γ mark h2 d=chainLength Γ' mark' h2' (f.dart d))
local notation "F" => full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen

lemma full_seed (d : B) : (F).dart d.val=(f.dart d).val :=
  full_iter Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen d 0
    (chainLength_pos Γ mark h2 d)

lemma full_vertexMap (v : ChainSubdivision.Vertex (repLength Γ mark h2) (V:=Mark mark)) :
    (F).vertex (vertexMap Γ mark h2 v)=vertexMap Γ' mark' h2'
      ((subdivided Γ mark h2 Γ' mark' h2' f hrank hlen).vertex v) := by
  change (vertexEquiv Γ' mark' h2' hcovered')
    ((subdivided Γ mark h2 Γ' mark' h2' f hrank hlen).vertex
      ((vertexEquiv Γ mark h2 hcovered).symm ((vertexEquiv Γ mark h2 hcovered) v)))=_
  rw [Equiv.symm_apply_apply]
  rfl

variable (side : V → Bool) (side' : V' → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (hs' : ∀ d,side' (Γ'.origin (Γ'.reverse d))=side' (Γ'.origin d))
    (hside : ∀ v : Mark mark,side v.val=side' (f.vertex v).val)

include hside hs hs' in
lemma full_side (v : V) : side v=side' ((F).vertex v) := by
  obtain ⟨v,rfl⟩ := (vertexEquiv Γ mark h2 hcovered).surjective v
  change side (vertexMap Γ mark h2 v)=side' ((F).vertex (vertexMap Γ mark h2 v))
  rw [full_vertexMap]
  cases v with
  | inl v => exact hside v
  | inr v =>
    rcases v with ⟨c,i⟩
    change side (Γ.origin ((next Γ.reverse (turn Γ.origin mark h2))^[i.val+1] c.val.val))=
      side' (Γ'.origin ((next Γ'.reverse (turn Γ'.origin mark' h2'))^[i.val+1] (f.dart c.val).val))
    rw [ChainSide.iterate_side Γ mark h2 side hs,ChainSide.iterate_side Γ' mark' h2' side' hs']
    have he := congrArg (fun x : Mark mark' => side' x.val) (f.origin_eq c.val)
    exact (hside ((S).origin c.val)).trans he

variable {P P' : Type} (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
    (paths' : P' → List {d : D' // turn Γ'.origin mark' h2' d=d})
    (eP : P ≃ P') (hp : ∀ p,(paths p).map f.dart=paths' (eP p))

include hp in
lemma full_words (p : P) : ((paths p).flatMap (word Γ mark h2)).map (F).dart =
    (paths' (eP p)).flatMap (word Γ' mark' h2') := by
  rw [List.map_flatMap,←hp,List.flatMap_map]
  apply List.flatMap_congr
  intro d _
  exact full_word Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen d

variable (hne : ∀ p,paths p≠[]) (hne' : ∀ p,paths' p≠[])
    (root : Option P) (root' : Option P') (hroot : root.map eP=root')

include hp hroot in
lemma full_source : (StageRoot.source Γ mark h2 paths hne root).map (F).vertex=
    StageRoot.source Γ' mark' h2' paths' hne' root' := by
  rw [←hroot]
  cases root with
  | none => rfl
  | some p =>
    simp only [StageRoot.source,Option.map_some]
    apply congrArg some
    change (F).vertex (Γ.origin ((paths p).head (hne p)).val)=
      Γ'.origin ((paths' (eP p)).head (hne' _)).val
    rw [(F).origin_eq,full_seed]
    have hh := congrArg List.head? (hp p)
    rw [List.head?_map,List.head?_eq_some_head (hne p),
      List.head?_eq_some_head (hne' (eP p))] at hh
    exact congrArg (fun d => Γ'.origin d.val) (Option.some.inj hh)

end TorsionFreeZeroDivisors.RankedSuppressionIso

end

end OAI
