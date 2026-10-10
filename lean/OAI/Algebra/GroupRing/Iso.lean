import Mathlib
import OAI.Algebra.GroupRing.PatternUniform

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PortSubdivision.Iso
open scoped Classical
variable {V D V' D' T TV : Type*} [Fintype V] [Fintype D] [Fintype V'] [Fintype D']
    [Fintype T] [Fintype TV] {Γ : PortGraph V D} {Γ' : PortGraph V' D'}
    (f : Iso Γ Γ') (side : V → Bool) (side' : V' → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (hs' : ∀ d,side' (Γ'.origin (Γ'.reverse d))=side' (Γ'.origin d))
    (hside : ∀ v,side v=side' (f.vertex v)) (b : Bool)
    (root : Option V) (root' : Option V') (hroot : root.map f.vertex=root')
    (label : D' → T) (outgoing : TV → Finset T) (target : TV) (bar : T → T)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar)

/-- A side-preserving graph isomorphism transports the actual rooted embedding,
not just its edge or vertex counts. -/
def sideEmbedding (e : RealizationTransport.Embedding (SideRestriction.graph Γ' side' hs' b)
    (fun d => label d.val) outgoing (RootPins.pin (SidePins.root side' root' b) target) bar r) :
    RealizationTransport.Embedding (SideRestriction.graph Γ side hs b)
      (fun d => label (f.dart d.val)) outgoing (RootPins.pin (SidePins.root side root b) target) bar r := by
  let fv : SideRestriction.Vertex side b ↪ SideRestriction.Vertex side' b :=
    ⟨fun v => ⟨f.vertex v.val,(hside v.val).symm.trans v.property⟩,
      fun _ _ h => Subtype.ext (f.vertex.injective (congrArg Subtype.val h))⟩
  let fd : SideRestriction.Dart Γ side b ↪ SideRestriction.Dart Γ' side' b :=
    ⟨fun d => ⟨f.dart d.val,by rw [←f.origin_eq,←hside]; exact d.property⟩,
      fun _ _ h => Subtype.ext (f.dart.injective (congrArg Subtype.val h))⟩
  have ho d : fv ((SideRestriction.graph Γ side hs b).origin d)=
      (SideRestriction.graph Γ' side' hs' b).origin (fd d) := Subtype.ext (f.origin_eq d.val)
  have hr d : fd ((SideRestriction.graph Γ side hs b).reverse d)=
      (SideRestriction.graph Γ' side' hs' b).reverse (fd d) := Subtype.ext (f.reverse_eq d.val)
  have hp v y : RootPins.pin (SidePins.root side root b) target v=some y →
      RootPins.pin (SidePins.root side' root' b) target (fv v)=some y := by
    simp only [RootPins.pin_some_iff,SidePins.root_eq_some]
    rintro ⟨hv,hy⟩
    refine ⟨?_,hy⟩
    rw [←hroot,hv]
    rfl
  exact RealizationTransport.restrict e _ fv fd ho hr _ hp

end TorsionFreeZeroDivisors.PortSubdivision.Iso

namespace TorsionFreeZeroDivisors.OriginalPatternIso
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks ActualPatternEvent
variable {V D P E V' D' P' E' : Type} [Fintype V] [Fintype D] [Fintype P]
    [Fintype V'] [Fintype D'] [Fintype P']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (paths' : P' → List {x : D' // turn Γ'.origin mark' h2' x=x}) (hp' : ∀ p,paths' p≠[])
local notation "pl" => pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)
local notation "pl'" => pathLength (chunks Γ' mark' h2' paths') (chunkLength Γ' mark' h2' paths')
variable (f : Iso Γ Γ') (eP : P ≃ P')
    (hwords : ∀ p,((paths p).flatMap (word Γ mark h2)).map f.dart =
      (paths' (eP p)).flatMap (word Γ' mark' h2'))

include hwords in
omit [Fintype V] [Fintype V'] [Fintype P] [Fintype P'] in
lemma length_eq (p : P) : pl p=pl' (eP p) := by
  rw [pathLength_eq,pathLength_eq,←hwords,List.length_map]

include hwords in
omit [Fintype V] [Fintype V'] [Fintype P] [Fintype P'] in
lemma dart_eq (x : Position pl) (hlen : ∀ p,pl p=pl' (eP p)) :
    f.dart (originalDart Γ mark h2 paths x)=
      originalDart Γ' mark' h2' paths' (ComparisonGeometry.position eP hlen x) := by
  apply Option.some.inj
  have h := congrArg (fun l : List D' => l[x.2.val.toNat]?) (hwords x.1)
  rw [List.getElem?_map,originalDart_get] at h
  change some (f.dart (originalDart Γ mark h2 paths x))=_ at h
  rw [←originalDart_get]
  exact h

variable (side : V → Bool) (side' : V' → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (hs' : ∀ d,side' (Γ'.origin (Γ'.reverse d))=side' (Γ'.origin d))
    (hside : ∀ v,side v=side' (f.vertex v))
    (root : Option P) (root' : Option P')
    (hroot : (StageRoot.source Γ mark h2 paths hp root).map f.vertex=
      StageRoot.source Γ' mark' h2' paths' hp' root')
    (C : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (C' : Comparisons (E:=E') (pathLength (chunks Γ' mark' h2' paths') (chunkLength Γ' mark' h2' paths')))
    (g : ComparisonGeometry.Iso C C') (hg : g.path=eP)
    (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)

include hwords hside hroot hg in
omit [Fintype V] [Fintype V'] [Fintype P] [Fintype P'] in
/-- An unlabeled pattern isomorphism preserves the actual event in each fixed
sample. No independence or expected-count assumption is used in this bridge. -/
lemma realized (r : Match rep)
    (he : OriginalPattern.Realized Γ' mark' h2' side' hs' paths' hp' root' rep a b C' r) :
    OriginalPattern.Realized Γ mark h2 side hs paths hp root rep a b C r := by
  subst eP
  rcases he with ⟨label,hl,hi,hc,⟨ea⟩,⟨eb⟩⟩
  refine ⟨label ∘ f.dart,?_,?_,?_,?_,?_⟩
  · intro d
    dsimp only [Function.comp_apply]
    rw [f.reverse_eq,hl]
  · intro d e ho he
    apply f.dart.injective
    apply hi _ _ _ he
    rw [←f.origin_eq,←f.origin_eq,ho]
  · intro x j hj
    have hh := hc (ComparisonGeometry.position g.path g.length_eq x) (g.comparison j)
      ((g.side_some x j).mpr hj)
    dsimp only [Function.comp_apply]
    rw [dart_eq Γ mark h2 Γ' mark' h2' paths paths' f g.path hwords x g.length_eq,
      dart_eq Γ mark h2 Γ' mark' h2' paths paths' f g.path hwords (C.pairing.partner x) g.length_eq,
      g.partner_eq,g.reverse_eq]
    exact hh
  · exact ⟨f.sideEmbedding side side' hs hs' hside true _ _ hroot label _ a Types.inverse r.1 ea⟩
  · exact ⟨f.sideEmbedding side side' hs hs' hside false _ _ hroot label _ b Types.inverse r.2 eb⟩

end TorsionFreeZeroDivisors.OriginalPatternIso

/-!
Finite names for the actual-image patterns in entropy.tex 126–138.  The bounds
R,K,T,I are fixed before H grows.  No vertex names or letters are stored.  Raw
codes include invalid multigraphs as an overcount; all validity conditions must
still be checked when a code is used in a realization event.
-/
namespace TorsionFreeZeroDivisors.PatternCoding

section
open scoped BigOperators Classical

/-- A list of at most T chain darts can be stored in T option-valued slots. -/
def packList {A : Type*} (T : ℕ) (p : List A) : Fin T → Option A :=
  fun i => p[i.val]?

lemma packList_injective {A : Type*} (T : ℕ) :
    Function.Injective (fun p : {p : List A // p.length ≤ T} => packList T p.val) := by
  intro p q h
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i < T
  · exact congrFun h ⟨i,hi⟩
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- One interval uses one path index and two integer endpoints. -/
abbrev Interval (K H : ℕ) := Fin K × Fin (H+1) × Fin (H+1)

/-- Two intervals and their comparison sign. Inactive comparison slots are absent. -/
abbrev Comparison (K H : ℕ) := Option (Interval K H × Interval K H × Bool)

/-- Bounded path sequences, marked graph incidence/reversal, lengths, sides,
root designation and interval data. Unused graph indices may be padded.
The use of oriented darts avoids choosing orientations of loop chains. -/
abbrev Code (R K T I H : ℕ) :=
  (Fin R → Fin R) × (Fin R → Fin R) × (Fin R → Bool) ×
  (Fin R → Fin (H+1)) × (Fin K → Fin T → Option (Fin R)) ×
  Option (Fin K × Bool) × (Fin I → Comparison K H)

lemma card_comparison (K H : ℕ) :
    Fintype.card (Comparison K H) = 1 + 2*K^2*(H+1)^4 := by
  simp only [Comparison,Interval,Fintype.card_option,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_bool]
  ring

lemma card_code (R K T I H : ℕ) :
    Fintype.card (Code R K T I H) =
      R^(2*R) * 2^R * (H+1)^R * (R+1)^(T*K) * (1+2*K) *
      (1+2*K^2*(H+1)^4)^I := by
  simp only [Code,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_bool,Fintype.card_option]
  simp only [pow_mul]
  ring

/-- The constant in the polynomial pattern bound depends only on fixed bounds. -/
def coefficient (R K T I : ℕ) : ℕ :=
  R^(2*R) * 2^R * (R+1)^(T*K) * (1+2*K) * (1+2*K^2)^I

lemma card_code_polynomial (R K T I H : ℕ) :
    Fintype.card (Code R K T I H) ≤ coefficient R K T I * (H+1)^(R+4*I) := by
  rw [card_code]
  have hp : 1 ≤ (H+1)^4 := Nat.one_le_pow _ _ (by omega)
  have hh : 1+2*K^2*(H+1)^4 ≤ (1+2*K^2)*(H+1)^4 := by nlinarith
  have he := Nat.pow_le_pow_left hh I
  calc
    _ ≤ R^(2*R)*2^R*(H+1)^R*(R+1)^(T*K)*(1+2*K)*
        ((1+2*K^2)*(H+1)^4)^I := Nat.mul_le_mul_left _ he
    _ = coefficient R K T I*(H+1)^(R+4*I) := by
      simp only [coefficient,mul_pow,pow_add,pow_mul]
      ring

/-- The canonical renaming is independent of every target vertex name. -/
def names {A : Type*} [Fintype A] (R : ℕ) (h : Fintype.card A ≤ R) : A ↪ Fin R :=
  (Fintype.equivFin A).toEmbedding.trans (Fin.castLEEmb h)

lemma names_injective {A : Type*} [Fintype A] {R : ℕ} (h : Fintype.card A ≤ R) :
    Function.Injective (names R h) := (names R h).injective

/-- Padding a finite table loses none of its entries. -/
def pad {A B : Type*} [Fintype A] (R : ℕ) (_h : Fintype.card A ≤ R)
    (default : B) (f : A → B) (i : Fin R) : B :=
  if hi : i.val < Fintype.card A then f ((Fintype.equivFin A).symm ⟨i.val,hi⟩)
  else default

lemma pad_names {A B : Type*} [Fintype A] (R : ℕ) (h : Fintype.card A ≤ R)
    (default : B) (f : A → B) (a : A) :
    pad R h default f (names R h a) = f a := by
  simp only [pad,names,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
    Fin.castLEEmb_apply]
  simp

/-- Thus all the actual comparison endpoints with a ≤H bound fit literally. -/
def endName (H : ℕ) (i : ℕ) (hi : i ≤ H) : Fin (H+1) := ⟨i,by omega⟩

@[simp] lemma endName_val (H i : ℕ) (hi : i ≤ H) : (endName H i hi).val = i := rfl

/-- An actual comparison endpoint. Its path and integer position are retained. -/
structure ActualInterval (P : Type*) (H : ℕ) where
  path : P
  start : Fin (H+1)
  stop : Fin (H+1)

/-- The sign records translation versus reflection, not a chosen graph label. -/
structure ActualComparison (P : Type*) (H : ℕ) where
  left : ActualInterval P H
  right : ActualInterval P H
  sign : Bool

def intervalName {P : Type*} [Fintype P] (K H : ℕ) (hP : Fintype.card P ≤ K)
    (a : ActualInterval P H) : Interval K H :=
  (names K hP a.path,a.start,a.stop)

def comparisonName {P : Type*} [Fintype P] (K H : ℕ) (hP : Fintype.card P ≤ K)
    (a : ActualComparison P H) : Comparison K H :=
  some (intervalName K H hP a.left,intervalName K H hP a.right,a.sign)

lemma intervalName_injective {P : Type*} [Fintype P] (K H : ℕ)
    (hP : Fintype.card P ≤ K) : Function.Injective (intervalName K H hP) := by
  intro a b h
  cases a with | mk ap ast asp =>
    cases b with | mk bp bst bsp =>
      simp only [intervalName,Prod.mk.injEq] at h
      obtain ⟨h1,h2,h3⟩ := h
      have h1' := names_injective hP h1
      cases h1'; cases h2; cases h3; rfl

lemma comparisonName_injective {P : Type*} [Fintype P] (K H : ℕ)
    (hP : Fintype.card P ≤ K) : Function.Injective (comparisonName K H hP) := by
  intro a b h
  cases a with | mk al ar asn =>
    cases b with | mk bl br bsn =>
      simp only [comparisonName,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨h1,h2,h3⟩ := h
      have h1' := intervalName_injective K H hP h1
      have h2' := intervalName_injective K H hP h2
      cases h1'; cases h2'; cases h3; rfl

/-- Explicit encoding of all source pattern data after suppression. The graph
and path carriers can be arbitrary finite types: their old vertex names do
not survive. Empty padding is not counted as an actual chain or path. -/
def encode {D V P J : Type*} [Fintype D] [Fintype V] [Fintype P] [Fintype J]
    (R K T I H : ℕ) (hR : 0<R)
    (hD : Fintype.card D ≤ R) (hV : Fintype.card V ≤ R)
    (hP : Fintype.card P ≤ K) (hJ : Fintype.card J ≤ I)
    (rev : D → D) (origin : D → V) (side : D → Bool)
    (length : D → Fin (H+1)) (paths : P → List D)
    (root : Option (P × Bool)) (comparisons : J → ActualComparison P H) : Code R K T I H :=
  (pad R hD ⟨0,hR⟩ (fun d => names R hD (rev d)),
   pad R hD ⟨0,hR⟩ (fun d => names R hV (origin d)),
   pad R hD false side,
   pad R hD 0 length,
   pad K hP (fun _ => none) (fun p => packList T ((paths p).map (names R hD))),
   root.map (fun a => (names K hP a.1,a.2)),
   pad I hJ none (fun j => comparisonName K H hP (comparisons j)))

/-- Every finite marked multigraph, bounded list of chain traversals, rooted
path designation and bounded set of signed comparisons is literally retained
in one member of the polynomially counted family. -/
theorem encode_preserves {D V P J : Type*} [Fintype D] [Fintype V] [Fintype P] [Fintype J]
    (R K T I H : ℕ) (hR : 0<R)
    (hD : Fintype.card D ≤ R) (hV : Fintype.card V ≤ R)
    (hP : Fintype.card P ≤ K) (hJ : Fintype.card J ≤ I)
    (rev : D → D) (origin : D → V) (side : D → Bool)
    (length : D → Fin (H+1)) (paths : P → List D)
    (root : Option (P × Bool)) (comparisons : J → ActualComparison P H) :
    let c := encode R K T I H hR hD hV hP hJ rev origin side length paths root comparisons
    (∀ d, c.1 (names R hD d) = names R hD (rev d)) ∧
    (∀ d, c.2.1 (names R hD d) = names R hV (origin d)) ∧
    (∀ d, c.2.2.1 (names R hD d) = side d) ∧
    (∀ d, c.2.2.2.1 (names R hD d) = length d) ∧
    (∀ p, c.2.2.2.2.1 (names K hP p) = packList T ((paths p).map (names R hD))) ∧
    c.2.2.2.2.2.1 = root.map (fun a => (names K hP a.1,a.2)) ∧
    (∀ j, c.2.2.2.2.2.2 (names I hJ j) = comparisonName K H hP (comparisons j)) := by
  simp only [encode,pad_names]
  simp

/-- The bounded-list slots lose no traversal, even if darts are repeated. -/
lemma encoded_paths_injective {D : Type*} [Fintype D] (R T : ℕ)
    (hD : Fintype.card D ≤ R) :
    Function.Injective (fun p : {p : List D // p.length ≤ T} =>
      packList T (p.val.map (names R hD))) := by
  intro p q h
  have hm : p.val.map (names R hD) = q.val.map (names R hD) := by
    exact congrArg Subtype.val (packList_injective T
      (a₁ := ⟨p.val.map (names R hD),by simpa using p.property⟩)
      (a₂ := ⟨q.val.map (names R hD),by simpa using q.property⟩) h)
  apply Subtype.ext
  exact (names_injective hD).list_map hm

end

open scoped Classical

/-- Carrier counts distinguish inactive padding from actual graph indices.
The four extra counts are uniformly bounded, independent of H and n. -/
abbrev SizedCode (R K T I H : ℕ) :=
  Fin (R+1) × Fin (R+1) × Fin (K+1) × Fin (I+1) × Code R K T I H

theorem card_sizedCode (R K T I H : ℕ) :
    Fintype.card (SizedCode R K T I H) ≤
      (R+1)^2*(K+1)*(I+1)*coefficient R K T I*(H+1)^(R+4*I) := by
  have hcard : Fintype.card (SizedCode R K T I H) =
      (R+1)*(R+1)*(K+1)*(I+1)*Fintype.card (Code R K T I H) := by
    simp only [SizedCode,Fintype.card_prod,Fintype.card_fin]
    ring
  rw [hcard]
  have h := Nat.mul_le_mul_left ((R+1)*(R+1)*(K+1)*(I+1))
    (card_code_polynomial R K T I H)
  convert h using 1; ring

variable {A B : Type*} [Fintype A] [Fintype B]

def rename (h : Fintype.card A=Fintype.card B) : A ≃ B :=
  (Fintype.equivFin A).trans ((finCongr h).trans (Fintype.equivFin B).symm)

theorem rename_rank (h : Fintype.card A=Fintype.card B) (a : A) :
    (Fintype.equivFin B (rename h a)).val = (Fintype.equivFin A a).val := by
  simp [rename]

theorem rename_names (R : ℕ) (hA : Fintype.card A ≤ R) (hB : Fintype.card B ≤ R)
    (h : Fintype.card A=Fintype.card B) (a : A) : names R hB (rename h a)=names R hA a := by
  apply Fin.ext
  exact rename_rank h a

theorem same_pad {X : Type*} (R : ℕ) (hA : Fintype.card A ≤ R) (hB : Fintype.card B ≤ R)
    (h : Fintype.card A=Fintype.card B) (x : X) (f : A → X) (g : B → X)
    (he : pad R hA x f=pad R hB x g) (a : A) : f a=g (rename h a) := by
  have hh := congrFun he (names R hA a)
  rw [pad_names,←rename_names R hA hB h,pad_names] at hh
  exact hh

/-- All non-label data of a bounded actual pattern. Proof fields are not
encoded, while all data fields are. -/
structure Data (D V P J : Type*) (T H : ℕ) where
  reverse : D → D
  origin : D → V
  side : D → Bool
  length : D → Fin (H+1)
  paths : P → List D
  path_bound : ∀ p,(paths p).length ≤ T
  root : Option (P × Bool)
  comparisons : J → ActualComparison P H

variable {D V P J D' V' P' J' : Type*}
  [Fintype D] [Fintype V] [Fintype P] [Fintype J]
  [Fintype D'] [Fintype V'] [Fintype P'] [Fintype J']

/-- Exact simultaneous equivalence of graph incidence, orientation, side,
length, every path traversal, root path, and comparison intervals. -/
structure Isomorphism {T H : ℕ} (a : Data D V P J T H) (b : Data D' V' P' J' T H) where
  dart : D ≃ D'
  vertex : V ≃ V'
  path : P ≃ P'
  comparison : J ≃ J'
  reverse_eq : ∀ d,dart (a.reverse d)=b.reverse (dart d)
  origin_eq : ∀ d,vertex (a.origin d)=b.origin (dart d)
  side_eq : ∀ d,a.side d=b.side (dart d)
  length_eq : ∀ d,a.length d=b.length (dart d)
  paths_eq : ∀ p,(a.paths p).map dart=b.paths (path p)
  root_eq : a.root.map (fun x => (path x.1,x.2))=b.root
  comparison_left_path : ∀ j,path (a.comparisons j).left.path=(b.comparisons (comparison j)).left.path
  comparison_left_start : ∀ j,(a.comparisons j).left.start=(b.comparisons (comparison j)).left.start
  comparison_left_stop : ∀ j,(a.comparisons j).left.stop=(b.comparisons (comparison j)).left.stop
  comparison_right_path : ∀ j,path (a.comparisons j).right.path=(b.comparisons (comparison j)).right.path
  comparison_right_start : ∀ j,(a.comparisons j).right.start=(b.comparisons (comparison j)).right.start
  comparison_right_stop : ∀ j,(a.comparisons j).right.stop=(b.comparisons (comparison j)).right.stop
  comparison_sign : ∀ j,(a.comparisons j).sign=(b.comparisons (comparison j)).sign

variable (R K T I H : ℕ) (hR : 0<R)
  (hD : Fintype.card D ≤ R) (hV : Fintype.card V ≤ R)
  (hP : Fintype.card P ≤ K) (hJ : Fintype.card J ≤ I)

def encodeData (a : Data D V P J T H) : SizedCode R K T I H :=
  (⟨Fintype.card D,by omega⟩,⟨Fintype.card V,by omega⟩,
   ⟨Fintype.card P,by omega⟩,⟨Fintype.card J,by omega⟩,
   encode R K T I H hR hD hV hP hJ a.reverse a.origin a.side a.length a.paths a.root a.comparisons)

variable (hD' : Fintype.card D' ≤ R) (hV' : Fintype.card V' ≤ R)
  (hP' : Fintype.card P' ≤ K) (hJ' : Fintype.card J' ≤ I)

/-- Equality of the finite code loses no pattern information: the resulting
isomorphism is valid for loops, repeated paths, and repeated comparisons. -/
theorem same_code_canonical_isomorphism (a : Data D V P J T H) (b : Data D' V' P' J' T H)
    (cD : Fintype.card D=Fintype.card D') (cV : Fintype.card V=Fintype.card V')
    (cP : Fintype.card P=Fintype.card P') (cJ : Fintype.card J=Fintype.card J')
    (he : encode R K T I H hR hD hV hP hJ a.reverse a.origin a.side a.length a.paths a.root a.comparisons =
      encode R K T I H hR hD' hV' hP' hJ' b.reverse b.origin b.side b.length b.paths b.root b.comparisons) :
    ∃ f : Isomorphism a b, f.dart=rename cD ∧ f.path=rename cP ∧ f.vertex=rename cV := by
  simp only [encode,Prod.mk.injEq] at he
  obtain ⟨hr,ho,hs,hl,hp,hroot,hcomp⟩ := he
  have hrev (d : D) : rename cD (a.reverse d)=b.reverse (rename cD d) := by
    apply names_injective hD'
    rw [rename_names R hD hD']
    exact same_pad R hD hD' cD (⟨0,hR⟩ : Fin R) _ _ hr d
  have horig (d : D) : rename cV (a.origin d)=b.origin (rename cD d) := by
    apply names_injective hV'
    rw [rename_names R hV hV']
    exact same_pad R hD hD' cD (⟨0,hR⟩ : Fin R) _ _ ho d
  have hpath (p : P) : (a.paths p).map (rename cD)=b.paths (rename cP p) := by
    have hh := same_pad K hP hP' cP (fun _ => none) _ _ hp p
    have hn : (a.paths p).map (names R hD)=(b.paths (rename cP p)).map (names R hD') := by
      exact congrArg Subtype.val (packList_injective T
        (a₁ := ⟨_,by simpa using a.path_bound p⟩)
        (a₂ := ⟨_,by simpa using b.path_bound (rename cP p)⟩) hh)
    apply (names_injective hD').list_map
    rw [List.map_map]
    have hrn : (names R hD') ∘ (rename cD)=names R hD := by
      funext d
      exact rename_names R hD hD' cD d
    rw [hrn]
    exact hn
  have hroot' : a.root.map (fun x => (rename cP x.1,x.2))=b.root := by
    cases ha : a.root with
    | none =>
      cases hb : b.root with
      | none => rfl
      | some y => simp [ha,hb] at hroot
    | some x =>
      cases hb : b.root with
      | none => simp [ha,hb] at hroot
      | some y =>
        have hh : names K hP x.1=names K hP' y.1 ∧ x.2=y.2 := by
          simpa only [ha,hb,Option.map_some,Option.some.injEq,Prod.mk.injEq] using hroot
        simp only [Option.map_some,Option.some.injEq]
        apply Prod.ext
        · apply names_injective hP'
          rw [rename_names K hP hP']
          exact hh.1
        · exact hh.2
  have hc (j : J) :
      (rename cP (a.comparisons j).left.path=(b.comparisons (rename cJ j)).left.path) ∧
      (a.comparisons j).left.start=(b.comparisons (rename cJ j)).left.start ∧
      (a.comparisons j).left.stop=(b.comparisons (rename cJ j)).left.stop ∧
      (rename cP (a.comparisons j).right.path=(b.comparisons (rename cJ j)).right.path) ∧
      (a.comparisons j).right.start=(b.comparisons (rename cJ j)).right.start ∧
      (a.comparisons j).right.stop=(b.comparisons (rename cJ j)).right.stop ∧
      (a.comparisons j).sign=(b.comparisons (rename cJ j)).sign := by
    have hh := same_pad I hJ hJ' cJ none _ _ hcomp j
    simp only [comparisonName,intervalName,Option.some.injEq,Prod.mk.injEq] at hh
    obtain ⟨⟨h1,h2,h3⟩,⟨h4,h5,h6⟩,h7⟩ := hh
    refine ⟨?_,h2,h3,?_,h5,h6,h7⟩
    · apply names_injective hP'
      rw [rename_names K hP hP']
      exact h1
    · apply names_injective hP'
      rw [rename_names K hP hP']
      exact h4
  exact ⟨⟨rename cD,rename cV,rename cP,rename cJ,hrev,horig,
    same_pad R hD hD' cD false a.side b.side hs,
    same_pad R hD hD' cD 0 a.length b.length hl,hpath,hroot',
    (fun j => (hc j).1),(fun j => (hc j).2.1),(fun j => (hc j).2.2.1),
    (fun j => (hc j).2.2.2.1),(fun j => (hc j).2.2.2.2.1),
    (fun j => (hc j).2.2.2.2.2.1),(fun j => (hc j).2.2.2.2.2.2)⟩, rfl, rfl, rfl⟩

theorem same_code_ranked_isomorphism (a : Data D V P J T H) (b : Data D' V' P' J' T H)
    (cD : Fintype.card D=Fintype.card D') (cV : Fintype.card V=Fintype.card V')
    (cP : Fintype.card P=Fintype.card P') (cJ : Fintype.card J=Fintype.card J')
    (he : encode R K T I H hR hD hV hP hJ a.reverse a.origin a.side a.length a.paths a.root a.comparisons =
      encode R K T I H hR hD' hV' hP' hJ' b.reverse b.origin b.side b.length b.paths b.root b.comparisons) :
    ∃ f : Isomorphism a b, ∀ d,
      (Fintype.equivFin D' (f.dart d)).val = (Fintype.equivFin D d).val := by
  obtain ⟨f,hD,hP⟩ := same_code_canonical_isomorphism R K T I H hR hD hV hP hJ hD' hV' hP' hJ' a b cD cV cP cJ he
  refine ⟨f,fun d => ?_⟩
  rw [hD]
  exact rename_rank cD d

theorem same_code_isomorphism (a : Data D V P J T H) (b : Data D' V' P' J' T H)
    (cD : Fintype.card D=Fintype.card D') (cV : Fintype.card V=Fintype.card V')
    (cP : Fintype.card P=Fintype.card P') (cJ : Fintype.card J=Fintype.card J')
    (he : encode R K T I H hR hD hV hP hJ a.reverse a.origin a.side a.length a.paths a.root a.comparisons =
      encode R K T I H hR hD' hV' hP' hJ' b.reverse b.origin b.side b.length b.paths b.root b.comparisons) :
    Nonempty (Isomorphism a b) := by
  obtain ⟨f,_⟩ := same_code_ranked_isomorphism R K T I H hR hD hV hP hJ hD' hV' hP' hJ' a b cD cV cP cJ he
  exact ⟨f⟩

/-- Equal padded SIZED codes imply actual pattern equivalence, not merely
similar numerical bounds or matching cardinalities. -/
theorem encodeData_complete (a : Data D V P J T H) (b : Data D' V' P' J' T H)
    (he : encodeData R K T I H hR hD hV hP hJ a =
      encodeData R K T I H hR hD' hV' hP' hJ' b) : Nonempty (Isomorphism a b) := by
  simp only [encodeData,Prod.mk.injEq] at he
  obtain ⟨h1,h2,h3,h4,he⟩ := he
  exact same_code_isomorphism R K T I H hR hD hV hP hJ hD' hV' hP' hJ' a b
    (congrArg Fin.val h1) (congrArg Fin.val h2) (congrArg Fin.val h3) (congrArg Fin.val h4) he

/-- Equal codes additionally preserve the literal rank orientation used in the
subdivision realization. This is an output of encoding, not an extra assumption. -/
theorem encodeData_ranked_complete (a : Data D V P J T H) (b : Data D' V' P' J' T H)
    (he : encodeData R K T I H hR hD hV hP hJ a =
      encodeData R K T I H hR hD' hV' hP' hJ' b) :
    ∃ f : Isomorphism a b, ∀ d,
      (Fintype.equivFin D' (f.dart d)).val = (Fintype.equivFin D d).val := by
  simp only [encodeData,Prod.mk.injEq] at he
  obtain ⟨h1,h2,h3,h4,he⟩ := he
  exact same_code_ranked_isomorphism R K T I H hR hD hV hP hJ hD' hV' hP' hJ' a b
    (congrArg Fin.val h1) (congrArg Fin.val h2) (congrArg Fin.val h3) (congrArg Fin.val h4) he

end TorsionFreeZeroDivisors.PatternCoding

end

end OAI
