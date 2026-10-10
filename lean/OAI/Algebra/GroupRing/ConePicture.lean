import Mathlib
import OAI.Algebra.GroupRing.PlanarMap

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SphericalPicture
open scoped Classical
open PortSubdivision PermutationCycles CycleLists
variable {V D A O : Type} [Fintype O] (Γ : PortGraph V D) (label : D→A) (inv : A→A)
/-- A finite lifted spherical boundary map; empty boundary components are not
recorded. Unlike the disk certificate there is NO marked exceptional boundary.
This is combinatorial data, not yet a claim about a continuous sphere map. -/
structure Data where
  rotation : Equiv.Perm O
  partner : Equiv.Perm O
  involutive : Function.Involutive partner
  fixed_free : ∀ i,partner i≠i
  dart : O→D
  consistent : ∀ i,Γ.origin (Γ.reverse (dart i))=Γ.origin (dart (rotation i))
  compatible : ∀ i,label (dart (partner i))=inv (label (dart i))
  genusZero : MapEuler.GenusZero rotation partner
namespace Data
variable {Γ label inv} (a : Data (O:=O) Γ label inv)

def Reduced : Prop := (∀i,a.dart (a.partner i)≠Γ.reverse (a.dart i)) ∧
  ∀i,a.dart (a.rotation i)≠Γ.reverse (a.dart i)

variable {O' : Type} [Fintype O']
def reindex (e : O≃O') : Data (O:=O') Γ label inv where
  rotation := e.permCongr a.rotation
  partner := e.permCongr a.partner
  involutive := PermutationTransport.involutive e _ a.involutive
  fixed_free := PermutationTransport.fixed_free e _ a.fixed_free
  dart i := a.dart (e.symm i)
  consistent i := by simpa only [Equiv.permCongr_apply,e.symm_apply_apply] using a.consistent (e.symm i)
  compatible i := by simpa only [Equiv.permCongr_apply,e.symm_apply_apply] using a.compatible (e.symm i)
  genusZero := MapConjugation.genusZero e _ _ a.genusZero

variable (p q : O) (hpq : p≠q)
def band (hpair : a.partner p=q) (he : a.dart q=Γ.reverse (a.dart p)) :
    Data (O:=BandEuler.Residual p q hpq) Γ label inv where
  rotation := BandEuler.rotation a.rotation p q hpq
  partner := BandEuler.partner a.partner a.involutive p q hpq hpair
  involutive := BandEuler.partner_involutive a.partner a.involutive p q hpq hpair
  fixed_free i hi := by
    apply a.fixed_free (BandEuler.val p q hpq i)
    have hh := congrArg (BandEuler.val p q hpq) hi
    rwa [BandEuler.partner_val] at hh
  dart i := a.dart (BandEuler.val p q hpq i)
  consistent := BoundarySurgery.consistent a.rotation (Γ.origin ∘ a.dart)
    (Γ.origin ∘ Γ.reverse ∘ a.dart) p q hpq a.consistent
    (by dsimp;rw [he]) (by dsimp;rw [he,Γ.reverse_reverse])
  compatible i := by rw [BandEuler.partner_val];exact a.compatible _
  genusZero := BandEuler.genusZero_all a.rotation a.partner a.involutive p q hpq hpair a.genusZero

def tighten (hinv : Function.Involutive inv) (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
    (hsp : a.rotation p=q) (he : a.dart q=Γ.reverse (a.dart p)) :
    Data (O:=PartialMatchingSurgery.Remaining p q) Γ label inv where
  rotation := Tightening.rotation a.rotation p q hpq hsp
  partner := PartialMatchingSurgery.partner a.partner a.involutive p q hpq (a.fixed_free p) (a.fixed_free q)
  involutive := PartialMatchingSurgery.involutive a.partner a.involutive p q hpq (a.fixed_free p) (a.fixed_free q)
  fixed_free i := PartialMatchingSurgery.distinct a.partner a.involutive p q hpq (a.fixed_free p)
    (a.fixed_free q) i (a.fixed_free i)
  dart i := a.dart i
  consistent := Tightening.consistent a.rotation p q hpq hsp (Γ.origin ∘ a.dart)
    (Γ.origin ∘ Γ.reverse ∘ a.dart) a.consistent (by dsimp;rw [he,Γ.reverse_reverse])
  compatible i := PartialMatchingSurgery.compatible a.partner a.involutive p q hpq (a.fixed_free p)
    (a.fixed_free q) inv hinv (label ∘ a.dart) a.compatible (by dsimp;rw [he,hlabel]) i
  genusZero := Tightening.partial_genusZero a.rotation p q hpq hsp a.partner a.involutive
    (a.fixed_free p) (a.fixed_free q) a.genusZero

lemma unequal_backtrack (he : a.dart q=Γ.reverse (a.dart p)) : p≠q := by
  intro h
  subst q
  exact Γ.reverse_ne (a.dart p) he.symm

def boundaryRep (c : Cycle a.rotation) : O := Quotient.out c
lemma boundaryRep_cycle (c : Cycle a.rotation) : cycle a.rotation (a.boundaryRep c)=c := Quotient.out_eq c
def occurrences (c : Cycle a.rotation) : List O := orbit a.rotation (a.boundaryRep c)
def paths (c : Cycle a.rotation) : List D := (a.occurrences c).map a.dart
lemma occurrences_nonempty (c : Cycle a.rotation) : a.occurrences c≠[] := orbit_nonempty _ _
lemma paths_nonempty (c : Cycle a.rotation) : a.paths c≠[] := by
  intro he
  exact a.occurrences_nonempty c (List.map_eq_nil_iff.mp he)
lemma paths_length (c : Cycle a.rotation) : (a.paths c).length=(a.occurrences c).length := List.length_map _
lemma occurrences_succ (c : Cycle a.rotation) (i : ℕ) (hi : i+1<(a.occurrences c).length) :
    a.rotation ((a.occurrences c)[i])=(a.occurrences c)[i+1] := orbit_succ _ _ _ hi
lemma occurrences_last (c : Cycle a.rotation) :
    a.rotation ((a.occurrences c).getLast (a.occurrences_nonempty c))=
      (a.occurrences c).head (a.occurrences_nonempty c) := orbit_last _ _

variable (hr : a.Reduced)
include hr in
lemma paths_chain (c : Cycle a.rotation) : (a.paths c).IsChain
    (fun d e=>Γ.origin (Γ.reverse d)=Γ.origin e ∧ e≠Γ.reverse d) := by
  rw [paths,List.isChain_map,List.isChain_iff_getElem]
  intro i hi
  have hh := a.consistent ((a.occurrences c)[i])
  have hb := hr.2 ((a.occurrences c)[i])
  rw [a.occurrences_succ c i hi] at hh hb
  exact ⟨hh,hb⟩
include hr in
lemma paths_closed (c : Cycle a.rotation) :
    Γ.origin (Γ.reverse ((a.paths c).getLast (a.paths_nonempty c)))=
      Γ.origin ((a.paths c).head (a.paths_nonempty c)) ∧
    (a.paths c).head (a.paths_nonempty c)≠Γ.reverse ((a.paths c).getLast (a.paths_nonempty c)) := by
  have hh := a.consistent ((a.occurrences c).getLast (a.occurrences_nonempty c))
  have hb := hr.2 ((a.occurrences c).getLast (a.occurrences_nonempty c))
  rw [a.occurrences_last c] at hh hb
  simpa only [paths,List.head_map,List.getLast_map] using And.intro hh hb

def pathCoordinates : (Σc : Cycle a.rotation,Fin (a.paths c).length)≃O :=
  (Equiv.sigmaCongrRight fun c=>finCongr (a.paths_length c)).trans
    (coordinates a.rotation a.boundaryRep a.boundaryRep_cycle)
lemma pathCoordinates_apply (p : Σc : Cycle a.rotation,Fin (a.paths c).length) :
    a.pathCoordinates p=(a.occurrences p.1)[p.2.val]'(by simpa only [a.paths_length] using p.2.isLt) := rfl
lemma paths_dart (p : Σc : Cycle a.rotation,Fin (a.paths c).length) :
    (a.paths p.1)[p.2.val]=a.dart (a.pathCoordinates p) := by
  rw [a.pathCoordinates_apply p]
  exact List.getElem_map _
lemma pathCoordinates_rotate (c : Cycle a.rotation) (i : Fin (a.paths c).length) :
    a.pathCoordinates ⟨c,finRotate (a.paths c).length i⟩=a.rotation (a.pathCoordinates ⟨c,i⟩) := by
  simp only [pathCoordinates_apply]
  have hh := orbit_rotate a.rotation (a.boundaryRep c) (finCongr (a.paths_length c) i)
  have commute : ∀{m n : ℕ}(h : m=n)(i : Fin m),finCongr h (finRotate m i)=finRotate n (finCongr h i) := by
    intro m n h i;subst n;rfl
  exact (congrArg (fun j : Fin (a.occurrences c).length=>(a.occurrences c)[j.val])
    (commute (a.paths_length c) i)).trans hh
end Data
end TorsionFreeZeroDivisors.SphericalPicture

namespace TorsionFreeZeroDivisors.SampleGraph.SpherePicture
open scoped Classical
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep}
  {O : Type} [Fintype O]
  (a : SphericalPicture.Data (O:=O) (graph rep r) (label rep) Types.inverse) (hr : a.Reduced)

def system : PathSystem rep r x y where
  P := Cycle a.rotation
  E := Empty
  paths := a.paths
  nonempty := a.paths_nonempty
  root := none
  path_chain := a.paths_chain hr
  cyclic_chain c _ := by
    intro d hd e he
    rw [List.getLast?_eq_some_getLast (a.paths_nonempty c)] at hd
    rw [Option.mem_some] at hd
    rw [List.head?_eq_some_head (a.paths_nonempty c)] at he
    rw [Option.mem_some] at he
    subst d
    subst e
    exact a.paths_closed hr c
  comparisons := Comparisons.empty _
  lower := Empty.elim
  upper := Empty.elim
  lower_eq := fun e=>Empty.elim e
  upper_eq := fun e=>Empty.elim e
  lower_le := fun e=>Empty.elim e
  upper_le := fun e=>Empty.elim e
  reduced := fun _ e=>Empty.elim e
  rootA q hq := by cases hq
  rootB q hq := by cases hq
  compatible := fun _ e=>Empty.elim e

def coordinates : Position (fun c=>(a.paths c).length)≃O :=
  (WordPositions.fin _).trans a.pathCoordinates
lemma dart (p : Position (fun c=>(a.paths c).length)) :
    RawDecomposition.dart a.paths p=a.dart (coordinates a p) := by
  rw [←(WordPositions.fin _).symm_apply_apply p,WordPositions.dart_fin]
  exact a.paths_dart _
lemma rotation (p : Position (fun c=>(a.paths c).length)) :
    coordinates a (BoundaryRotation.perm (fun c=>(a.paths c).length) p)=a.rotation (coordinates a p) := by
  generalize he : (WordPositions.fin (fun c=>(a.paths c).length)) p=q
  have hp : p=(WordPositions.fin _).symm q := by rw [←he,Equiv.symm_apply_apply]
  rw [hp]
  rcases q with ⟨c,i⟩
  rw [BoundaryRotation.apply_fin]
  simp only [coordinates,Equiv.trans_apply,Equiv.apply_symm_apply]
  exact a.pathCoordinates_rotate c i
lemma rotation_conjugate : BoundaryRotation.perm (fun c=>(a.paths c).length)=
    (coordinates a).symm.permCongr a.rotation := by
  apply Equiv.ext
  intro p
  apply (coordinates a).injective
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  exact rotation a p
lemma partner_compatible (p : Position (fun c=>(a.paths c).length)) :
    label rep (RawDecomposition.dart a.paths ((coordinates a).symm.permCongr a.partner p))=
      Types.inverse (label rep (RawDecomposition.dart a.paths p)) := by
  rw [dart,dart]
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  exact a.compatible _
include hr in
lemma partner_reduced (p : Position (fun c=>(a.paths c).length)) :
    RawDecomposition.dart a.paths p≠RawDecomposition.dart a.paths ((coordinates a).symm.permCongr a.partner p) ∧
    RawDecomposition.dart a.paths p≠(graph rep r).reverse
      (RawDecomposition.dart a.paths ((coordinates a).symm.permCongr a.partner p)) := by
  rw [dart,dart]
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  constructor
  · intro he
    have hh := a.compatible (coordinates a p)
    rw [←he] at hh
    exact Types.inverse_ne _ hh.symm
  · intro he
    apply hr.1 (coordinates a p)
    have hh := congrArg (graph rep r).reverse he
    rw [(graph rep r).reverse_reverse] at hh
    exact hh.symm

def pairing : FullPairing (system (x:=x) (y:=y) a hr) where
  perm := (coordinates a).symm.permCongr a.partner
  involutive := PermutationTransport.involutive _ _ a.involutive
  fixed_free := PermutationTransport.fixed_free _ _ a.fixed_free
  compatible p := partner_compatible a p
  reduced p := partner_reduced a hr p
lemma pairing_genusZero : MapEuler.GenusZero
    (BoundaryRotation.perm (fun c=>(a.paths c).length)) (pairing (x:=x) (y:=y) a hr).perm := by
  change MapEuler.GenusZero (BoundaryRotation.perm (fun c=>(a.paths c).length))
    ((coordinates a).symm.permCongr a.partner)
  rw [rotation_conjugate]
  exact MapConjugation.genusZero (coordinates a).symm _ _ a.genusZero
lemma pairing_euler [Nonempty O] : (pairing (x:=x) (y:=y) a hr).Euler := by
  let : Nonempty (Position (fun c=>((system (x:=x) (y:=y) a hr).paths c).length)) :=
    ⟨(coordinates a).symm (Classical.choice inferInstance)⟩
  exact MapEuler.euler_of_genusZero _ _ (pairing_genusZero a hr) (pairing a hr).fixed_free
lemma system_ordinary [Nonempty O] : ∃c,(system (x:=x) (y:=y) a hr).root≠some c :=
  ⟨cycle a.rotation (Classical.choice inferInstance),by intro h;cases h⟩

/-- Unconditional sharp split for the prepared all-cyclic spherical system. -/
lemma separator (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
    (S : Finset ((pairing (x:=x) (y:=y) a hr).prepared hL hd).P) :
    Nonempty (RecursiveSeparator.Split (PairingClusters.Rel
      (fun p : Position (fun t=>(((pairing a hr).prepared hL hd).paths t).length)=>p.1)
      ((pairing a hr).prepared hL hd).comparisons.pairing.partner) S) := by
  let s := system (x:=x) (y:=y) a hr
  let cap := FullPairing.U₀*GirthAsymptotics.L (TypedGraphs.size rep)
  let hc : 0<cap := FullPairing.cap_positive hL
  have hp : ∀p,0<BalancedRotation.len s.paths cap hc p := fun p=>
    List.length_pos_iff.mpr (BalancedWords.segment_nonempty s.paths cap hc s.nonempty p)
  have hz := BalancedGenus.genusZero s.paths cap hc (pairing a hr).perm
    (pairing a hr).involutive (pairing_genusZero a hr)
  obtain ⟨P⟩ := BoundaryRotation.split (BalancedRotation.len s.paths cap hc) hp
    ((pairing a hr).α cap hc) ((pairing a hr).α_involutive cap hc) hz S
  exact ⟨(pairing a hr).closed_split cap hc (by omega) hd _ S P⟩

include a hr in
/-- There is no NONEMPTY reduced spherical boundary certificate in the sample. -/
theorem excluded [Nonempty O] (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep))
    (hd : GraphSample.Diameters rep r) (hsample : r∈ActualPatternEvent.samples rep)
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y)) :
    False :=
  FullPairing.excluded (pairing a hr) hL hd hsample (system_ordinary a hr) (pairing_euler a hr)
    (fun S _=>separator a hr hL hd S) havoid
end TorsionFreeZeroDivisors.SampleGraph.SpherePicture

namespace TorsionFreeZeroDivisors.SphericalPicture
open scoped Classical
variable {V D A : Type} (Γ : PortSubdivision.PortGraph V D) (label : D→A) (inv : A→A)
/-- Literal finite surgery trace, including the empty terminal picture.  This
records no geometric realization or implicit essentiality hypothesis. -/
inductive ReducesToEmpty : {O : Type} → [Fintype O] → Data (O:=O) Γ label inv → Prop
  | empty {O : Type} [Fintype O] (a : Data (O:=O) Γ label inv) (h : IsEmpty O) :
      ReducesToEmpty a
  | band {O : Type} [Fintype O] (a : Data (O:=O) Γ label inv) (p q : O) (hpq : p≠q)
      (hpair : a.partner p=q) (he : a.dart q=Γ.reverse (a.dart p))
      (next : ReducesToEmpty (a.band p q hpq hpair he)) : ReducesToEmpty a
  | tighten {O : Type} [Fintype O] (a : Data (O:=O) Γ label inv) (p q : O) (hpq : p≠q)
      (hinv : Function.Involutive inv) (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
      (hsp : a.rotation p=q) (he : a.dart q=Γ.reverse (a.dart p))
      (next : ReducesToEmpty (a.tighten p q hpq hinv hlabel hsp he)) : ReducesToEmpty a
variable {Γ label inv}
namespace Data
variable {O : Type} [Fintype O] (p q : O) (hpq : p≠q)
def deletionCoordinates : BandEuler.Residual p q hpq ≃ PartialMatchingSurgery.Remaining p q where
  toFun z := ⟨BandEuler.val p q hpq z,BandEuler.val_ne_p p q hpq z,BandEuler.val_ne_q p q hpq z⟩
  invFun z := ⟨⟨z,z.property.1⟩,fun he=>z.property.2 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl
include hpq in
lemma remaining_two_fewer : Fintype.card (PartialMatchingSurgery.Remaining p q)+2=Fintype.card O := by
  rw [←Fintype.card_congr (deletionCoordinates p q hpq)]
  exact BandEuler.two_fewer p q hpq
end Data
/-- Strong induction on the actual number of boundary occurrences: each
nonterminal step deletes two occurrences. -/
theorem reduces_of_no_reduced (hinv : Function.Involutive inv)
    (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
    (hex : ∀{O : Type}[Fintype O][Nonempty O](a : Data (O:=O) Γ label inv),¬a.Reduced)
    {O : Type} [Fintype O] (a : Data (O:=O) Γ label inv) : ReducesToEmpty Γ label inv a := by
  generalize he : Fintype.card O=n
  induction n using Nat.strong_induction_on generalizing O with
  | h n ih =>
    by_cases hzero : IsEmpty O
    · exact .empty a hzero
    let : Nonempty O := not_isEmpty_iff.mp hzero
    have hn := hex a
    simp only [Data.Reduced,not_and_or,not_forall,Classical.not_not] at hn
    rcases hn with ⟨p,hp⟩ | ⟨p,hp⟩
    · let q := a.partner p
      have hpq : p≠q := (a.fixed_free p).symm
      refine .band a p q hpq rfl hp (ih (Fintype.card (BandEuler.Residual p q hpq)) ?_ _ rfl)
      have hc := BandEuler.two_fewer p q hpq
      omega
    · let q := a.rotation p
      have hpq : p≠q := a.unequal_backtrack p q hp
      refine .tighten a p q hpq hinv hlabel rfl hp
        (ih (Fintype.card (PartialMatchingSurgery.Remaining p q)) ?_ _ rfl)
      have hc := Data.remaining_two_fewer p q hpq
      omega
end TorsionFreeZeroDivisors.SphericalPicture
namespace TorsionFreeZeroDivisors.SampleGraph.SpherePicture
open scoped Classical
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep}
theorem reduces_to_empty
    (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep))
    (hd : GraphSample.Diameters rep r) (hsample : r∈ActualPatternEvent.samples rep)
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))
    {O : Type} [Fintype O]
    (a : SphericalPicture.Data (O:=O) (graph rep r) (label rep) Types.inverse) :
    SphericalPicture.ReducesToEmpty (graph rep r) (label rep) Types.inverse a := by
  apply SphericalPicture.reduces_of_no_reduced Types.inverse_inverse (fun d=>label_reverse rep r d)
  intro O _ _ b hr
  exact excluded b hr hL hd hsample havoid
end TorsionFreeZeroDivisors.SampleGraph.SpherePicture

namespace TorsionFreeZeroDivisors.ConePicture
open PortSubdivision GraphPresentation SphericalPicture
open scoped Classical
variable {V D A : Type} (Γ : PortGraph V D) (R : Routes Γ)
abbrev Radial := {v : V // v≠R.base v}
abbrev Dart := D ⊕ (Radial Γ R × Bool)
def reverse : Dart Γ R→Dart Γ R
  | .inl d => .inl (Γ.reverse d)
  | .inr (v,b) => .inr (v,!b)
def origin : Dart Γ R→V
  | .inl d => Γ.origin d
  | .inr (v,b) => if b then R.base v else v
/-- The one-skeleton in an abstract graph cone after its root radial edge
is collapsed. Physical graph edges and all other radial edges are retained. -/
def graph : PortGraph V (Dart Γ R) where
  origin := origin Γ R
  reverse := reverse Γ R
  reverse_reverse d := by
    rcases d with d|⟨v,b⟩
    · exact congrArg Sum.inl (Γ.reverse_reverse d)
    · cases b <;> rfl
  reverse_ne d := by
    rcases d with d|⟨v,b⟩
    · intro he; exact Γ.reverse_ne d (Sum.inl.inj he)
    · cases b <;> simp [reverse]
variable (label : D→A) (inv : A→A)
def labels : Dart Γ R→ A ⊕ (Radial Γ R × Bool)
  | .inl d => .inl (label d)
  | .inr p => .inr p
def inverse : A ⊕ (Radial Γ R × Bool) → A ⊕ (Radial Γ R × Bool)
  | .inl a => .inl (inv a)
  | .inr (v,b) => .inr (v,!b)
lemma inverse_inverse (hi : Function.Involutive inv) : Function.Involutive (inverse Γ R inv) := by
  rintro (a|⟨v,b⟩)
  · exact congrArg Sum.inl (hi a)
  · cases b <;> rfl
lemma label_reverse (hl : ∀d,label (Γ.reverse d)=inv (label d)) (d : Dart Γ R) :
    labels Γ R label ((graph Γ R).reverse d)=inverse Γ R inv (labels Γ R label d) := by
  rcases d with d|⟨v,b⟩
  · exact congrArg Sum.inl (hl d)
  · rfl
variable {Γ R label inv} {O : Type} [Fintype O]
  (a : Data (O:=O) (graph Γ R) (labels Γ R label) (inverse Γ R inv))
lemma reduced_old (hr : a.Reduced) (i : O) : ∃d,a.dart i=Sum.inl d := by
  cases he : a.dart i with
  | inl d => exact ⟨d,rfl⟩
  | inr p =>
    exfalso
    have hc := a.compatible i
    rw [he] at hc
    have hp : a.dart (a.partner i)=Sum.inr (p.1,!p.2) := by
      cases hq : a.dart (a.partner i) with
      | inl d => simp [hq,labels,inverse] at hc
      | inr q =>
        have heq : q=(p.1,!p.2) := Sum.inr.inj (by simpa only [hq,labels,inverse] using hc)
        rw [heq]
    exact hr.1 i (by rw [he,hp];rfl)
/-- Removing the ghost radial alphabet from a reduced picture changes
NEITHER its permutation genus nor its boundary representatives. -/
def oldData (hr : a.Reduced) : Data (O:=O) Γ label inv where
  rotation := a.rotation
  partner := a.partner
  involutive := a.involutive
  fixed_free := a.fixed_free
  dart i := (reduced_old a hr i).choose
  consistent i := by
    have h := a.consistent i
    rw [(reduced_old a hr i).choose_spec,(reduced_old a hr (a.rotation i)).choose_spec] at h
    exact h
  compatible i := by
    have h := a.compatible i
    rw [(reduced_old a hr i).choose_spec,(reduced_old a hr (a.partner i)).choose_spec] at h
    exact Sum.inl.inj h
  genusZero := a.genusZero
lemma oldData_reduced (hr : a.Reduced) : (oldData a hr).Reduced := by
  constructor
  · intro i hi
    apply hr.1 i
    rw [(reduced_old a hr i).choose_spec,(reduced_old a hr (a.partner i)).choose_spec]
    exact congrArg Sum.inl hi
  · intro i hi
    apply hr.2 i
    rw [(reduced_old a hr i).choose_spec,(reduced_old a hr (a.rotation i)).choose_spec]
    exact congrArg Sum.inl hi
variable (hi : Function.Involutive inv) (hl : ∀d,label (Γ.reverse d)=inv (label d))
include hi hl in
/-- Actual triangular cone presentations introduce no extra reduced spherical
pictures: every paired radial occurrence is the very same physical radial edge. -/
theorem reduces_to_empty
    (hex : ∀{P : Type}[Fintype P][Nonempty P](b : Data (O:=P) Γ label inv),¬b.Reduced) :
    ReducesToEmpty (graph Γ R) (labels Γ R label) (inverse Γ R inv) a := by
  apply SphericalPicture.reduces_of_no_reduced (inverse_inverse Γ R inv hi) (label_reverse Γ R label inv hl)
  intro P _ _ b hb
  exact hex (oldData b hb) (oldData_reduced b hb)
end TorsionFreeZeroDivisors.ConePicture

end

end OAI
