import Mathlib
import OAI.Algebra.GroupRing.ClosedWords

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.CycleLists
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
def orbit (x : O) : List O := if f x=x then [x] else f.toList x
lemma mem_orbit {x y : O} : y∈orbit f x ↔ f.SameCycle x y := by
  by_cases hx : f x=x
  · simp only [orbit,ite_eq_left hx,List.mem_singleton]
    exact ⟨fun h=>h.symm.sameCycle f,fun h=>(h.eq_of_left hx).symm⟩
  · rw [orbit,ite_eq_right hx,Equiv.Perm.mem_toList_iff]
    exact and_iff_left (Equiv.Perm.mem_support.mpr hx)
lemma orbit_nonempty (x : O) : orbit f x≠[] :=
  List.ne_nil_of_mem ((mem_orbit f).mpr (Equiv.Perm.SameCycle.refl f x))
lemma orbit_nodup (x : O) : (orbit f x).Nodup := by
  by_cases hx : f x=x
  · simp only [orbit,ite_eq_left hx,List.nodup_singleton]
  · rw [orbit,ite_eq_right hx]
    exact f.nodup_toList x
lemma orbit_head (x : O) : (orbit f x).head (orbit_nonempty f x)=x := by
  by_cases hx : f x=x
  · simp only [orbit,ite_eq_left hx,List.head_cons]
  · simpa only [orbit,ite_eq_right hx,List.head_eq_getElem] using
      f.toList_getElem_zero x (Equiv.Perm.mem_support.mpr hx)
lemma orbit_next {x y : O} (hy : y∈orbit f x) : (orbit f x).next y hy=f y := by
  by_cases hx : f x=x
  · have he : y=x := by simpa only [orbit,ite_eq_left hx,List.mem_singleton] using hy
    subst y
    simp [orbit,hx]
  · simpa only [orbit,ite_eq_right hx] using f.next_toList_eq_apply x y
      (by simpa only [orbit,ite_eq_right hx] using hy)
lemma orbit_rotate (x : O) (i : Fin (orbit f x).length) :
    (orbit f x)[(finRotate (orbit f x).length i).val]=f ((orbit f x)[i.val]) := by
  have h := orbit_next f (List.getElem_mem i.isLt)
  rw [List.next_getElem _ (orbit_nodup f x)] at h
  have hv : (finRotate (orbit f x).length i).val=(i.val+1)%(orbit f x).length := by
    let _ := i.neZero
    rw [finRotate_apply,Fin.val_add,Fin.val_one',Nat.add_mod_mod]
  simpa only [hv] using h
lemma orbit_succ (x : O) (i : ℕ) (hi : i+1<(orbit f x).length) :
    f ((orbit f x)[i])=(orbit f x)[i+1] := by
  have h := orbit_next f (List.getElem_mem (by omega : i<(orbit f x).length))
  rw [List.next_getElem _ (orbit_nodup f x)] at h
  simpa only [Nat.mod_eq_of_lt hi] using h.symm
lemma orbit_last (x : O) :
    f ((orbit f x).getLast (orbit_nonempty f x))=(orbit f x).head (orbit_nonempty f x) := by
  exact (orbit_next f (List.getLast_mem (orbit_nonempty f x))).symm.trans
    (List.next_getLast_eq_head (orbit f x) (orbit_nonempty f x) (orbit_nodup f x))
variable (rep : Cycle f→O) (hrep : ∀c,cycle f (rep c)=c)
def words (c : Cycle f) : List O := orbit f (rep c)
def atIndex (p : Σc : Cycle f,Fin (words f rep c).length) : O := (words f rep p.1)[p.2.val]
include hrep in
lemma atIndex_cycle (p : Σc : Cycle f,Fin (words f rep c).length) :
    cycle f (atIndex f rep p)=p.1 := by
  have hm : atIndex f rep p∈orbit f (rep p.1) := List.getElem_mem p.2.isLt
  exact ((cycle_eq f).mpr ((mem_orbit f).mp hm)).symm.trans (hrep p.1)
include hrep in
lemma atIndex_bijective : Function.Bijective (atIndex f rep) := by
  constructor
  · rintro ⟨c,i⟩ ⟨d,j⟩ he
    have hd : c=d := (atIndex_cycle f rep hrep ⟨c,i⟩).symm.trans
      ((congrArg (cycle f) he).trans (atIndex_cycle f rep hrep ⟨d,j⟩))
    subst d
    have hi : i=j := (List.nodup_iff_injective_getElem.mp (orbit_nodup f (rep c))) he
    subst j
    rfl
  · intro x
    let c := cycle f x
    have hx : x∈words f rep c := (mem_orbit f).mpr ((cycle_eq f).mp (hrep c))
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
    exact ⟨⟨c,⟨i,hi⟩⟩,he⟩
def coordinates : (Σc : Cycle f,Fin (words f rep c).length)≃O :=
  Equiv.ofBijective (atIndex f rep) (atIndex_bijective f rep hrep)
lemma atIndex_rotate (c : Cycle f) (i : Fin (words f rep c).length) :
    atIndex f rep ⟨c,finRotate (words f rep c).length i⟩=f (atIndex f rep ⟨c,i⟩) :=
  orbit_rotate f (rep c) i
lemma coordinates_rotate (c : Cycle f) (i : Fin (words f rep c).length) :
    coordinates f rep hrep ⟨c,finRotate (words f rep c).length i⟩=
      f (coordinates f rep hrep ⟨c,i⟩) := atIndex_rotate f rep c i
/-- Prescribe the representative of one root cycle without disturbing others. -/
def rootedRep (z : O) (c : Cycle f) : O := if c=cycle f z then z else Quotient.out c
omit [Fintype O] in
lemma rootedRep_cycle (z : O) (c : Cycle f) : cycle f (rootedRep f z c)=c := by
  by_cases hc : c=cycle f z
  · simp only [rootedRep,ite_eq_left hc];exact hc.symm
  · rw [rootedRep,ite_eq_right hc]
    exact Quotient.out_eq c
omit [Fintype O] in
lemma rootedRep_root (z : O) : rootedRep f z (cycle f z)=z := by simp [rootedRep]
end TorsionFreeZeroDivisors.CycleLists

namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
open PermutationCycles CycleLists
variable {V D A O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D}
  {label : D→A} {inv : A→A} {x y : V} (a : Data (O:=O) Γ label inv x y) (hxy : x≠y)
def rootCycle : Cycle a.closedRotation := cycle a.closedRotation (a.first hxy)
def boundaryRep : Cycle a.closedRotation→a.Occ := rootedRep a.closedRotation (a.first hxy)
def occurrences (c : Cycle a.closedRotation) : List a.Occ := orbit a.closedRotation (a.boundaryRep hxy c)
def paths (c : Cycle a.closedRotation) : List D := (a.occurrences hxy c).map a.edge
lemma occurrences_nonempty (c : Cycle a.closedRotation) : a.occurrences hxy c≠[] := orbit_nonempty _ _
lemma occurrences_nodup (c : Cycle a.closedRotation) : (a.occurrences hxy c).Nodup := orbit_nodup _ _
lemma paths_nonempty (c : Cycle a.closedRotation) : a.paths hxy c≠[] := by
  intro he
  exact a.occurrences_nonempty hxy c (List.map_eq_nil_iff.mp he)
lemma paths_length (c : Cycle a.closedRotation) : (a.paths hxy c).length=(a.occurrences hxy c).length := List.length_map _
lemma occurrences_cycle {c : Cycle a.closedRotation} {i : a.Occ} (hi : i∈a.occurrences hxy c) :
    cycle a.closedRotation i=c := by
  have hh := (mem_orbit a.closedRotation).mp hi
  exact ((cycle_eq _).mpr hh).symm.trans (rootedRep_cycle _ _ c)
lemma occurrences_root_head : (a.occurrences hxy (a.rootCycle hxy)).head (a.occurrences_nonempty hxy _) =a.first hxy := by
  change (orbit a.closedRotation (a.boundaryRep hxy (a.rootCycle hxy))).head _=a.first hxy
  rw [orbit_head]
  exact rootedRep_root _ _
lemma root_occurrence_position {c : Cycle a.closedRotation} (i : Fin (a.occurrences hxy c).length)
    (hi : (a.occurrences hxy c)[i.val]=a.first hxy) : c=a.rootCycle hxy ∧ i.val=0 := by
  have hc : c=a.rootCycle hxy := (a.occurrences_cycle hxy (List.getElem_mem i.isLt)).symm.trans
    (congrArg (cycle a.closedRotation) hi)
  subst c
  have hp : 0<(a.occurrences hxy (a.rootCycle hxy)).length := List.length_pos_iff.mpr (a.occurrences_nonempty hxy _)
  have hz : (a.occurrences hxy (a.rootCycle hxy))[0]=a.first hxy := by
    simpa only [List.head_eq_getElem] using a.occurrences_root_head hxy
  have he : i=⟨0,hp⟩ := (List.nodup_iff_injective_getElem.mp (a.occurrences_nodup hxy _)) (hi.trans hz.symm)
  exact ⟨rfl,congrArg Fin.val he⟩
lemma occurrences_succ {c : Cycle a.closedRotation} (i : ℕ) (hi : i+1<(a.occurrences hxy c).length) :
    a.closedRotation ((a.occurrences hxy c)[i])=(a.occurrences hxy c)[i+1] := orbit_succ _ _ _ hi
lemma occurrences_succ_ne_first {c : Cycle a.closedRotation} (i : ℕ) (hi : i+1<(a.occurrences hxy c).length) :
    a.closedRotation ((a.occurrences hxy c)[i])≠a.first hxy := by
  rw [a.occurrences_succ hxy i hi]
  intro he
  have hh := (a.root_occurrence_position hxy ⟨i+1,hi⟩ he).2
  simp only at hh
  omega
lemma occurrences_last (c : Cycle a.closedRotation) :
    a.closedRotation ((a.occurrences hxy c).getLast (a.occurrences_nonempty hxy c))=
      (a.occurrences hxy c).head (a.occurrences_nonempty hxy c) := orbit_last _ _
lemma ordinary_last_ne_first (c : Cycle a.closedRotation) (hc : c≠a.rootCycle hxy) :
    a.closedRotation ((a.occurrences hxy c).getLast (a.occurrences_nonempty hxy c))≠a.first hxy := by
  intro he
  apply hc
  have hm : a.closedRotation ((a.occurrences hxy c).getLast (a.occurrences_nonempty hxy c))∈a.occurrences hxy c := by
    rw [a.occurrences_last hxy c]
    exact List.head_mem _
  exact (a.occurrences_cycle hxy hm).symm.trans (congrArg (cycle a.closedRotation) he)
variable (hr : a.Reduced)
include hr in
lemma paths_chain (c : Cycle a.closedRotation) : (a.paths hxy c).IsChain
    (fun d e=>Γ.origin (Γ.reverse d)=Γ.origin e ∧ e≠Γ.reverse d) := by
  rw [paths,List.isChain_map,List.isChain_iff_getElem]
  intro i hi
  have hn := a.occurrences_succ_ne_first hxy i hi
  have hh := a.edge_consistent hxy ((a.occurrences hxy c)[i]) hn
  have hb := a.edge_no_backtrack hxy hr ((a.occurrences hxy c)[i]) hn
  rw [a.occurrences_succ hxy i hi] at hh hb
  exact ⟨hh,hb⟩
include hr in
lemma paths_closed (c : Cycle a.closedRotation) (hc : c≠a.rootCycle hxy) :
    Γ.origin (Γ.reverse ((a.paths hxy c).getLast (a.paths_nonempty hxy c)))=
      Γ.origin ((a.paths hxy c).head (a.paths_nonempty hxy c)) ∧
    (a.paths hxy c).head (a.paths_nonempty hxy c)≠
      Γ.reverse ((a.paths hxy c).getLast (a.paths_nonempty hxy c)) := by
  have hn := a.ordinary_last_ne_first hxy c hc
  have hh := a.edge_consistent hxy ((a.occurrences hxy c).getLast (a.occurrences_nonempty hxy c)) hn
  have hb := a.edge_no_backtrack hxy hr ((a.occurrences hxy c).getLast (a.occurrences_nonempty hxy c)) hn
  rw [a.occurrences_last hxy c] at hh hb
  simpa only [paths,List.head_map,List.getLast_map] using And.intro hh hb
lemma paths_root_begins : Γ.origin ((a.paths hxy (a.rootCycle hxy)).head (a.paths_nonempty hxy _))=x := by
  simpa only [paths,List.head_map,a.occurrences_root_head hxy] using a.first_start hxy
lemma paths_root_ends : Γ.origin (Γ.reverse ((a.paths hxy (a.rootCycle hxy)).getLast (a.paths_nonempty hxy _)))=y := by
  simp only [paths,List.getLast_map]
  apply a.last_end hxy
  rw [a.occurrences_last hxy,a.occurrences_root_head hxy]
/-- Every literal boundary position is exactly one surviving picture occurrence. -/
def pathCoordinates : (Σ c : Cycle a.closedRotation,Fin (a.paths hxy c).length)≃a.Occ :=
  (Equiv.sigmaCongrRight fun c=>finCongr (a.paths_length hxy c)).trans
    (coordinates a.closedRotation (a.boundaryRep hxy) (rootedRep_cycle _ _))
lemma pathCoordinates_apply (p : Σ c : Cycle a.closedRotation,Fin (a.paths hxy c).length) :
    a.pathCoordinates hxy p=(a.occurrences hxy p.1)[p.2.val]'(by simpa only [a.paths_length] using p.2.isLt) := rfl
lemma paths_dart (p : Σ c : Cycle a.closedRotation,Fin (a.paths hxy c).length) :
    (a.paths hxy p.1)[p.2.val]=a.edge (a.pathCoordinates hxy p) := by
  rw [a.pathCoordinates_apply hxy p]
  exact List.getElem_map _
lemma pathCoordinates_rotate (c : Cycle a.closedRotation) (i : Fin (a.paths hxy c).length) :
    a.pathCoordinates hxy ⟨c,finRotate (a.paths hxy c).length i⟩=
      a.closedRotation (a.pathCoordinates hxy ⟨c,i⟩) := by
  simp only [pathCoordinates_apply]
  have hh := orbit_rotate a.closedRotation (a.boundaryRep hxy c)
    (finCongr (a.paths_length hxy c) i)
  have commute : ∀ {n m : ℕ} (h : n=m) (i : Fin n),
      finCongr h (finRotate n i)=finRotate m (finCongr h i) := by
    intro n m h i
    subst m
    rfl
  exact (congrArg (fun j : Fin (a.occurrences hxy c).length=>(a.occurrences hxy c)[j.val])
    (commute (a.paths_length hxy c) i)).trans hh
end TorsionFreeZeroDivisors.FinitePicture.Data

namespace TorsionFreeZeroDivisors.ComparedBlocks.Comparisons
open scoped Classical
open BlockAlignment
def empty {T : Type} (len : T→ℕ) : Comparisons (E:=Empty) len where
  pairing := ⟨id,fun _=>rfl⟩
  side := fun _=>none
  flip := Empty.elim
  flip_inv := fun e=>Empty.elim e
  flip_ne := fun e=>Empty.elim e
  side_partner := fun _ e=>Empty.elim e
  none_iff := fun _=>⟨fun _=>rfl,fun _=>rfl⟩
  source := Empty.elim
  lo := Empty.elim
  hi := Empty.elim
  reverse := Empty.elim
  offset := Empty.elim
  side_iff := fun _ e=>Empty.elim e
  partner_source := fun _ e=>Empty.elim e
  partner_coordinate := fun _ e=>Empty.elim e
  target_range := fun e=>Empty.elim e
end TorsionFreeZeroDivisors.ComparedBlocks.Comparisons
namespace TorsionFreeZeroDivisors.SampleGraph.Picture
open scoped Classical
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep} {z w : VA rep⊕VB rep}
  {O : Type} [Fintype O]
  (a : FinitePicture.Data (O:=O) (graph rep r) (label rep) Types.inverse z w)
  (hzw : z≠w) (hr : a.Reduced) (hz : z=Sum.inl x ∨ z=Sum.inr y)
def system : PathSystem rep r x y where
  P := Cycle a.closedRotation
  E := Empty
  paths := a.paths hzw
  nonempty := a.paths_nonempty hzw
  root := some (a.rootCycle hzw)
  path_chain := a.paths_chain hzw hr
  cyclic_chain c hc := by
    have hd : c≠a.rootCycle hzw := by
      have hc' := hc
      simp only [StageRoot.cyclic,decide_eq_true_eq] at hc'
      exact fun he=>hc' (congrArg some he.symm)
    intro d hd' e he
    rw [List.getLast?_eq_some_getLast (a.paths_nonempty hzw c)] at hd'
    rw [Option.mem_some] at hd'
    rw [List.head?_eq_some_head (a.paths_nonempty hzw c)] at he
    rw [Option.mem_some] at he
    subst d
    subst e
    exact a.paths_closed hzw hr c hd
  comparisons := Comparisons.empty _
  lower := Empty.elim
  upper := Empty.elim
  lower_eq := fun e=>Empty.elim e
  upper_eq := fun e=>Empty.elim e
  lower_le := fun e=>Empty.elim e
  upper_le := fun e=>Empty.elim e
  reduced := fun _ e=>Empty.elim e
  rootA q hq := by
    have he : z=Sum.inl q := by
      simpa only [Option.map_some,a.paths_root_begins hzw,Option.some.injEq] using hq
    rcases hz with ha|hb
    · exact Sum.inl.inj (he.symm.trans ha)
    · exact False.elim (Sum.inl_ne_inr (he.symm.trans hb))
  rootB q hq := by
    have he : z=Sum.inr q := by
      simpa only [Option.map_some,a.paths_root_begins hzw,Option.some.injEq] using hq
    rcases hz with ha|hb
    · exact False.elim (Sum.inr_ne_inl (he.symm.trans ha))
    · exact Sum.inr.inj (he.symm.trans hb)
  compatible := fun _ e=>Empty.elim e

def coordinates : Position (fun c=>(a.paths hzw c).length)≃a.Occ :=
  (WordPositions.fin _).trans (a.pathCoordinates hzw)
lemma dart (p : Position (fun c=>(a.paths hzw c).length)) :
    RawDecomposition.dart (a.paths hzw) p=a.edge (coordinates a hzw p) := by
  rw [←(WordPositions.fin _).symm_apply_apply p,WordPositions.dart_fin]
  exact a.paths_dart hzw _
lemma rotation (p : Position (fun c=>(a.paths hzw c).length)) :
    coordinates a hzw (BoundaryRotation.perm (fun c=>(a.paths hzw c).length) p)=
      a.closedRotation (coordinates a hzw p) := by
  generalize he : (WordPositions.fin (fun c=>(a.paths hzw c).length)) p=q
  have hp : p=(WordPositions.fin _).symm q := by rw [←he,Equiv.symm_apply_apply]
  rw [hp]
  rcases q with ⟨c,i⟩
  rw [BoundaryRotation.apply_fin]
  simp only [coordinates,Equiv.trans_apply,Equiv.apply_symm_apply]
  exact a.pathCoordinates_rotate hzw c i

lemma partner_compatible (p : Position (fun c=>(a.paths hzw c).length)) :
    label rep (RawDecomposition.dart (a.paths hzw) ((coordinates a hzw).symm.permCongr a.fullPartner p))=
      Types.inverse (label rep (RawDecomposition.dart (a.paths hzw) p)) := by
  rw [dart,dart]
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  exact a.edge_compatible _
include hr in
lemma partner_reduced (p : Position (fun c=>(a.paths hzw c).length)) :
    RawDecomposition.dart (a.paths hzw) p≠RawDecomposition.dart (a.paths hzw) ((coordinates a hzw).symm.permCongr a.fullPartner p) ∧
    RawDecomposition.dart (a.paths hzw) p≠(graph rep r).reverse (RawDecomposition.dart (a.paths hzw) ((coordinates a hzw).symm.permCongr a.fullPartner p)) := by
  rw [dart,dart]
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  exact a.edge_reduced hr (fun d=>Types.inverse_ne (label rep d)) _

def pairing : FullPairing (system a hzw hr hz) where
  perm := (coordinates a hzw).symm.permCongr a.fullPartner
  involutive := PermutationTransport.involutive _ _ a.fullPartner_involutive
  fixed_free := PermutationTransport.fixed_free _ _ a.fullPartner_nonfixed
  compatible p := partner_compatible a hzw p
  reduced p := partner_reduced a hzw hr p

lemma rotation_conjugate : BoundaryRotation.perm (fun c=>(a.paths hzw c).length)=
    (coordinates a hzw).symm.permCongr a.closedRotation := by
  apply Equiv.ext
  intro p
  apply (coordinates a hzw).injective
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  exact rotation a hzw p
/-- Literal finite marked-certificate reduction supplies the Euler hypothesis
of the actual boundary-pairing exclusion; nothing geometric is assumed here. -/
lemma pairing_euler : (pairing a hzw hr hz).Euler := by
  change Fintype.card (Position (fun c=>(a.paths hzw c).length))+4≤
    2*Fintype.card (Cycle (BoundaryRotation.perm (fun c=>(a.paths hzw c).length)))+
    2*Fintype.card (Cycle ((coordinates a hzw).symm.permCongr a.fullPartner *
      BoundaryRotation.perm (fun c=>(a.paths hzw c).length)))
  rw [rotation_conjugate,←PermutationTransport.mul,PermutationTransport.card_cycles,
    PermutationTransport.card_cycles,Fintype.card_congr (coordinates a hzw)]
  exact a.closedRotation_euler hzw
lemma system_ordinary : ∃c,(system a hzw hr hz).root≠some c := by
  obtain ⟨c,hc⟩ := a.ordinary_boundary hzw hr (label_reverse rep r) (immersed rep r)
  exact ⟨c,fun he=>hc (Option.some.inj he).symm⟩
lemma pairing_genusZero : MapEuler.GenusZero
    (BoundaryRotation.perm (fun c=>(a.paths hzw c).length)) (pairing a hzw hr hz).perm := by
  change MapEuler.GenusZero (BoundaryRotation.perm (fun c=>(a.paths hzw c).length))
    ((coordinates a hzw).symm.permCongr a.fullPartner)
  rw [rotation_conjugate]
  exact MapConjugation.genusZero (coordinates a hzw).symm _ _ (a.closedRotation_genusZero hzw)
/-- Actual finite picture exclusion, conditional only on the still-missing
sharp planar separator for its literal prepared interval graph. This is not
an unconditional topology theorem or a proof of the manuscript's main result. -/
theorem excluded (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep))
    (hd : GraphSample.Diameters rep r) (hsample : r∈ActualPatternEvent.samples rep)
    (oneStep : ∀ S : Finset ((pairing a hzw hr hz).prepared hL hd).P,
      PlanarParameters.K PathSystem.ε ClosedWords.D<S.card →
      Nonempty (RecursiveSeparator.Split
        (PairingClusters.Rel (fun p : Position (fun t=>(((pairing a hzw hr hz).prepared hL hd).paths t).length)=>p.1)
          ((pairing a hzw hr hz).prepared hL hd).comparisons.pairing.partner) S))
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y)) : False :=
  FullPairing.excluded (pairing a hzw hr hz) hL hd hsample
    (system_ordinary a hzw hr hz) (pairing_euler a hzw hr hz) oneStep havoid

end TorsionFreeZeroDivisors.SampleGraph.Picture

end

end OAI
