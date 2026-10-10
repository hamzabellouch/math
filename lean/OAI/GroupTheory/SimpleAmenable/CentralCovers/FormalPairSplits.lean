import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalCoordinates
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalStarTables

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FormalPairSplits
variable {α ι H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

def starPair (F : Option ι → TrackStar α →* H) (i j : ι) :
    Option Bool → TrackStar α →* H
  | none => F none
  | some false => F (some i)
  | some true => F (some j)

variable (F : Option ι → TrackStar α →* H)
    (T : ∀ i j, FormalStarTable (starPair F i j))

noncomputable def formalPairSplit (i : ι) (j : Option ι) (b : Bool) : TrackStar α →* H :=
  (T i (j.getD i)).sector
    ((match j with | none => Set.univ | some _ => {σ | σ true=true}) ∩ {σ | σ false=b})

noncomputable def formalPairContainer (i : ι) (b : Bool) : TrackStar α →* H :=
  (T i i).sector {σ | σ false=b}

theorem formalPair_container_shared (i j : ι) (b : Bool) :
    formalPairContainer F T i b=(T i j).sector {σ | σ false=b} := by
  cases b with
  | true =>
    exact ((T i i).sector_input (some false)).trans
      ((T i j).sector_input (some false)).symm
  | false =>
    ext s
    have hd : Disjoint {σ : Bool → Bool | σ false=true} {σ | σ false=false} := by
      apply Set.disjoint_left.mpr; intro σ ht hf
      exact Bool.false_ne_true (hf.symm.trans ht)
    have he : ({σ : Bool → Bool | σ false=true} ∪ {σ | σ false=false})=Set.univ := by
      ext σ; simp only [Set.mem_union,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
      cases σ false <;> simp
    have hi := (T i i).sector_union hd s
    have hj := (T i j).sector_union hd s
    rw [he,(T i i).sector_input none,(T i i).sector_input (some false)] at hi
    rw [he,(T i j).sector_input none,(T i j).sector_input (some false)] at hj
    change (T i i).sector _ s=(T i j).sector _ s
    exact mul_left_cancel (hi.symm.trans hj)

theorem formalPair_split (i : ι) (j : Option ι) (s : TrackStar α) :
    F j s=formalPairSplit F T i j true s*formalPairSplit F T i j false s := by
  classical
  let U : Set (Bool → Bool) := match j with | none => Set.univ | some _ => {σ | σ true=true}
  have hd : Disjoint (U ∩ {σ | σ false=true}) (U ∩ {σ | σ false=false}) := by
    apply Set.disjoint_left.mpr; intro σ ht hf
    exact Bool.false_ne_true (hf.2.symm.trans ht.2)
  have he : (U ∩ {σ | σ false=true}) ∪ (U ∩ {σ | σ false=false})=U := by
    ext σ
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_ofPred_eq]
    cases σ false <;> simp
  have hh := (T i (j.getD i)).sector_union hd s
  rw [he] at hh
  have hi : (T i (j.getD i)).sector U=F j := by
    cases j with
    | none => exact (T i i).sector_input none
    | some j => exact (T i j).sector_input (some true)
  rw [hi] at hh
  exact hh

theorem formalPair_split_whole (i : ι) : formalPairSplit F T i none true=F (some i) := by
  change (T i i).sector (Set.univ ∩ _)=_
  rw [Set.univ_inter]
  exact (T i i).sector_input (some false)

theorem formalPair_mem (i : ι) (j : Option ι) (b : Bool) (s : TrackStar α) :
    formalPairSplit F T i j b s ∈ (copyFamilyEval F).range := by
  have hh := (T i (j.getD i)).sector_mem
    ((match j with | none => Set.univ | some _ => {σ | σ true=true}) ∩ {σ | σ false=b}) s
  apply Set.mem_of_subset_of_mem (show (copyFamilyEval (starPair F i (j.getD i))).range ≤ _ from ?_) hh
  rw [copyFamilyEval_range,copyFamilyEval_range]
  apply iSup_le
  intro k
  cases k with
  | none => exact le_iSup (fun j => (F j).range) none
  | some b => cases b <;> exact le_iSup (fun j => (F j).range) _

theorem formalPair_supported (L : Finset α → Subgroup H)
    (hF : ∀ j, SmallSupported L (F j)) (i : ι) (j : Option ι) (b : Bool) :
    SmallSupported L (formalPairSplit F T i j b) := by
  apply FormalStarTable.sector_supported
  intro k
  cases k with
  | none => exact hF none
  | some b => cases b <;> exact hF _

theorem formalPair_container_supported (L : Finset α → Subgroup H)
    (hF : ∀ j, SmallSupported L (F j)) (i : ι) (b : Bool) :
    SmallSupported L (formalPairContainer F T i b) := by
  apply FormalStarTable.sector_supported
  intro k
  cases k with
  | none => exact hF none
  | some b => cases b <;> exact hF _

theorem formalPair_control (c : alternatingGroup α →* H)
    (hc : F none=c.comp (universalProjection (alternatingGroup α)))
    (i : ι) (j : Option ι) (b : Bool) :
    SmallControlled c (formalPairSplit F T i j b) (formalPairContainer F T i b) := by
  rw [formalPair_container_shared F T i (j.getD i)]
  have hh := (T i (j.getD i)).sector_control
    (show ((match j with | none => Set.univ | some _ => {σ | σ true=true}) ∩
      {σ | σ false=b}) ⊆ {σ | σ false=b} from Set.inter_subset_right)
  intro I s x hx
  have he := hh (universalMap (subtypeAlternatingHom I.val) s) x hx
  change _=(F none (universalMap (subtypeAlternatingHom I.val) s))*x*
    (F none (universalMap (subtypeAlternatingHom I.val) s))⁻¹ at he
  simpa only [hc,MonoidHom.comp_apply] using he

theorem formalPair_containers_commute (i : ι) (s t : TrackStar α) :
    Commute (formalPairContainer F T i true s) (formalPairContainer F T i false t) := by
  apply FormalStarTable.sector_commute
  apply Set.disjoint_left.mpr
  intro σ ht hf
  exact Bool.false_ne_true (hf.symm.trans ht)

end FormalPairSplits

section FormalPairAssembly
variable {α ι H : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem formal_pairs_assemble (hα : 20 ≤ Fintype.card α)
    (L : Finset α → Subgroup H) (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (F : Option ι → TrackStar α →* H) (hF : ∀ j, SmallSupported L (F j))
    (h0 : F none=c.comp (universalProjection (alternatingGroup α)))
    (T : ∀ i j, FormalStarTable (starPair F i j)) : Nonempty (FormalStarTable F) := by
  let K := (copyFamilyEval F).range
  have hm (i : Option ι) (s : TrackStar α) : F i s ∈ K :=
    ⟨FreeGroup.of (i,s),copyFamilyEval_of F i s⟩
  let F' := fun i => (F i).codRestrict K (hm i)
  let : Group.IsPerfect K := copyFamilyEval_perfect F
  have hcm (s : alternatingGroup α) : c s ∈ K := by
    obtain ⟨t,rfl⟩ := universalProjection_surjective (alternatingGroup α) s
    rw [← MonoidHom.comp_apply,← h0]
    exact hm none t
  let c' := c.codRestrict K hcm
  have h0' : F' none=c'.comp (universalProjection (alternatingGroup α)) := by
    ext s
    exact DFunLike.congr_fun h0 s
  let Fl := fun i j => (formalPairSplit F T i j true).codRestrict K (formalPair_mem F T i j true)
  let Fr := fun i j => (formalPairSplit F T i j false).codRestrict K (formalPair_mem F T i j false)
  obtain ⟨φ,hφ,hφc,hφi⟩ := star_split_assignment
    (universalProjection (alternatingGroup α)) (universalProjection_surjective _) c' F' h0'
    (codRestrict_iSup_top F K hm (copyFamilyEval_range F).symm) Fl Fr
    (fun i j s => Subtype.ext (formalPair_split F T i j s))
    (fun i j k s t => by
      apply Subtype.ext
      exact (small_control_disjoint L c hc hd hα _ _ _ _
        (formalPair_supported F T L hF i j true)
        (formalPair_supported F T L hF i k false)
        (formalPair_container_supported F T L hF i true)
        (formalPair_control F T c h0 i j true)
        (formalPair_control F T c h0 i k false)
        (formalPair_containers_commute F T i) s t).eq)
    (fun i => by ext s; exact DFunLike.congr_fun (formalPair_split_whole F T i) s)
  refine ⟨⟨K,rfl,F',(fun _ => rfl),φ,hφ,?_⟩⟩
  intro i
  cases i with
  | none =>
    change φ.comp ((sectorMask Set.univ).comp _)=_
    rw [← MonoidHom.comp_assoc,hφc,MonoidHom.comp_assoc,← h0']
  | some i => exact hφi i

end FormalPairAssembly

end SimpleAmenable
end
end

end OAI
