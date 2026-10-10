import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TrackPoint

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonTrackStabilizer
open Classical Set

namespace PolygonTracks
variable {a k n : ℕ}
noncomputable def join (a k n : ℕ) :
    TrackPoint a k ⊕ TrackPoint a n ≃ TrackPoint a (k+n) :=
  (Equiv.sumProdDistrib (Fin k) (Fin n) (GenericSquare a)).symm.trans
    (Equiv.prodCongr finSumFinEquiv (Equiv.refl _))

@[simp] theorem join_inl (x : TrackPoint a k) : join a k n (.inl x)=(x.1.castAdd n,x.2) := rfl
@[simp] theorem join_inr (x : TrackPoint a n) : join a k n (.inr x)=(x.1.natAdd k,x.2) := rfl
@[simp] theorem join_symm_left (x : TrackPoint a k) :
    (join a k n).symm (x.1.castAdd n,x.2)=.inl x := (join a k n).symm_apply_apply (.inl x)
@[simp] theorem join_symm_right (x : TrackPoint a n) :
    (join a k n).symm (x.1.natAdd k,x.2)=.inr x := (join a k n).symm_apply_apply (.inr x)

noncomputable def blockPerm (k : ℕ) (f : Equiv.Perm (TrackPoint a n)) :
    Equiv.Perm (TrackPoint a (k+n)) :=
  (join a k n).symm.trans (((Equiv.refl _).sumCongr f).trans (join a k n))

@[simp] theorem blockPerm_left (f : Equiv.Perm (TrackPoint a n)) (x : TrackPoint a k) :
    blockPerm k f (x.1.castAdd n,x.2)=(x.1.castAdd n,x.2) := by
  simp [blockPerm]

@[simp] theorem blockPerm_right (f : Equiv.Perm (TrackPoint a n)) (x : TrackPoint a n) :
    blockPerm k f (x.1.natAdd k,x.2)=((f x).1.natAdd k,(f x).2) := by
  simp [blockPerm]

theorem blockPerm_hasTable (f : polygonFullGroup a n) : HasTranslationTable (blockPerm k f.val) := by
  obtain ⟨s,hs,hcover⟩ := f.property
  let leftChart : Fin k → TableChart a (k+n) := fun i => ⟨i.castAdd n,i.castAdd n,0,⊤⟩
  let rightChart : TableChart a n → TableChart a (k+n) := fun c =>
    ⟨c.source.natAdd k,c.target.natAdd k,c.shift,c.domain⟩
  refine ⟨Finset.univ.image leftChart ∪ s.image rightChart,?_,?_⟩
  · intro c hc
    rcases Finset.mem_union.mp hc with hc|hc
    · obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      change blockPerm k f.val (i.castAdd n,x)=(i.castAdd n,translate a 0 x)
      rw [blockPerm_left (x:=(i,x)),translate_zero]
    · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      change blockPerm k f.val (d.source.natAdd k,x)=(d.target.natAdd k,translate a d.shift x)
      rw [blockPerm_right (x:=(d.source,x)),hs d hd x hx]
  · rintro ⟨i,x⟩
    induction i using Fin.addCases with
    | left i =>
      exact ⟨leftChart i,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),rfl,by trivial⟩
    | right i =>
      obtain ⟨c,hc,hx⟩ := hcover (i,x)
      refine ⟨rightChart c,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c,hc,rfl⟩),?_,hx.2⟩
      exact congrArg (Fin.natAdd k) hx.1

noncomputable def stabilize (a k n : ℕ) : polygonFullGroup a n →* polygonFullGroup a (k+n) where
  toFun f := ⟨blockPerm k f.val,blockPerm_hasTable f⟩
  map_one' := by
    apply Subtype.ext; apply Equiv.ext
    intro x
    obtain ⟨y,rfl⟩ := (join a k n).surjective x
    cases y <;> simp [blockPerm]
  map_mul' f g := by
    apply Subtype.ext; apply Equiv.ext
    intro x
    obtain ⟨y,rfl⟩ := (join a k n).surjective x
    cases y <;> simp [blockPerm,Equiv.Perm.mul_apply]

@[simp] theorem stabilize_left (f : polygonFullGroup a n) (x : TrackPoint a k) :
    (stabilize a k n f).val (x.1.castAdd n,x.2)=(x.1.castAdd n,x.2) := blockPerm_left f.val x
@[simp] theorem stabilize_right (f : polygonFullGroup a n) (x : TrackPoint a n) :
    (stabilize a k n f).val (x.1.natAdd k,x.2)=((f.val x).1.natAdd k,(f.val x).2) := blockPerm_right f.val x

theorem stabilize_injective : Function.Injective (stabilize a k n) := by
  intro f g he
  apply Subtype.ext; apply Equiv.ext
  intro x
  have h := congrArg (fun p : polygonFullGroup a (k+n) => p.val (x.1.natAdd k,x.2)) he
  simp only [stabilize_right] at h
  apply Prod.ext
  · apply Fin.ext
    exact Nat.add_left_cancel (congrArg (fun p : TrackPoint a (k+n) => p.1.val) h)
  · exact congrArg (fun p : TrackPoint a (k+n) => p.2) h

def bankFixer (a k n : ℕ) : Subgroup (polygonFullGroup a (k+n)) where
  carrier := {g | ∀x : TrackPoint a k,g.val (x.1.castAdd n,x.2)=(x.1.castAdd n,x.2)}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro f g hf hg x
    change f.val (g.val (x.1.castAdd n,x.2))=_
    rw [hg x,hf x]
  inv_mem' := by
    intro g hg x
    exact g.val.symm_apply_eq.mpr (hg x).symm

@[simp] theorem mem_bankFixer (g : polygonFullGroup a (k+n)) :
    g∈bankFixer a k n ↔ ∀x : TrackPoint a k,g.val (x.1.castAdd n,x.2)=(x.1.castAdd n,x.2) := Iff.rfl

theorem stabilize_mem_bankFixer (g : polygonFullGroup a n) :
    stabilize a k n g∈bankFixer a k n := stabilize_left g

end PolygonTracks
end PolygonTrackStabilizer

section PolygonTrackRestriction
open Classical Set
namespace PolygonTracks
variable {a k n : ℕ}

def rightIncl (a k n : ℕ) (x : TrackPoint a n) : TrackPoint a (k+n) :=
  (x.1.natAdd k,x.2)

theorem rightIncl_injective : Function.Injective (rightIncl a k n) := by
  intro x y he
  apply Prod.ext
  · apply Fin.ext
    exact Nat.add_left_cancel (congrArg (fun p : TrackPoint a (k+n) => p.1.val) he)
  · exact congrArg (fun p : TrackPoint a (k+n) => p.2) he

theorem bankFixer_preserves_right (g : bankFixer a k n) (x : TrackPoint a n) :
    ∃y : TrackPoint a n,g.val.val (rightIncl a k n x)=rightIncl a k n y := by
  obtain ⟨z,hz⟩ := (join a k n).surjective (g.val.val (rightIncl a k n x))
  cases z with
  | inl z =>
    have he : rightIncl a k n x=(z.1.castAdd n,z.2) :=
      g.val.val.injective (hz.symm.trans (g.property z).symm)
    have hf := congrArg (fun p : TrackPoint a (k+n) => p.1.val) he
    have := z.1.isLt
    change k+x.1.val=z.1.val at hf
    omega
  | inr y => exact ⟨y,hz.symm⟩

noncomputable def rightValue (g : bankFixer a k n) (x : TrackPoint a n) : TrackPoint a n :=
  (bankFixer_preserves_right g x).choose

@[simp] theorem rightValue_spec (g : bankFixer a k n) (x : TrackPoint a n) :
    rightIncl a k n (rightValue g x)=g.val.val (rightIncl a k n x) :=
  (bankFixer_preserves_right g x).choose_spec.symm

noncomputable def restrictPerm (g : bankFixer a k n) : Equiv.Perm (TrackPoint a n) where
  toFun := rightValue g
  invFun := rightValue g⁻¹
  left_inv x := by
    apply rightIncl_injective (a:=a) (k:=k)
    rw [rightValue_spec,rightValue_spec]
    exact g.val.val.symm_apply_apply _
  right_inv x := by
    apply rightIncl_injective (a:=a) (k:=k)
    rw [rightValue_spec,rightValue_spec]
    exact g.val.val.apply_symm_apply _

@[simp] theorem restrictPerm_spec (g : bankFixer a k n) (x : TrackPoint a n) :
    rightIncl a k n (restrictPerm g x)=g.val.val (rightIncl a k n x) := rightValue_spec g x

theorem restrictPerm_hasTable (g : bankFixer a k n) : HasTranslationTable (restrictPerm g) := by
  obtain ⟨s,hs,hcover⟩ := g.val.property
  let admissible : Fin n × Fin n × TableChart a (k+n) → Prop := fun t =>
    t.2.2.source=t.1.natAdd k ∧ t.2.2.target=t.2.1.natAdd k
  let conv : Fin n × Fin n × TableChart a (k+n) → TableChart a n := fun t =>
    ⟨t.1,t.2.1,t.2.2.shift,t.2.2.domain⟩
  let ts := ((Finset.univ : Finset (Fin n)).product ((Finset.univ : Finset (Fin n)).product s)).filter admissible
  refine ⟨ts.image conv,?_,?_⟩
  · intro c hc
    obtain ⟨⟨i,j,d⟩,hd,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hmem,hsource,htarget⟩ := Finset.mem_filter.mp hd
    have hdmem : d∈s := (Finset.mem_product.mp (Finset.mem_product.mp hmem).2).2
    intro x hx
    apply rightIncl_injective (a:=a) (k:=k)
    rw [restrictPerm_spec]
    change g.val.val (i.natAdd k,x)=(j.natAdd k,translate a d.shift x)
    change d.source=i.natAdd k at hsource
    change d.target=j.natAdd k at htarget
    rw [← hsource,← htarget]
    exact hs d hdmem x hx
  · intro x
    obtain ⟨d,hd,hsource,hx⟩ := hcover (rightIncl a k n x)
    have he := hs d hd x.2 hx
    have htarget : d.target=(restrictPerm g x).1.natAdd k := by
      have hp := congrArg Prod.fst (restrictPerm_spec g x)
      change x.1.natAdd k=d.source at hsource
      rw [← hsource] at he
      exact (congrArg Prod.fst he).symm.trans hp.symm
    refine ⟨conv (x.1,(restrictPerm g x).1,d),Finset.mem_image.mpr ⟨_,?_,rfl⟩,rfl,hx⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_product.mpr ⟨Finset.mem_univ _,hd⟩⟩,hsource.symm,htarget⟩

noncomputable def restrict (g : bankFixer a k n) : polygonFullGroup a n :=
  ⟨restrictPerm g,restrictPerm_hasTable g⟩

@[simp] theorem stabilize_restrict (g : bankFixer a k n) : stabilize a k n (restrict g)=g.val := by
  apply Subtype.ext; apply Equiv.ext
  intro x
  obtain ⟨z,rfl⟩ := (join a k n).surjective x
  cases z with
  | inl y => exact (stabilize_left _ y).trans (g.property y).symm
  | inr y => exact (stabilize_right _ y).trans (restrictPerm_spec g y)

@[simp] theorem restrict_stabilize (g : polygonFullGroup a n) :
    restrict ⟨stabilize a k n g,stabilize_mem_bankFixer g⟩=g := by
  apply stabilize_injective (k:=k)
  exact stabilize_restrict _

noncomputable def stabilizerEquiv (a k n : ℕ) : polygonFullGroup a n ≃* bankFixer a k n where
  toFun g := ⟨stabilize a k n g,stabilize_mem_bankFixer g⟩
  invFun := restrict
  left_inv := restrict_stabilize
  right_inv g := Subtype.ext (stabilize_restrict g)
  map_mul' g h := Subtype.ext ((stabilize a k n).map_mul g h)

end PolygonTracks
end PolygonTrackRestriction

end SimpleAmenable
end
end

end OAI
