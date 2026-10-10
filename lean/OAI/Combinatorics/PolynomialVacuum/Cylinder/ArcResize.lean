import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcSeparation
import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcBoundaryValues
import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcMajorant

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M H J K : ℕ} [NeZero M]
namespace BoundaryArc
noncomputable def archOfShort (A : BoundaryArc (bandSites M H)) (h : A.word.length<H) :
    PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M := (A.shape_arch_of_length_lt h).choose
@[simp] theorem archOfShort_shape (A : BoundaryArc (bandSites M H)) (h : A.word.length<H) :
    A.shape=.inl (A.archOfShort h) := (A.shape_arch_of_length_lt h).choose_spec
@[simp] theorem archOfShort_word (A : BoundaryArc (bandSites M H)) (h : A.word.length<H) :
    (A.archOfShort h).val.word=A.word := by
  have hh:=A.shape_word
  rw [A.archOfShort_shape h] at hh
  exact hh

def Short (K : ℕ) (A : BoundaryArc (bandSites M H)) : Prop := A.word.length≤K
noncomputable def resize (hH : K<H) (hJ : K<J) (A : {A : BoundaryArc (bandSites M H) // A.Short K}) :
    BoundaryArc (bandSites M J) :=
  atPort (A.val.archOfShort (lt_of_le_of_lt A.property hH))
    (by have hh:=(A.val.archOfShort (lt_of_le_of_lt A.property hH)).val.height_le_length
        rw [archOfShort_word] at hh; exact hh.trans (A.property.trans hJ.le)) A.val.port
@[simp] theorem resize_port (hH : K<H) (hJ : K<J) (A : {A : BoundaryArc (bandSites M H) // A.Short K}) :
    (resize hH hJ A).port=A.val.port := by simp [resize]
@[simp] theorem resize_shape (hH : K<H) (hJ : K<J) (A : {A : BoundaryArc (bandSites M H) // A.Short K}) :
    (resize hH hJ A).shape=A.val.shape := by simp [resize,← A.val.archOfShort_shape (lt_of_le_of_lt A.property hH)]
@[simp] theorem resize_word (hH : K<H) (hJ : K<J) (A : {A : BoundaryArc (bandSites M H) // A.Short K}) :
    (resize hH hJ A).word=A.val.word := by simp [resize]

theorem resize_injective (hH : K<H) (hJ : K<J) : Function.Injective (resize (M:=M) hH hJ) := by
  intro A B he
  apply Subtype.ext
  apply A.val.eq_of_port_shape B.val
  · simpa only [resize_port] using congrArg port he
  · simpa only [resize_shape] using congrArg shape he

theorem resize_weight (hH : K<H) (hJ : K<J) (A : {A : BoundaryArc (bandSites M H) // A.Short K}) :
    (resize hH hJ A).weight=A.val.weight := by
  let B:=A.val.archOfShort (lt_of_le_of_lt A.property hH)
  have hl : B.val.height≤H := by
    have hh:=B.val.height_le_length
    simp only [B,archOfShort_word] at hh
    exact hh.trans (A.property.trans hH.le)
  have he:=eq_atPort_of_shape A.val B (A.val.archOfShort_shape _) hl
  change (atPort B _ A.val.port).weight=A.val.weight
  rw [atPort_weight B hl,← he]

theorem resize_boundary (hH : K<H) (hJ : K<J) (A : {A : BoundaryArc (bandSites M H) // A.Short K})
    (i : ZMod M) :
    (resize hH hJ A).current ((i,0),0)=A.val.current ((i,0),0) ∧
    (resize hH hJ A).current ((i,(J : ℤ)),0)=A.val.current ((i,(H : ℤ)),0) := by
  let B:=A.val.archOfShort (lt_of_le_of_lt A.property hH)
  have hl : B.val.height≤H := by
    have hh:=B.val.height_le_length
    simp only [B,archOfShort_word] at hh
    exact hh.trans (A.property.trans hH.le)
  have he:=eq_atPort_of_shape A.val B (A.val.archOfShort_shape _) hl
  change (atPort B _ A.val.port).current _=_ ∧ (atPort B _ A.val.port).current _=_
  conv_rhs => rw [he]
  constructor
  · rw [atPort_bottom_current,he,atPort_bottom_current,atPort_port]
  · rw [atPort_top_current,atPort_top_current,atPort_port]

theorem resize_disjoint (hH : K<H) (hJ : K<J) (hH' : 2*K≤H) (hJ' : 2*K≤J)
    (A B : {A : BoundaryArc (bandSites M H) // A.Short K}) :
    Disjoint (resize hH hJ A).vertices (resize hH hJ B).vertices ↔ Disjoint A.val.vertices B.val.vertices := by
  let a:=A.val.archOfShort (lt_of_le_of_lt A.property hH)
  let b:=B.val.archOfShort (lt_of_le_of_lt B.property hH)
  have ha : a.val.height≤H := by
    have hh:=a.val.height_le_length; simp only [a,archOfShort_word] at hh
    exact hh.trans (A.property.trans hH.le)
  have hb : b.val.height≤H := by
    have hh:=b.val.height_le_length; simp only [b,archOfShort_word] at hh
    exact hh.trans (B.property.trans hH.le)
  have hsum : a.val.word.length+b.val.word.length≤2*K := by
    simp only [a,b,archOfShort_word]; have := A.property; have := B.property
    change A.val.word.length≤K at ‹A.val.Short K›
    dsimp [Short] at *; omega
  change Disjoint (atPort a _ A.val.port).vertices (atPort b _ B.val.port).vertices ↔ _
  rw [atPort_disjoint_stable a b ha hb _ _ _ _ (hsum.trans hH') (hsum.trans hJ'),
    ← eq_atPort_of_shape A.val a (A.val.archOfShort_shape _) ha,
    ← eq_atPort_of_shape B.val b (B.val.archOfShort_shape _) hb]
end BoundaryArc
end PolynomialVacuumCylinder

end OAI
