import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonMatchingLaw

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SubgroupTestReiter
open Classical Set

noncomputable def subgroupOrbitSetoid {G : Type*} [Group G] (H : Subgroup G) : Setoid G where
  r x y := ∃h : H,(h:G)*x=y
  iseqv := ⟨fun x => ⟨1,by simp⟩,by
    rintro x y ⟨h,hh⟩
    refine ⟨h⁻¹,?_⟩
    rw [←hh]
    simp,by
    rintro x y z ⟨h,hh⟩ ⟨k,hk⟩
    refine ⟨k*h,?_⟩
    change (k:G)*(h:G)*x=z
    rw [mul_assoc,hh,hk]⟩

noncomputable def subgroupOrbitBase {G : Type*} [Group G] (H : Subgroup G) (x : G) : G :=
  (Quotient.mk (subgroupOrbitSetoid H) x).out

theorem subgroupOrbitBase_spec {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    ∃h : H,(h:G)*subgroupOrbitBase H x=x :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (subgroupOrbitSetoid H) x))

noncomputable def subgroupCoordinate {G : Type*} [Group G] (H : Subgroup G) (x : G) : H :=
  (subgroupOrbitBase_spec H x).choose

theorem subgroupCoordinate_spec {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    (subgroupCoordinate H x:G)*subgroupOrbitBase H x=x := (subgroupOrbitBase_spec H x).choose_spec

theorem subgroupCoordinate_mul {G : Type*} [Group G] (H : Subgroup G) (k : H) (x : G) :
    subgroupCoordinate H ((k:G)*x)=k*subgroupCoordinate H x := by
  have hb : subgroupOrbitBase H x=subgroupOrbitBase H ((k:G)*x) :=
    congrArg Quotient.out (Quotient.sound (s:=subgroupOrbitSetoid H) ⟨k,rfl⟩)
  apply Subtype.ext
  apply mul_right_cancel (b:=subgroupOrbitBase H ((k:G)*x))
  rw [subgroupCoordinate_spec]
  change (k:G)*x=((k:G)*(subgroupCoordinate H x:G))*subgroupOrbitBase H ((k:G)*x)
  rw [←hb,mul_assoc,subgroupCoordinate_spec]

theorem finite_weights_push {X Y : Type*} (S : Finset X) (p : X → ℝ) (π : X → Y)
    (hp : ∀x,0 ≤ p x) (hm : (∑x∈S,p x)=1) :
    ∃(T : Finset Y) (q : Y → ℝ),(∀y,0 ≤ q y) ∧ (∀y∉T,q y=0) ∧ (∑y∈T,q y)=1 ∧
      ∀f : Y → ℝ,(∑y∈T,q y*f y)=∑x∈S,p x*f (π x) := by
  obtain ⟨T,q,hq,hs,ht,havg⟩ := finite_uniform_mixture S p (fun x => {π x})
    (fun x _ => hp x) hm (fun _ _ => Finset.singleton_nonempty _)
  refine ⟨T,q,hq,hs,ht,?_⟩
  intro f
  simpa using havg f

theorem FiniteTestReiter.subgroup {G : Type*} [Group G] (h : FiniteTestReiter G)
    (H : Subgroup G) : FiniteTestReiter H := by
  intro K ε hε
  obtain ⟨S,p,hp,hs,hm,ht⟩ := h (K.image (fun k : H => (k:G))) ε hε
  obtain ⟨T,q,hq,hT,hM,havg⟩ := finite_weights_push S p (subgroupCoordinate H) hp hm
  refine ⟨T,q,hq,hT,hM,?_⟩
  intro k hk f hf
  rw [havg,havg]
  have hh := ht (k:G) (Finset.mem_image_of_mem (fun k : H => (k:G)) hk)
    (fun x => f (subgroupCoordinate H x)) (fun x => hf (subgroupCoordinate H x))
  simpa only [subgroupCoordinate_mul] using hh

end SubgroupTestReiter

section PolygonAmenability

theorem polygonFullGroup_folner {a m : ℕ} (ha : 0 < a) :
    FolnerAmenable (polygonFullGroup a m) :=
  folner_of_finite_reiter (finiteSupportReiter_of_finiteTestReiter (polygonFullGroup_finiteTestReiter ha))

theorem polygonAlternatingGroup_folner {a m : ℕ} (ha : 0 < a) :
    FolnerAmenable (polygonAlternatingGroup a m) :=
  folner_of_finite_reiter (finiteSupportReiter_of_finiteTestReiter
    ((polygonFullGroup_finiteTestReiter ha).subgroup (polygonAlternatingGroup a m)))

theorem polygon_infinite_simple_folner {a m : ℕ} (ha : 0 < a) (hm : 15 ≤ m) :
    Infinite (polygonAlternatingGroup a m) ∧ IsSimpleGroup (polygonAlternatingGroup a m) ∧
    FolnerAmenable (polygonAlternatingGroup a m) :=
  ⟨polygonAlternatingGroup_infinite a m (by omega),polygonAlternatingGroup_simple a m hm,
    polygonAlternatingGroup_folner ha⟩

end PolygonAmenability

end SimpleAmenable
end
end

end OAI
