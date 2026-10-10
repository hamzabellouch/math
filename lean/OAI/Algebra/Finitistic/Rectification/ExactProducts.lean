import Mathlib.Algebra.Exact.Basic

namespace OAI
noncomputable section
namespace LittleFinitistic.RectificationTotal
variable {A B C A' B' C' : Type*} [Zero C] [Zero C']
variable {f : A → B} {g : B → C} {f' : A' → B'} {g' : B' → C'}

/-- Exact pairs remain exact under the concrete binary product of maps. -/
theorem exact_prod (h : Function.Exact f g) (h' : Function.Exact f' g') :
    Function.Exact (Prod.map f f') (Prod.map g g') := by
  rintro ⟨x, x'⟩
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (h x).mp (congrArg Prod.fst hx)
    obtain ⟨y', hy'⟩ := (h' x').mp (congrArg Prod.snd hx)
    exact ⟨(y,y'), Prod.ext hy hy'⟩
  · rintro ⟨⟨y,y'⟩, hy⟩
    rw [← hy]
    exact Prod.ext (h.apply_apply_eq_zero y) (h'.apply_apply_eq_zero y')

/-- Short exactness is also preserved by the concrete binary product. -/
theorem shortExact_prod (h : Function.Exact f g) (h' : Function.Exact f' g')
    (hf : Function.Injective f) (hf' : Function.Injective f')
    (hg : Function.Surjective g) (hg' : Function.Surjective g') :
    Function.Injective (Prod.map f f') ∧
      Function.Exact (Prod.map f f') (Prod.map g g') ∧
      Function.Surjective (Prod.map g g') := by
  refine ⟨?_, exact_prod h h', ?_⟩
  · intro x y hxy
    exact Prod.ext (hf (congrArg Prod.fst hxy)) (hf' (congrArg Prod.snd hxy))
  · rintro ⟨z,z'⟩
    obtain ⟨x,hx⟩ := hg z
    obtain ⟨x',hx'⟩ := hg' z'
    exact ⟨(x,x'),Prod.ext hx hx'⟩

variable {X Y Z X' Y' Z' : Type*} [Zero Z] [Zero Z']
variable (eX : X ≃ X') (eY : Y ≃ Y') (eZ : Z ≃ Z') (eZzero : eZ 0 = 0)
variable {f : X → Y} {g : Y → Z} {f' : X' → Y'} {g' : Y' → Z'}
variable (commF : ∀ x, eY (f x) = f' (eX x))
variable (commG : ∀ y, eZ (g y) = g' (eY y))

include eX eY eZ eZzero commF commG

theorem exact_transport (h : Function.Exact f' g') : Function.Exact f g := by
  intro y
  constructor
  · intro hy
    obtain ⟨x',hx'⟩ := (h (eY y)).mp (by rw [← commG, hy, eZzero])
    refine ⟨eX.symm x', eY.injective ?_⟩
    rw [commF, eX.apply_symm_apply, hx']
  · rintro ⟨x,rfl⟩
    apply eZ.injective
    rw [commG, commF, h.apply_apply_eq_zero, eZzero]

theorem shortExact_transport (hf : Function.Injective f') (h : Function.Exact f' g')
    (hg : Function.Surjective g') :
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g := by
  refine ⟨?_, exact_transport eX eY eZ eZzero commF commG h, ?_⟩
  · intro x y hxy
    apply eX.injective
    apply hf
    rw [← commF, ← commF, hxy]
  · intro z
    obtain ⟨y',hy'⟩ := hg (eZ z)
    refine ⟨eY.symm y',eZ.injective ?_⟩
    rw [commG, eY.apply_symm_apply, hy']
end LittleFinitistic.RectificationTotal

end

end OAI
