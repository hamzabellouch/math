import Mathlib

namespace OAI

noncomputable section

namespace Problem340

theorem coverEntropy_image_of_uniformInducing
    {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    {f : X → X} {g : Y → Y} {e : X → Y}
    (h : Function.Semiconj e f g) (he : IsUniformInducing e) (s : Set X) :
    Dynamics.coverEntropy g (e '' s) = Dynamics.coverEntropy f s := by
  rw [Dynamics.coverEntropy_image_of_comap _ h s, he.comap_uniformSpace]

theorem coverEntropy_range_of_section
    {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    {f : X → X} {g : Y → Y} {e : X → Y} {p : Y → X}
    (h : Function.Semiconj e f g)
    (he : UniformContinuous e) (hp : UniformContinuous p)
    (hpe : Function.LeftInverse p e) :
    Dynamics.coverEntropy g (Set.range e) =
      Dynamics.coverEntropy f (Set.univ : Set X) := by
  have hcomp : p ∘ e = id := funext hpe
  have hi : IsUniformInducing e :=
    IsUniformInducing.of_comp he hp (by rw [hcomp]; exact IsUniformInducing.id)
  simpa only [Set.image_univ] using coverEntropy_image_of_uniformInducing h hi Set.univ

theorem coverEntropy_fixed_snd
    {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    (f : X → X) (g : X × Y → X × Y) (y : Y)
    (h : ∀ x, g (x, y) = (f x, y)) :
    Dynamics.coverEntropy g {z : X × Y | z.2 = y} =
      Dynamics.coverEntropy f (Set.univ : Set X) := by
  have hrange : Set.range (fun x : X => (x, y)) = {z : X × Y | z.2 = y} := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      rfl
    · intro hz
      exact ⟨z.1, Prod.ext rfl hz.symm⟩
  rw [← hrange]
  exact coverEntropy_range_of_section (fun x => (h x).symm)
    (uniformContinuous_id.prodMk uniformContinuous_const) uniformContinuous_fst
    (fun _ => rfl)

theorem coverEntropy_fixed_fst
    {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    (f : Y → Y) (g : X × Y → X × Y) (x : X)
    (h : ∀ y, g (x, y) = (x, f y)) :
    Dynamics.coverEntropy g {z : X × Y | z.1 = x} =
      Dynamics.coverEntropy f (Set.univ : Set Y) := by
  have hrange : Set.range (fun y : Y => (x, y)) = {z : X × Y | z.1 = x} := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      rfl
    · intro hz
      exact ⟨z.2, Prod.ext hz.symm rfl⟩
  rw [← hrange]
  exact coverEntropy_range_of_section (fun y => (h y).symm)
    (uniformContinuous_const.prodMk uniformContinuous_id) uniformContinuous_snd
    (fun _ => rfl)

theorem coverEntropy_fixed_clock_main
    {X Y Z : Type*} [UniformSpace X] [UniformSpace Y] [UniformSpace Z]
    (f : Z → Z) (g : X × (Y × Z) → X × (Y × Z)) (x : X) (y : Y)
    (h : ∀ z, g (x, y, z) = (x, y, f z)) :
    Dynamics.coverEntropy g {p : X × (Y × Z) | p.1 = x ∧ p.2.1 = y} =
      Dynamics.coverEntropy f (Set.univ : Set Z) := by
  have hrange : Set.range (fun z : Z => (x, y, z)) =
      {p : X × (Y × Z) | p.1 = x ∧ p.2.1 = y} := by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨hx, hy⟩
      exact ⟨p.2.2, Prod.ext hx.symm (Prod.ext hy.symm rfl)⟩
  rw [← hrange]
  exact coverEntropy_range_of_section (fun z => (h z).symm)
    (uniformContinuous_const.prodMk
      (uniformContinuous_const.prodMk uniformContinuous_id))
    (uniformContinuous_snd.comp uniformContinuous_snd) (fun _ => rfl)

end Problem340

end

end OAI
