import OAI.Geometry.PeriodicTiling.Model
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

namespace OAI

universe uG

namespace PeriodicTilingThree

abbrev Plane := ℤ × ℤ

def planeEquiv : Plane ≃+ Lattice 2 where
  toEquiv := (finTwoArrowEquiv ℤ).symm
  map_add' p q := by
    ext i
    fin_cases i <;> rfl

section AdditiveGroup

variable {G : Type uG} [AddCommGroup G]

theorem tiles_iff_unique_tile {F : Finset G} {A : Set G} :
    Tiles F A ↔ ∀ x : G, ∃! f : ↥F, x - (f : G) ∈ A := by
  constructor
  · intro h x
    obtain ⟨⟨f, a⟩, hx⟩ := h.2 x
    have hfa : x - (f : G) = (a : G) := by
      rw [← hx]
      simp
    refine ⟨f, ?_, ?_⟩
    · change x - (f : G) ∈ A
      rw [hfa]
      exact a.property
    · intro g hg
      have hp : (g, (⟨x - (g : G), hg⟩ : A)) = (f, a) := by
        apply h.1
        change (g : G) + (x - (g : G)) = (f : G) + (a : G)
        simpa [add_comm] using hx.symm
      exact congrArg Prod.fst hp
  · intro h
    constructor
    · rintro ⟨f, a⟩ ⟨g, b⟩ he
      obtain ⟨f₀, _hf₀, huniq⟩ := h ((f : G) + (a : G))
      have hf : (f : G) + (a : G) - (f : G) ∈ A := by
        simp [a.property]
      have hg : (f : G) + (a : G) - (g : G) ∈ A := by
        change (f : G) + (a : G) = (g : G) + (b : G) at he
        rw [he]
        simp [b.property]
      have hfg : f = g := (huniq f hf).trans (huniq g hg).symm
      cases hfg
      have hab : a = b := Subtype.ext (add_left_cancel he)
      exact Prod.ext rfl hab
    · intro x
      obtain ⟨f, hf, _huniq⟩ := h x
      refine ⟨(f, ⟨x - (f : G), hf⟩), ?_⟩
      change (f : G) + (x - (f : G)) = x
      simp

theorem Tiles.tile_nonempty {F : Finset G} {A : Set G} (h : Tiles F A) :
    F.Nonempty := by
  obtain ⟨⟨f, _a⟩, _hx⟩ := h.2 0
  exact ⟨f, f.property⟩

theorem Tiles.complement_nonempty {F : Finset G} {A : Set G} (h : Tiles F A) :
    A.Nonempty := by
  obtain ⟨⟨_f, a⟩, _hx⟩ := h.2 0
  exact ⟨a, a.property⟩

theorem period_zero (A : Set G) : Period A 0 := by
  intro x
  simp

theorem Period.add {A : Set G} {v w : G} (hv : Period A v) (hw : Period A w) :
    Period A (v + w) := by
  intro x
  rw [← add_assoc, hw, hv]

theorem Period.neg {A : Set G} {v : G} (hv : Period A v) : Period A (-v) := by
  intro x
  simpa [sub_eq_add_neg, add_assoc] using (hv (x - v)).symm

def periodSubgroup (A : Set G) : AddSubgroup G where
  carrier := {v | Period A v}
  zero_mem' := period_zero A
  add_mem' := fun hv hw => hv.add hw
  neg_mem' := fun hv => hv.neg

end AdditiveGroup

end PeriodicTilingThree

end OAI
