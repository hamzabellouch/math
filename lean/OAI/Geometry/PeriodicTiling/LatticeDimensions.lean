import OAI.Geometry.PeriodicTiling.TilingBasic

namespace OAI

namespace PeriodicTilingThree

def intEquiv : ℤ ≃+ Lattice 1 where
  toFun z := fun _ => z
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  map_add' _ _ := rfl

theorem fullyPeriodic_lattice_zero (A : Set (Lattice 0)) : FullyPeriodic A := by
  refine ⟨⊤, inferInstance, ?_⟩
  intro v _hv x
  have hx : x + v = x := Subsingleton.elim _ _
  rw [hx]

theorem lattice_zero_tile_has_fullyPeriodic_complement
    (F : Finset (Lattice 0)) (h : ∃ A, Tiles F A) :
    ∃ A, Tiles F A ∧ FullyPeriodic A := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, hA, fullyPeriodic_lattice_zero A⟩

end PeriodicTilingThree

end OAI
