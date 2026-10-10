import OAI.GroupTheory.Thompson.PLRefinement

namespace OAI

namespace ThompsonNonamenability

def standardSubgroup : Subgroup IntervalHomeomorph where
  carrier := {f | StrictMono f ∧ HasDyadicPLPieces f}
  one_mem' := ⟨fun _ _ h => h, hasDyadicPLPieces_one⟩
  mul_mem' hh hg :=
    ⟨hh.1.comp hg.1, hh.2.mul hg.2 hh.1 hg.1⟩
  inv_mem' hg :=
    ⟨IntervalHomeomorph.strictMono_inv hg.1, hg.2.inv hg.1⟩

namespace F

instance : Group F := inferInstanceAs (Group standardSubgroup)

@[simp] theorem one_apply (x : UnitInterval) : (1 : F) x = x := rfl

@[simp] theorem mul_apply (h g : F) (x : UnitInterval) : (h * g) x = h (g x) := rfl

@[simp] theorem inv_apply_apply (g : F) (x : UnitInterval) : g⁻¹ (g x) = x :=
  IntervalHomeomorph.inv_apply_apply g.toIntervalHomeomorph x

@[simp] theorem apply_inv_apply (g : F) (x : UnitInterval) : g (g⁻¹ x) = x :=
  IntervalHomeomorph.apply_inv_apply g.toIntervalHomeomorph x

def toIntervalHomeomorphHom : F →* IntervalHomeomorph where
  toFun := toIntervalHomeomorph
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toIntervalHomeomorph_injective :
    Function.Injective toIntervalHomeomorph := fun _ _ h => Subtype.ext h

theorem toHomeomorph_injective : Function.Injective toHomeomorph := by
  intro g h heq
  apply ext
  intro x
  exact congrArg (fun f : UnitInterval ≃ₜ UnitInterval => f x) heq

/-- The representation forgets no mathematical data: it is equivalent to the
usual subtype of actual increasing finite dyadic PL interval homeomorphisms. -/
def standardHomeomorphEquiv :
    F ≃ {f : UnitInterval ≃ₜ UnitInterval //
      StrictMono f ∧ HasDyadicPLPieces ⟨f⟩} where
  toFun g := ⟨g.toHomeomorph, g.strictMono, g.hasDyadicPLPieces⟩
  invFun g := ⟨⟨g.val⟩, g.property⟩
  left_inv g := by
    apply F.ext
    intro x
    rfl
  right_inv g := by
    apply Subtype.ext
    rfl

theorem mem_iff_standardPL (f : IntervalHomeomorph) :
    (∃ g : F, g.toIntervalHomeomorph = f) ↔
      StrictMono f ∧ HasDyadicPLPieces f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact g.property
  · intro hf
    exact ⟨⟨f, hf⟩, rfl⟩

end F

end ThompsonNonamenability

end OAI
