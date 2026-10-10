import OAI.GroupTheory.CyclicSeries.Length
import Mathlib.GroupTheory.Index

namespace OAI

/-!
# Polycyclic and virtually polycyclic groups

We use the existing concrete cyclic subnormal series, including normality and
cyclicity of each quotient. Neither polycyclicity nor virtual polycyclicity is
an unspecified property parameter.
-/

namespace PolycyclicRecognition

open ChromaticCyclic

variable (G : Type*) [Group G]

/-- A polycyclic group has a finite subnormal series from the trivial subgroup
to the whole group with cyclic factors. -/
def IsPolycyclic : Prop :=
  ∃ n : ℕ, Nonempty (CyclicSeries (⊥ : Subgroup G) ⊤ n)

/-- A virtually polycyclic group contains a polycyclic subgroup of finite index. -/
def IsVirtuallyPolycyclic : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolycyclic H

variable {G} {H : Type*} [Group H]

/-- The length-zero series proves polycyclicity of the trivial group. -/
theorem isPolycyclic_of_subsingleton [Subsingleton G] : IsPolycyclic G := by
  refine ⟨0, ?_⟩
  have htop : (⊥ : Subgroup G) = ⊤ := Subsingleton.elim _ _
  simpa only [htop] using (⟨CyclicSeries.refl (⊥ : Subgroup G)⟩ :
    Nonempty (CyclicSeries (⊥ : Subgroup G) ⊥ 0))

/-- Polycyclicity descends to a surjective image by mapping a cyclic series. -/
theorem IsPolycyclic.of_surjective (hG : IsPolycyclic G)
    (f : G →* H) (hf : Function.Surjective f) : IsPolycyclic H := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  refine ⟨n, ?_⟩
  have hc := c.map f
  rw [Subgroup.map_bot, Subgroup.map_top_of_surjective f hf] at hc
  exact ⟨hc⟩

/-- Subgroups of polycyclic groups are polycyclic, by pulling back the cyclic series. -/
theorem IsPolycyclic.of_injective (hG : IsPolycyclic G)
    (f : H →* G) (hf : Function.Injective f) : IsPolycyclic H := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  refine ⟨n, ?_⟩
  have hc := c.comap f
  rw [MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff f).mpr hf,
    Subgroup.comap_top] at hc
  exact ⟨hc⟩

/-- This formulation is invariant under group isomorphisms. -/
theorem isPolycyclic_equiv (e : G ≃* H) : IsPolycyclic G ↔ IsPolycyclic H :=
  ⟨fun h => h.of_surjective e.toMonoidHom e.surjective,
    fun h => h.of_surjective e.symm.toMonoidHom e.symm.surjective⟩

/-- A polycyclic group is virtually polycyclic, using the whole group. -/
theorem IsPolycyclic.isVirtuallyPolycyclic (hG : IsPolycyclic G) :
    IsVirtuallyPolycyclic G := by
  refine ⟨⊤, inferInstance, ?_⟩
  exact hG.of_injective (⊤ : Subgroup G).subtype Subtype.val_injective

/-- Every finite group is virtually polycyclic, via its trivial subgroup.
The ambient finite group itself need not be solvable. -/
theorem isVirtuallyPolycyclic_of_finite [Finite G] : IsVirtuallyPolycyclic G :=
  ⟨⊥, inferInstance, isPolycyclic_of_subsingleton⟩

/-- A subgroup of a virtually polycyclic group is virtually polycyclic. -/
theorem IsVirtuallyPolycyclic.of_injective (hG : IsVirtuallyPolycyclic G)
    (f : H →* G) (hf : Function.Injective f) : IsVirtuallyPolycyclic H := by
  obtain ⟨K, hKindex, hKpoly⟩ := hG
  let := hKindex
  let J : Subgroup H := K.comap f
  let g : J →* K :=
    { toFun x := ⟨f x, x.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' x y := Subtype.ext (f.map_mul x y) }
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hxy
  exact ⟨J, inferInstance, hKpoly.of_injective g hg⟩

end PolycyclicRecognition

end OAI
