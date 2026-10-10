import OAI.GroupTheory.PolycyclicRecognition.Algebra.Polycyclic

namespace OAI

/-!
# Cyclic factors and extensions of polycyclic groups

These are elementary consequences of concrete cyclic subnormal series. They
are used in the nilpotent branch of the recognition argument.
-/

namespace PolycyclicRecognition

open ChromaticCyclic

variable {G : Type*} [Group G]

/-- A cyclic group has a one-step cyclic series. -/
theorem isPolycyclic_of_isCyclic [IsCyclic G] : IsPolycyclic G := by
  have : IsCyclic (⊤ : Subgroup G) :=
    isCyclic_of_injective (⊤ : Subgroup G).subtype Subtype.val_injective
  exact ⟨1, ⟨CyclicSeries.cons (CyclicStep.bot ⊤) (CyclicSeries.refl ⊤)⟩⟩

/-- Polycyclic groups are closed under group extensions, by concatenating the
series in the kernel with the lifted series in the quotient. -/
theorem isPolycyclic_of_normal_subgroup (N : Subgroup G) [N.Normal]
    (hN : IsPolycyclic N) (hQ : IsPolycyclic (G ⧸ N)) : IsPolycyclic G := by
  obtain ⟨n, ⟨c⟩⟩ := hN
  obtain ⟨m, ⟨d⟩⟩ := hQ
  have cG := c.map N.subtype
  rw [Subgroup.map_bot, ← MonoidHom.range_eq_map, N.range_subtype] at cG
  have dG := d.comap (QuotientGroup.mk' N)
  rw [MonoidHom.comap_bot, QuotientGroup.ker_mk', Subgroup.comap_top] at dG
  exact ⟨n + m, ⟨cG.append dG⟩⟩

end PolycyclicRecognition

end OAI
