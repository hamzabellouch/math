import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PolyZDuality

namespace OAI

/-! # A proved duality comparison for virtually polycyclic groups

The polycyclic comparison group's duality follows from a finite-index poly-Z
series and the cyclic-extension resolution. The recognition consequence is
conditional on the four finiteness and transfer inputs.
-/

namespace PolycyclicRecognition

theorem exists_coarse_poincareDuality_comparison_proved
    (P H : Type) [Group P] [Group H] [Group.FG P]
    (hP : IsVirtuallyPolycyclic P) (e : GroupCoarseEquivalence P H) :
    ∃ (K : Subgroup P) (Γ : Subgroup K),
      K.FiniteIndex ∧ Γ.FiniteIndex ∧ Group.FG Γ ∧
      Nonempty (GroupCoarseEquivalence Γ H) ∧
      ∃ n : ℕ, IsIntegralPoincareDualityGroup Γ n := by
  obtain ⟨K, hKindex, hKpoly⟩ := hP
  let := hKindex
  obtain ⟨Γ, hΓindex, n, hΓPD⟩ := hKpoly.exists_poincareDuality_finiteIndex
  let := hΓindex
  exact ⟨K, Γ, hKindex, hΓindex, inferInstance,
    ⟨(finiteIndexCoarseEquivalence Γ).trans ((finiteIndexCoarseEquivalence K).trans e)⟩,
    n, hΓPD⟩

theorem virtuallyPolycyclic_of_elementaryAmenable_coarse_virtualPolycyclic_proved
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    (P H : Type) [Group P] [Group H] [Group.FG P] [Group.FG H]
    (hP : IsVirtuallyPolycyclic P) (e : GroupCoarseEquivalence P H)
    (hEA : IsElementaryAmenable H) : IsVirtuallyPolycyclic H := by
  obtain ⟨K, Γ, _, _, hfg, ⟨eΓ⟩, n, hΓPD⟩ :=
    exists_coarse_poincareDuality_comparison_proved P H hP e
  let := hfg
  exact virtuallyPolycyclic_of_elementaryAmenable_coarse_PD liFP eaFP liPD bieri Γ H eΓ hEA n hΓPD

end PolycyclicRecognition

end OAI
