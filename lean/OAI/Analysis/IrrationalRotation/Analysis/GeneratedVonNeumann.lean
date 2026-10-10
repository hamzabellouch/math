import OAI.Analysis.IrrationalRotation.Model.GeneratedVonNeumann

namespace OAI

open scoped Pointwise

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

@[simp]
theorem coe_vonNeumannGenerated (s : Set (H →L[ℂ] H)) :
    (vonNeumannGenerated s : Set (H →L[ℂ] H)) =
      (s ∪ star s).centralizer.centralizer := by
  exact StarSubalgebra.coe_centralizer_centralizer ℂ s

theorem subset_vonNeumannGenerated (s : Set (H →L[ℂ] H)) :
    s ⊆ vonNeumannGenerated s := by
  rw [coe_vonNeumannGenerated]
  exact Set.Subset.trans Set.subset_union_left Set.subset_centralizer_centralizer

theorem vonNeumannGenerated_le (s : Set (H →L[ℂ] H)) (M : VonNeumannAlgebra H)
    (hs : s ⊆ M) : vonNeumannGenerated s ≤ M := by
  change (vonNeumannGenerated s : Set (H →L[ℂ] H)) ⊆ M
  rw [coe_vonNeumannGenerated, ← M.centralizer_centralizer]
  apply Set.centralizer_subset
  apply Set.centralizer_subset
  intro T hT
  rcases hT with hT | hT
  · exact hs hT
  · have hstar : star T ∈ s := hT
    simpa using (star_mem (hs hstar) : star (star T) ∈ M)

theorem vonNeumannGenerated_le_iff (s : Set (H →L[ℂ] H)) (M : VonNeumannAlgebra H) :
    vonNeumannGenerated s ≤ M ↔ s ⊆ M := by
  exact ⟨fun h => Set.Subset.trans (subset_vonNeumannGenerated s) h,
    vonNeumannGenerated_le s M⟩

theorem vonNeumannGenerated_mono {s t : Set (H →L[ℂ] H)} (hst : s ⊆ t) :
    vonNeumannGenerated s ≤ vonNeumannGenerated t :=
  vonNeumannGenerated_le s _ (hst.trans (subset_vonNeumannGenerated t))

@[simp]
theorem vonNeumannGenerated_coe (M : VonNeumannAlgebra H) :
    vonNeumannGenerated (M : Set (H →L[ℂ] H)) = M := by
  apply le_antisymm
  · exact vonNeumannGenerated_le _ _ (Set.Subset.refl _)
  · exact subset_vonNeumannGenerated _

@[simp]
theorem coe_commutant_vonNeumannGenerated (s : Set (H →L[ℂ] H)) :
    ((vonNeumannGenerated s).commutant : Set (H →L[ℂ] H)) =
      (s ∪ star s).centralizer := by
  rw [VonNeumannAlgebra.coe_commutant, coe_vonNeumannGenerated,
    Set.centralizer_centralizer_centralizer]

theorem mem_commutant_vonNeumannGenerated_iff (s : Set (H →L[ℂ] H))
    (T : H →L[ℂ] H) :
    T ∈ (vonNeumannGenerated s).commutant ↔
      ∀ A ∈ s, A * T = T * A ∧ star A * T = T * star A := by
  change T ∈ ((vonNeumannGenerated s).commutant : Set (H →L[ℂ] H)) ↔ _
  rw [coe_commutant_vonNeumannGenerated]
  exact StarSubalgebra.mem_centralizer_iff ℂ

end Invariant233

end OAI
