import OAI.Analysis.KadisonKastler.SimultaneousRowFamily

namespace OAI

/-! Coordinate images of a minimal simultaneous row family are minimal.
The proved one-map theorem therefore produces a common modular cluster. -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {J : Type*} {c : J → ℝ}

theorem family_orbitClosure_coordinate (hc : ∀ j, 0 ≤ c j) (F : WeakMapFamily M c)
    {G : WeakMapFamily M c} (hG : G ∈ closure (familyRowOrbit hc F)) (j : J) :
    G j ∈ closure (boundedWeakRowOrbit (F j)) := by
  apply closure_minimal (t := {A : WeakMapFamily M c |
    A j ∈ closure (boundedWeakRowOrbit (F j))}) _
      (isClosed_closure.preimage (continuous_apply j)) hG
  rintro A ⟨n, r, hr, rfl⟩
  apply subset_closure
  exact ⟨n, r, hr, rfl⟩

theorem minimal_family_coordinate (hc : ∀ j, 0 ≤ c j)
    (C : Set (WeakMapFamily M c)) (hclosed : IsClosed C)
    (hinv : FamilyRowInvariant hc C)
    (hmin : ∀ D : Set (WeakMapFamily M c), D ⊆ C → D.Nonempty → IsClosed D →
      FamilyRowInvariant hc D → D = C) (j : J) :
    IsClosed ((fun F => F j) '' C) ∧ RowInvariant (hc j) ((fun F => F j) '' C) ∧
      ∀ D : Set (BoundedWeakAlgebraMap M (c j)), D ⊆ ((fun F => F j) '' C) →
        D.Nonempty → IsClosed D → RowInvariant (hc j) D → D = ((fun F => F j) '' C) := by
  let (j : J) : CompactSpace (BoundedWeakAlgebraMap M (c j)) :=
    isCompact_univ_iff.mp (isCompact_boundedWeakAlgebraMap M (hc j))
  refine ⟨(hclosed.isCompact.image (continuous_apply j)).isClosed, ?_, ?_⟩
  · intro n r hr G hG
    obtain ⟨A, hA, rfl⟩ := hG
    exact ⟨familyRowAverage hc r hr A, hinv n r hr hA, rfl⟩
  · intro D hD hne hcl hi
    let E : Set (WeakMapFamily M c) := C ∩ (fun F => F j) ⁻¹' D
    have hEC : E ⊆ C := fun _ h => h.1
    have hEn : E.Nonempty := by
      obtain ⟨G, hG⟩ := hne
      obtain ⟨A, hA, he⟩ := hD hG
      change A j = G at he
      exact ⟨A, hA, by change A j ∈ D; rwa [he]⟩
    have hEcl : IsClosed E := hclosed.inter (hcl.preimage (continuous_apply j))
    have hEi : FamilyRowInvariant hc E := by
      intro n r hr A hA
      exact ⟨hinv n r hr hA.1, hi n r hr hA.2⟩
    have he := hmin E hEC hEn hEcl hEi
    apply Set.Subset.antisymm hD
    rintro G ⟨A, hA, rfl⟩
    have hAE : A ∈ E := by rw [he]; exact hA
    exact hAE.2

theorem exists_simultaneous_modular_cluster [Nontrivial H]
    (hc : ∀ j, 0 ≤ c j) (F : WeakMapFamily M c) :
    ∃ G ∈ closure (familyRowOrbit hc F), ∀ j a b, (G j).map (a * b) = (G j).map a * b := by
  obtain ⟨C, hCF, hne, hcl, hi, hm⟩ := exists_minimal_familyRowFamily hc F
  obtain ⟨G, hG⟩ := hne
  refine ⟨G, hCF hG, ?_⟩
  intro j
  obtain ⟨hdcl, hdi, hdm⟩ := minimal_family_coordinate hc C hcl hi hm j
  apply minimal_row_family_right_module (hc j) (F j) ((fun A => A j) '' C) _ hdcl hdi hdm
    (G j) ⟨G, hG, rfl⟩
  rintro B ⟨A, hA, rfl⟩
  exact family_orbitClosure_coordinate hc F (hCF hA) j

end

end KadisonKastler

end OAI
