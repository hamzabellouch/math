import OAI.Analysis.KadisonKastler.MinimalRowDynamics

namespace OAI

/-! Norm minimization may be performed on the invariant family itself.
This lets us use the uniquely defined cyclic right factor without extending
that factor to maps outside the family. -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {c : ℝ}

theorem minimal_row_family_quantity_constant_on
    (hc : 0 ≤ c) (C : Set (BoundedWeakAlgebraMap M c)) (hclosed : IsClosed C)
    (hinv : RowInvariant hc C)
    (hmin : ∀ D : Set (BoundedWeakAlgebraMap M c), D ⊆ C → D.Nonempty → IsClosed D →
      RowInvariant hc D → D = C)
    (q : C → ℝ) (hsub : ∀ a, IsClosed {F | q F ≤ a})
    (hdec : ∀ (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1)
      (F : C), q ⟨boundedWeakRowAverage hc r hr F.val, hinv n r hr F.property⟩ ≤ q F)
    (F G : C) : q F = q G := by
  have hle (A B : C) : q B ≤ q A := by
    let D : Set (BoundedWeakAlgebraMap M c) := Subtype.val '' {T : C | q T ≤ q A}
    have hDC : D ⊆ C := by
      rintro _ ⟨T, _, rfl⟩
      exact T.property
    have hne : D.Nonempty := ⟨A.val, A, show q A ≤ q A from le_rfl, rfl⟩
    have hcl : IsClosed D := hclosed.isClosedMap_subtype_val _ (hsub (q A))
    have hi : RowInvariant hc D := by
      intro n r hr T hT
      obtain ⟨T, hT, rfl⟩ := hT
      exact ⟨⟨boundedWeakRowAverage hc r hr T.val, hinv n r hr T.property⟩,
        (hdec n r hr T).trans hT, rfl⟩
    have he := hmin D hDC hne hcl hi
    have hB : B.val ∈ D := by rw [he]; exact B.property
    obtain ⟨B', hB', he'⟩ := hB
    change q B' ≤ q A at hB'
    have hBB : B' = B := Subtype.ext he'
    simpa only [hBB] using hB'
  exact le_antisymm (hle G F) (hle F G)

end

end KadisonKastler

end OAI
