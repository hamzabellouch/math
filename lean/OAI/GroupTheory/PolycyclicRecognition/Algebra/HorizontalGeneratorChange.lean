import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedGeneration

namespace OAI

/-! # Changing a horizontal spanning family preserves bracket generation -/

noncomputable section

namespace PolycyclicRecognition

open Module

theorem exists_word_basis_of_spanning_horizontal
    {H V I J K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] V) (hB : IsLieBracket B)
    (D : H →L[ℝ] V) (X : I → H) (b₀ : Basis K ℝ V) (w₀ : K → FreeMagma I)
    (hw₀ : ∀ k, evalBilinearWord B (fun i => D (X i)) (w₀ k) = b₀ k)
    (Y : J → H) (hY : Submodule.span ℝ (Set.range Y) = ⊤) :
    ∃ b : Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∃ w : Fin (Module.finrank ℝ V) → FreeMagma J,
        ∀ k, evalBilinearWord B (fun j => D (Y j)) (w k) = b k := by
  let := lieRingOfBilinear B hB
  let := lieAlgebraOfBilinear B hB
  let P := LieSubalgebra.lieSpan ℝ V (Set.range (fun j => D (Y j)))
  have hD (h : H) : D h ∈ P := by
    have hh : h ∈ Submodule.span ℝ (Set.range Y) := by rw [hY]; trivial
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨j, rfl⟩ := hh
      exact LieSubalgebra.subset_lieSpan ⟨j, rfl⟩
    | zero => simpa only [map_zero] using P.zero_mem
    | add h k _ _ hh hk => simpa only [map_add] using P.add_mem hh hk
    | smul c h _ hh => simpa only [map_smul] using P.smul_mem c hh
  have hP : P = ⊤ := by
    apply top_unique
    rw [← lieSpan_eq_top_of_word_basis B hB (fun i => D (X i)) b₀ w₀ hw₀]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hD (X i)
  obtain ⟨b, hb⟩ := exists_bracketWord_basis (fun j => D (Y j)) hP
  choose w hw using hb
  refine ⟨b, w, fun k => ?_⟩
  rw [evalBilinearWord_eq_lieWord B hB]
  exact hw k

end PolycyclicRecognition

end

end OAI
