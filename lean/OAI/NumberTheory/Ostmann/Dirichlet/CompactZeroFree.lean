import OAI.NumberTheory.Ostmann.Dirichlet.Zeros

namespace OAI

open Set Filter
open scoped Topology

namespace Ostmann.Dirichlet

theorem exists_fixed_character_zero_free_strip {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ,
      1 - δ ≤ s.re → |s.im| ≤ T → χ.LFunction s ≠ 0 := by
  let K : Set ℂ := (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) '' Icc (-T) T
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hopen : IsOpen {s : ℂ | χ.LFunction s ≠ 0} :=
    isOpen_ne.preimage (DirichletCharacter.differentiable_LFunction hχ).continuous
  have hKne : K ⊆ {s : ℂ | χ.LFunction s ≠ 0} := by
    rintro _ ⟨t, ht, rfl⟩
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp)
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hopen hKne
  refine ⟨δ, hδ, ?_⟩
  intro s hs him
  by_cases hre : 1 ≤ s.re
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre
  · apply hsub
    apply Metric.mem_cthickening_of_dist_le s (1 + (s.im : ℂ) * Complex.I) δ K
    · exact ⟨s.im, abs_le.mp him, rfl⟩
    · have he : s - (1 + (s.im : ℂ) * Complex.I) = ((s.re - 1 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [dist_eq_norm, he, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : s.re - 1 ≤ 0)]
      linarith

theorem exists_finite_family_zero_free_strip {ι : Type*} (F : Finset ι)
    (q : ι → ℕ) (hq : ∀ i, NeZero (q i))
    (χ : (i : ι) → DirichletCharacter ℂ (q i))
    (hχ : ∀ i ∈ F, χ i ≠ 1) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ F, ∀ s : ℂ,
      1 - δ ≤ s.re → |s.im| ≤ T → @DirichletCharacter.LFunction (q i) (hq i) (χ i) s ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i F hi ih =>
      obtain ⟨δ, hδ, hF⟩ := ih (fun j hj => hχ j (Finset.mem_insert_of_mem hj))
      let : NeZero (q i) := hq i
      obtain ⟨ε, hε, hiχ⟩ := exists_fixed_character_zero_free_strip
        (χ i) (hχ i (Finset.mem_insert_self i F)) T
      refine ⟨min δ ε, lt_min hδ hε, ?_⟩
      intro j hj s hs him
      rcases Finset.mem_insert.mp hj with rfl | hj
      · apply hiχ s _ him
        have := min_le_right δ ε
        linarith
      · apply hF j hj s _ him
        have := min_le_left δ ε
        linarith

end Ostmann.Dirichlet

end OAI
