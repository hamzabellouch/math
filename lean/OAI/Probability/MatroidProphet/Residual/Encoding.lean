import OAI.Probability.MatroidProphet.Residual.Timeline
import OAI.Probability.MatroidProphet.Pivots.PhasePattern
import OAI.Probability.MatroidProphet.Pivots.ResidualFamily

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}

noncomputable def validBirthMark (a : ℤ) (ε : Fin 2) (k : IntWindow a) : Bool :=
  decide (a + 2 ≤ k.val ∧ k.val ≤ 0 ∧ k.val % 2 = (ε.val : ℤ))

noncomputable def integerBirthLayer (X : ℤ → Set α) (test : Fin n → α) (a : ℤ)
    (ε : Fin 2) (b : ParityWindow a ε) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => a + 2 ≤ b.val.val ∧ b.val.val ≤ 0 ∧
    test f ∈ X b.val.val ∧ test f ∉ X (b.val.val - 1)

noncomputable def integerResidual {Z : Type*} (M : Matroid α) (X : ℤ → Set α)
    (test : Fin n → α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α)
    (z : Z → α) (β : Z → ParityWindow a ε) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => ∃ b, f ∈ integerBirthLayer X test a ε b ∧
    test f ∉ M.closure (X (b.val.val - 2) ∪ K b ∪ z '' {w | β w = b})

noncomputable def integerResidualFamily (M : Matroid α) (U : Finset α) (q : ℕ)
    (F : ℤ → Set α) (a : ℤ) (ε : Fin 2) (K : ParityWindow a ε → Set α)
    (test : Fin n → α) : Finset (Finset (Fin n)) :=
  residualFamily M U q
    (blockOldLabel (F := fun t : IntWindow a => F t.val))
    (blockOldLabel (F := phaseOld (fun t : ParityWindow a ε => F t.val.val) K))
    (fun o => validBirthMark a ε (blockOldStage o))
    (fun o => (ofLex (blockOldStage o)).2) test

lemma generatedPath_mono
    {α : Type u_1} [Fintype α] [LinearOrder α] {G : Type*}
    (M : Matroid α) (F : ℤ → Set α) (hF : Monotone F)
    (g : G → α) (ν : G → ℤ) : Monotone (generatedPath M F g ν) := by
  intro k l hkl
  exact M.closure_subset_closure (union_subset_union (hF hkl)
    (image_mono (fun _ hx => hx.trans hkl)))

lemma first_integer_pattern {G : Type*} [Fintype G]
    (M : Matroid α) (hE : M.E = Set.univ) (F : ℤ → Set α) (hF : Monotone F)
    (a : ℤ) (hFe : ∀ k < a, F k = M.closure ∅) (ε : Fin 2)
    (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (test : Fin n → α) (f : Fin n) :
    f ∈ blockBirthPattern M (fun t : IntWindow a => F t.val) g (windowPlacement a ν hν)
      test (validBirthMark a ε) ↔
      ∃ b, f ∈ integerBirthLayer (generatedPath M F g ν) test a ε b := by
  classical
  simp only [blockBirthPattern, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hm, hx, hn⟩
    have hv : a + 2 ≤ k.val ∧ k.val ≤ 0 ∧ k.val % 2 = (ε.val : ℤ) := by
      simpa [validBirthMark] using hm
    rw [window_prefix M F hF] at hx
    rw [window_before M hE F hF a hFe] at hn
    exact ⟨⟨k, hv.2.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.1, hv.2.1, hx, hn⟩⟩
  · rintro ⟨b, hb⟩
    have hv : a + 2 ≤ b.val.val ∧ b.val.val ≤ 0 ∧
        test f ∈ generatedPath M F g ν b.val.val ∧ test f ∉ generatedPath M F g ν (b.val.val - 1) := by
      simpa [integerBirthLayer] using hb
    refine ⟨b.val, ?_, ?_, ?_⟩
    · simpa [validBirthMark] using And.intro hv.1 (And.intro hv.2.1 b.property)
    · rw [window_prefix M F hF]
      exact hv.2.2.1
    · rw [window_before M hE F hF a hFe]
      exact hv.2.2.2

lemma integerResidual_mem_family (M : Matroid α) (hE : M.E = Set.univ)
    (U J Z : Finset α) (q : ℕ) (F : ℤ → Set α) (hF : Monotone F)
    (a : ℤ) (ha : a ≤ 0) (hFe : ∀ k < a, F k = M.closure ∅)
    (hFl : ∀ k, 0 ≤ k → F k = Set.univ) (ε : Fin 2)
    (K : ParityWindow a ε → Set α) (hK : ∀ b, K b ⊆ F b.val.val)
    (ν : J → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0)
    (β : Z → ParityWindow a ε)
    (hz : ∀ w, w.val ∈ generatedPath M F (fun i : J => i.val) ν (β w).val.val)
    (test : Fin n → α) (hnonloop : ∀ f, test f ∉ M.closure ∅)
    (hJ : J ⊆ U) (hJq : J.card ≤ q) (hZ : Z ⊆ U) (hZq : Z.card ≤ q) :
    integerResidual M (generatedPath M F (fun i : J => i.val) ν) test a ε K
        (fun w : Z => w.val) β ∈ integerResidualFamily M U q F a ε K test := by
  classical
  let g : J → α := fun i => i.val
  let z : Z → α := fun i => i.val
  let FW := fun t : IntWindow a => F t.val
  let FP := fun t : ParityWindow a ε => F t.val.val
  let θ := parityPlacement a ε ν hν
  let first := blockBirthPattern M FW g (windowPlacement a ν hν) test (validBirthMark a ε)
  let second := blockBirthPattern M (phaseOld FP K) (Sum.elim g z) (phasePlacement θ β) test
    (fun p => (ofLex p).2)
  have hz' : ∀ w, z w ∈ upperPath M FP g θ (β w) := by
    intro w
    rw [parity_upperPath]
    exact hz w
  have hFP : Monotone FP := fun _ _ h => hF h
  have hfirst : ∀ f, f ∈ first ↔ ∃ b, f ∈ integerBirthLayer (generatedPath M F g ν) test a ε b :=
    first_integer_pattern M hE F hF a hFe ε g ν hν test
  have hP : ∀ b f, f ∈ integerBirthLayer (generatedPath M F g ν) test a ε b →
      test f ∈ upperPath M FP g θ b ∧ test f ∉ lowerPath M FP g θ b := by
    intro b f hf
    have hv : a + 2 ≤ b.val.val ∧ b.val.val ≤ 0 ∧
        test f ∈ generatedPath M F g ν b.val.val ∧ test f ∉ generatedPath M F g ν (b.val.val - 1) := by
      simpa [integerBirthLayer] using hf
    rw [parity_upperPath, parity_lowerPath M hE F hF a hFe]
    exact ⟨hv.2.2.1, fun he => hv.2.2.2 (generatedPath_mono M F hF g ν (by omega) he)⟩
  have hinter := first_inter_phase_eq_residual M hE FP K hFP hK g z θ β hz' test
    (integerBirthLayer (generatedPath M F g ν) test a ε) first hfirst hP
  have hres : residualOfLayers M FP K g z θ β test
      (integerBirthLayer (generatedPath M F g ν) test a ε) =
      integerResidual M (generatedPath M F g ν) test a ε K z β := by
    ext f
    simp only [residualOfLayers, integerResidual, Finset.mem_filter, Finset.mem_univ, true_and,
      FP, θ, parity_lowerPath M hE F hF a hFe]
  rw [hres] at hinter
  rw [← hinter]
  apply mem_residualFamily M U J Z q _ _ _ _ test first second hJ hJq hZ hZq
  · apply blockBirthPattern_mem_freeMarkedPatterns M FW g (windowPlacement a ν hν) test
      (validBirthMark a ε) hnonloop
    intro f
    apply M.subset_closure _ (by simp [hE])
    let k : IntWindow a := ⟨0, by constructor <;> omega⟩
    have he : test f ∈ FW k := by change test f ∈ F 0; simp [hFl 0 le_rfl]
    exact ⟨Sum.inl ⟨toLex (k, test f), he⟩, rfl⟩
  · apply blockBirthPattern_mem_freeMarkedPatterns M (phaseOld FP K) (Sum.elim g z)
      (phasePlacement θ β) test (fun p => (ofLex p).2) hnonloop
    intro f
    apply M.subset_closure _ (by simp [hE])
    let b : ParityWindow a ε := ⟨⟨roundParity ε 0, by
      have := roundParity_bounds ε 0
      constructor <;> omega⟩, roundParity_mod ε 0⟩
    have he : test f ∈ phaseOld FP K (toLex (b, true)) := by
      change test f ∈ F (roundParity ε 0)
      simp [hFl _ (roundParity_bounds ε 0).1]
    exact ⟨Sum.inl ⟨toLex (toLex (b, true), test f), he⟩, rfl⟩

end MatroidProphet.Pivots

end OAI
