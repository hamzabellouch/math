import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveRescaling
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledUniformGeneration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponentBounds

namespace OAI

/-! # Passing from uniformly rescaled words to global bounded word width -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology

/-- Positive coordinate widths exhaust the whole Lie algebra. Uniform
rescaled word length therefore gives bounded global word length after
absorbing the rescaling into the unrestricted generator amplitudes. -/
theorem global_generator_words_of_uniform_rescaling
    {L G I J : Type*} [LieRing L] [LieAlgebra ℝ L] [Group G] [Fintype J]
    (X : I → L) (Exp : L → G) (b : Basis J ℝ L) (cost : J → ℝ)
    (hcost : ∀ j, 0 < cost j) (N : ℕ)
    (hwords : ∀ r : ℝ, 0 ≤ r → ∀ v : L,
      ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤ 1 →
      ∃ u : List (I × ℝ), u.length ≤ N ∧
        generatorGroupWord (fun i => Real.exp r • X i) Exp u = Exp v) :
    ∀ v : L, ∃ u : List (I × ℝ), u.length ≤ N ∧ generatorGroupWord X Exp u = Exp v := by
  intro v
  have hlim := exponentialRescaleBasis_coordinates_tendsto_zero b cost hcost v
  have hnorm : Tendsto (fun r : ℝ => ‖(exponentialRescaleBasis b cost r).equivFun v‖)
      atTop (𝓝 (0 : ℝ)) := by simpa only [norm_zero] using hlim.norm
  have hsmall : ∀ᶠ r : ℝ in atTop, ‖(exponentialRescaleBasis b cost r).equivFun v‖ < 1 := by
    exact hnorm.eventually (eventually_lt_nhds zero_lt_one)
  obtain ⟨r, hr, hrv⟩ := ((eventually_ge_atTop (0 : ℝ)).and hsmall).exists
  obtain ⟨u, hu, he⟩ := hwords r hr v hrv.le
  let u' := u.map (fun z => (z.1, z.2 * Real.exp r))
  refine ⟨u', by simpa only [u', List.length_map] using hu, ?_⟩
  have hword : generatorGroupWord X Exp u' =
      generatorGroupWord (fun i => Real.exp r • X i) Exp u := by
    simp only [generatorGroupWord, u', List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro z _
    rw [smul_smul]
  exact hword.trans he

/-- The uniform word theorem over all generator weights already implies
bounded word width on the entire exponential group. -/
theorem global_generator_words_of_all_rescalings
    {L G I : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [Group G] [Fintype I] [DecidableEq I]
    (X : I → L) (Exp : L → G) (S : Finset (FreeMagma I))
    [Nonempty (WordBasisSelections X S)]
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (hwords : ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧
      ∀ (s : I → ℝ) (β : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀)
        (fun w : S => bracketWordExponent s w.val) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ v : L,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j : Fin (finrank ℝ L) => bracketWordExponent s (β.val j).val) r).equivFun v‖ ≤ 1 →
      ∃ u : List (I × ℝ), u.length ≤ N ∧ (∀ z ∈ u, |z.2| ≤ C) ∧
        generatorGroupWord (fun i => Real.exp (r * s i) • X i) Exp u = Exp v) :
    ∃ N : ℕ, ∀ v : L, ∃ u : List (I × ℝ),
      u.length ≤ N ∧ generatorGroupWord X Exp u = Exp v := by
  obtain ⟨β, hβ⟩ := exists_maximizing_wordBasis X S b₀
    (fun w : S => bracketWordExponent (fun _ : I => (1 : ℝ)) w.val)
  obtain ⟨N, C, _, hwords⟩ := hwords
  refine ⟨N, global_generator_words_of_uniform_rescaling X Exp
    (WordBasisSelections.basis X S β)
    (fun j : Fin (finrank ℝ L) => bracketWordExponent (fun _ : I => (1 : ℝ)) (β.val j).val)
    (fun j : Fin (finrank ℝ L) => bracketWordExponent_pos (I := I) (fun _ : I => (1 : ℝ)) (fun _ => zero_lt_one) (β.val j).val)
    N ?_⟩
  intro r hr v hv
  obtain ⟨u, hu, _, he⟩ := hwords (fun _ => 1) β hβ r hr v hv
  exact ⟨u, hu, by simpa only [mul_one] using he⟩

end PolycyclicRecognition

end

end OAI
