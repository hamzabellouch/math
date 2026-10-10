import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledWordPrefixes

namespace OAI

/-! # Bounded prefixes when a smaller template is used for generation -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

variable {I L E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- Uniform generation in a smaller template does not force a change of the
ambient maximizing basis. Shrinking each normalized letter amplitude
places every prefix in a fixed-radius box for the larger template. -/
theorem exists_uniform_dominated_word_prefix_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (X : I → L) {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords c)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (N : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (s t : I → ℝ), (∀ i, s i ≤ t i) →
      ∀ β : WordBasisSelections X (boundedBracketWords c),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords c) b₀)
        (fun w => bracketWordExponent t w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ u : List (I × ℝ), u.length ≤ N →
      (∀ z ∈ u, |z.2| ≤ A) → ∀ j : ℕ,
      generatorGroupWord (fun i => Real.exp (r * s i) • X i) (Exp ∘ e) (u.take j) ∈
        exponentialCoordinateBox (Exp ∘ e)
          (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
            (fun k => bracketWordExponent t (β.val k)) r) D := by
  obtain ⟨D, hD, hprefix⟩ := exists_uniform_rescaled_word_prefix_bound
    dynkin e Exp hExp X hc hletters b₀ N hA
  refine ⟨D, hD, ?_⟩
  intro s t hst β hβ r hr u hu hamp j
  let renorm := fun z : I × ℝ => (z.1, z.2 * Real.exp (r * (s z.1 - t z.1)))
  have hrenorm (z : I × ℝ) : |(renorm z).2| ≤ |z.2| := by
    change |z.2 * Real.exp (r * (s z.1 - t z.1))| ≤ |z.2|
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ |z.2| * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr (hst z.1))))
        (abs_nonneg _)
      _ = _ := mul_one _
  have hh := hprefix t β hβ r hr (u.map renorm)
    (by simpa only [List.length_map] using hu)
    (by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact (hrenorm y).trans (hamp y hy)) j
  have hword : generatorGroupWord (fun i => Real.exp (r * t i) • X i)
      (Exp ∘ e) ((u.map renorm).take j) =
      generatorGroupWord (fun i => Real.exp (r * s i) • X i) (Exp ∘ e) (u.take j) := by
    simp only [generatorGroupWord, ← List.map_take, List.map_map]
    congr 1
    apply List.map_congr_left
    intro z _
    apply congrArg (Exp ∘ e)
    change (z.2 * Real.exp (r * (s z.1 - t z.1))) •
      (Real.exp (r * t z.1) • X z.1) = z.2 • (Real.exp (r * s z.1) • X z.1)
    rw [smul_smul, smul_smul, mul_assoc, ← Real.exp_add]
    rw [show r * (s z.1 - t z.1) + r * t z.1 = r * s z.1 by ring]
  rwa [hword] at hh

end PolycyclicRecognition

end

end OAI
