import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledGeneratorBounds
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorConjugation

namespace OAI

/-! # Uniform coordinate bounds for every prefix of a bounded generator word

This is the prefix control needed to apply the neighboring-sheet argument
to words supplied by uniform generation. Both the word length and the
normalized amplitudes are bounded; the box shape and scale may vary.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

variable {I L E G : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

omit [FiniteDimensional ℝ L] in
/-- Every prefix of every bounded normalized generator word remains in a
single uniformly enlarged rescaled box. -/
theorem exists_uniform_rescaled_word_prefix_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (X : I → L) {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords c)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (N : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords c)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords c) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ u : List (I × ℝ), u.length ≤ N →
      (∀ z ∈ u, |z.2| ≤ A) → ∀ j : ℕ,
      generatorGroupWord (fun i => Real.exp (r * s i) • X i) (Exp ∘ e) (u.take j) ∈
        exponentialCoordinateBox (Exp ∘ e)
          (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
            (fun k => bracketWordExponent s (β.val k)) r) D := by
  obtain ⟨R, hR, hgen⟩ := exists_uniform_rescaled_generator_bound
    X (boundedBracketWords c) hletters b₀
  obtain ⟨K, hK, hprod⟩ := exists_uniform_word_box_product_bound dynkin e Exp hExp X hc b₀
  let D := K * (1 + (N : ℝ)) ^ c * (1 + A * R) ^ c
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro s β hβ r hr u hu hamp j
  let v := u.take j
  let b := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
    (fun k => bracketWordExponent s (β.val k)) r
  let g := fun k : Fin v.length => Exp (e ((v.get k).2 • (Real.exp (r * s (v.get k).1) • X (v.get k).1)))
  have hg (k : Fin v.length) : g k ∈ exponentialCoordinateBox (Exp ∘ e) b (A * R) := by
    refine ⟨(v.get k).2 • (Real.exp (r * s (v.get k).1) • X (v.get k).1), rfl, ?_⟩
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hamp _ (List.mem_of_mem_take (List.get_mem v k)))
      (hgen s β hβ r hr _) (norm_nonneg _) hA
  have hp := hprod s β hβ r hr v.length (A * R) (mul_nonneg hA hR) g hg
  have hlist : List.ofFn g = v.map (fun z : I × ℝ =>
      Exp (e (z.2 • (Real.exp (r * s z.1) • X z.1)))) := by
    dsimp only [g]
    rw [List.ofFn_comp' v.get (fun z : I × ℝ =>
      Exp (e (z.2 • (Real.exp (r * s z.1) • X z.1)))), List.ofFn_get]
  rw [hlist] at hp
  change generatorGroupWord (fun i => Real.exp (r * s i) • X i) (Exp ∘ e) v ∈
    exponentialCoordinateBox (Exp ∘ e) b
      (K * (1 + (v.length : ℝ)) ^ c * (1 + A * R) ^ c) at hp
  obtain ⟨x, hx, hbound⟩ := hp
  refine ⟨x, hx, hbound.trans ?_⟩
  have hlen : v.length ≤ N := by
    simpa only [v, List.length_take] using (Nat.min_le_right j u.length).trans hu
  have hlen' : (v.length : ℝ) ≤ N := by exact_mod_cast hlen
  dsimp only [D]
  gcongr

end PolycyclicRecognition

end

end OAI
