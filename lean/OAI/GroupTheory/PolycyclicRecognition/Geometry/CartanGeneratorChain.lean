import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGeneratorPrefixes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorWordPadding

namespace OAI

/-! # Fixed-length bounded-prefix chains in actual Cartan boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- Every point in a rescaled box is joined to zero by one fixed number of
actual generator steps. Every logarithmic prefix stays in a common enlarged
box. This supplies the vertices and edges used by profile concentration. -/
theorem exists_uniform_cartan_generator_chain
    [Nonempty (Fin M.letterCount)]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (R : ℝ) :
    ∃ (N : ℕ) (C D : ℝ), 1 ≤ C ∧ 0 ≤ D ∧
      ∀ (s : Fin M.letterCount → ℝ) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ v : cartanRootIdeal H,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun k => bracketWordExponent s (β.val k)) r).equivFun v‖ ≤ R →
      ∃ u : List (Fin M.letterCount × ℝ), ∃ k : ℕ → cartanRootIdeal H,
        u.length = N ∧ (∀ z ∈ u, |z.2| ≤ C) ∧ k 0 = 0 ∧ k N = v ∧
        (∀ j, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
          (fun i => bracketWordExponent s (β.val i)) r).equivFun (k j)‖ ≤ D) ∧
        ∀ j (hj : j < u.length),
          F.ExpN (F.N.equiv (k (j + 1))) = F.ExpN (F.N.equiv (k j)) *
            F.ExpN (F.N.equiv (u[j].2 • (Real.exp (r * s u[j].1) • M.letter u[j].1))) := by
  classical
  obtain ⟨N, C, D, hC, hD, hwords⟩ := M.exists_uniform_cartan_generator_prefixes T F
    hExpG realize haarN dynkinN b₀ R
  obtain ⟨⟨chart, hchart⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  have hinj : Function.Injective (F.ExpN ∘ F.N.equiv) :=
    (funext hchart ▸ chart.injective).comp F.N.equiv.injective
  have hzero : (F.ExpN ∘ F.N.equiv) 0 = 1 := by simp only [Function.comp_apply, map_zero, F.isExpN.map_zero]
  let i₀ : Fin M.letterCount := Classical.choice inferInstance
  refine ⟨N, C, D, hC, hD, ?_⟩
  intro s β hβ r hr v hv
  obtain ⟨u₀, hu₀, hamp₀, hend₀, hprefix₀⟩ := hwords s β hβ r hr v hv
  let X := fun i => Real.exp (r * s i) • M.letter i
  obtain ⟨u, hu, hamp, hend, hprefix⟩ := exists_fixed_length_generator_word X
    (F.ExpN ∘ F.N.equiv) hzero i₀ u₀ hu₀ ((by norm_num : (0 : ℝ) ≤ 1).trans hC) hamp₀
  have hkall (j : ℕ) : ∃ w : cartanRootIdeal H,
      (F.ExpN ∘ F.N.equiv) w = generatorGroupWord X (F.ExpN ∘ F.N.equiv) (u.take j) ∧
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => bracketWordExponent s (β.val i)) r).equivFun w‖ ≤ D := by
    obtain ⟨w, hw, hb⟩ := hprefix₀ j
    exact ⟨w, hw.trans (hprefix j).symm, hb⟩
  choose k hk hbound using hkall
  obtain ⟨hk0, hkN, hstep⟩ := generator_prefix_log_chain X (F.ExpN ∘ F.N.equiv)
    hinj hzero u hu k hk v (hend.trans hend₀)
  exact ⟨u, k, hu, hamp, hk0, hkN, hbound, hstep⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
