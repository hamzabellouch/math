import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGlobalGeneratorWords
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryLeaf

namespace OAI

/-! # Extending generator height bounds to whole nilpotent leaves -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set
open scoped Manifold

variable {EG G W P : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- A parameter-independent bound on each complete generator flow gives
one bound on every leaf of the actual nilpotent factor. -/
theorem exists_uniform_nilpotent_leaf_bound
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (η : P → G → W) {B : ℝ} (hB : 0 ≤ B)
    (hstep : ∀ (p : P) (x : G) (i : Fin M.letterCount) (t : ℝ),
      ‖η p (x * ExpG (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) - η p x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p x (n : F.N.carrier),
      ‖η p (x * F.inclusionN n) - η p x‖ ≤ C := by
  classical
  obtain ⟨N, hw⟩ := M.exists_global_cartan_generator_words T F hExpG realize haarN dynkinN b₀
  let gen := fun z : Fin M.letterCount × ℝ =>
    ExpG (z.2 • (M.letter z.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  refine ⟨(N : ℝ) * B, by positivity, ?_⟩
  intro p x n
  obtain ⟨u, hu, he⟩ := hw n
  let l := u.map gen
  have hl : l.prod = F.inclusionN n := by
    have hm := congrArg F.inclusionN he
    simp only [generatorGroupWord, map_list_prod, List.map_map, Function.comp_def] at hm
    calc
      l.prod = (u.map (fun z => F.inclusionN (F.ExpN (F.N.equiv (z.2 • M.letter z.1))))).prod := by
        congr 1
        apply List.map_congr_left
        intro z _
        simpa only [LieSubmodule.coe_smul] using (F.compatibleN (z.2 • M.letter z.1)).symm
      _ = F.inclusionN n := hm
  have hgen : ∀ g ∈ Set.range gen, ∀ x, ‖η p (x * g) - η p x‖ ≤ B := by
    rintro g ⟨z, rfl⟩ y
    exact hstep p y z.1 z.2
  have hmem : ∀ g ∈ l, g ∈ Set.range gen := by
    intro g hg
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hg
    exact Set.mem_range_self z
  rw [← hl]
  exact (norm_increment_list_prod (η p) (Set.range gen) hgen l hmem x).trans
    (mul_le_mul_of_nonneg_right (by simpa only [l, List.length_map] using (Nat.cast_le.mpr hu : (u.length : ℝ) ≤ N)) hB)

end PolycyclicRecognition.CartanWordModel

end

end OAI
