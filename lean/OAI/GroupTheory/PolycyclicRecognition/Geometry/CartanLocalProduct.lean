import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocalSubmersion
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDecomposition
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMultiplication
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

namespace OAI

/-! # Local multiplication of the actual Cartan factors

Surjectivity of the differential follows from spanning by the two Lie
algebras. The factors may overlap. The resulting local open mapping property
propagates to every point by left and right translations.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter Set
open scoped Manifold Topology ContDiff

variable {EN ED EG N D G : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [NormedAddCommGroup ED] [NormedSpace ℝ ED] [FiniteDimensional ℝ ED]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [TopologicalSpace D] [ChartedSpace ED D] [Group D] [LieGroup (𝓘(ℝ, ED)) ⊤ D]
  [TopologicalSpace G] [ChartedSpace EG G] [Group G] [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  (ι : N →* G) (κ : D →* G)

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ ED] [FiniteDimensional ℝ EG]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [LieGroup (𝓘(ℝ, ED)) ⊤ D] in
/-- The derivative of multiplication of homomorphisms at the identity is
the sum of their derivatives. -/
theorem mfderiv_factorProduct_one
    (hι : ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι)
    (hκ : ContMDiff (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) ∞ κ)
    (v : TangentSpace ((𝓘(ℝ, EN)).prod (𝓘(ℝ, ED))) (1 : N × D)) :
    (tangentSpaceCast (𝓘(ℝ, EG)) (ι 1 * κ 1) 1)
      (mfderiv ((𝓘(ℝ, EN)).prod (𝓘(ℝ, ED))) (𝓘(ℝ, EG))
        (fun p : N × D => ι p.1 * κ p.2) 1 v) =
      (tangentSpaceCast (𝓘(ℝ, EG)) (ι 1) 1) (mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 v.1) +
      (tangentSpaceCast (𝓘(ℝ, EG)) (κ 1) 1) (mfderiv (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) κ 1 v.2) := by
  have hs : MDifferentiableAt ((𝓘(ℝ, EN)).prod (𝓘(ℝ, ED))) (𝓘(ℝ, EG))
      (fun p : N × D => ι p.1 * κ p.2) 1 :=
    ((hι.comp contMDiff_fst).mul (hκ.comp contMDiff_snd)).mdifferentiableAt
      (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have he := mfderiv_prod_eq_add_apply (v := v) hs
  have hl : (fun z : N => ι z * κ 1) = ι := by ext z; simp
  have hr : (fun z : D => ι 1 * κ z) = κ := by ext z; simp
  change _ = mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) (fun z : N => ι z * κ 1) 1 v.1 +
    mfderiv (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) (fun z : D => ι 1 * κ z) 1 v.2 at he
  rw [hl, hr] at he
  exact he

omit [LieGroup (𝓘(ℝ, EN)) ⊤ N] [LieGroup (𝓘(ℝ, ED)) ⊤ D] in
/-- Spanning tangent images give the exact local open mapping property. -/
theorem factorProduct_map_nhds_one
    (hι : ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι)
    (hκ : ContMDiff (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) ∞ κ)
    (hspan : ∀ z : GroupLieAlgebra (𝓘(ℝ, EG)) G,
      ∃ u v, (tangentSpaceCast (𝓘(ℝ, EG)) (ι 1) 1) (mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 u) +
        (tangentSpaceCast (𝓘(ℝ, EG)) (κ 1) 1) (mfderiv (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) κ 1 v) = z) :
    map (fun p : N × D => ι p.1 * κ p.2) (𝓝 (1 : N × D)) = 𝓝 (1 : G) := by
  have hs : ContMDiffAt ((𝓘(ℝ, EN)).prod (𝓘(ℝ, ED))) (𝓘(ℝ, EG)) 1
      (fun p : N × D => ι p.1 * κ p.2) 1 :=
    (((hι.comp contMDiff_fst).mul (hκ.comp contMDiff_snd)).contMDiffAt
      (x := 1)).of_le (by simp)
  have hsurj : Function.Surjective
      (mfderiv ((𝓘(ℝ, EN)).prod (𝓘(ℝ, ED))) (𝓘(ℝ, EG))
        (fun p : N × D => ι p.1 * κ p.2) 1) := by
    intro z
    obtain ⟨u, v, huv⟩ := hspan ((tangentSpaceCast (𝓘(ℝ, EG)) (ι 1 * κ 1) 1) z)
    refine ⟨(u, v), (tangentSpaceCast (𝓘(ℝ, EG)) (ι 1 * κ 1) 1).injective ?_⟩
    exact (mfderiv_factorProduct_one ι κ hι hκ (u, v)).trans huv
  simpa only [Prod.fst_one, Prod.snd_one, map_one, mul_one] using
    map_nhds_eq_of_surjective_mfderiv hs hsurj

/-- The previously proved Cartan spanning theorem supplies the differential
surjectivity, including when the two subalgebras intersect. -/
theorem cartanFactorProduct_map_nhds_one
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
    (hι : ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι)
    (hκ : ContMDiff (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) ∞ κ)
    (dι : ∀ x : cartanRootIdeal H,
      (tangentSpaceCast (𝓘(ℝ, EG)) (ι 1) 1)
        (mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 (eN x)) = x)
    (dκ : ∀ x : H,
      (tangentSpaceCast (𝓘(ℝ, EG)) (κ 1) 1)
        (mfderiv (𝓘(ℝ, ED)) (𝓘(ℝ, EG)) κ 1 (eD x)) = x) :
    map (fun p : N × D => ι p.1 * κ p.2) (𝓝 (1 : N × D)) = 𝓝 (1 : G) := by
  apply factorProduct_map_nhds_one ι κ hι hκ
  intro z
  have hz : z ∈ (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule := by
    rw [triangular_cartan_spanning T H]
    trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hz
  refine ⟨eN ⟨u, hu⟩, eD ⟨v, hv⟩, ?_⟩
  rw [dι, dκ]
  exact huv

/-- A local factor product gives both global factorization and compact
lifts in a connected Lie group. No complement or global section is needed. -/
theorem factorProduct_surjective_and_compact_lifts
    [PreconnectedSpace G] [IsTopologicalGroup N] [IsTopologicalGroup D]
    [IsTopologicalGroup G] [LocallyCompactSpace N] [LocallyCompactSpace D]
    (φ : D →* MulAut N)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (hlocal : map (fun p : N × D => ι p.1 * κ p.2) (𝓝 (1 : N × D)) = 𝓝 (1 : G)) :
    Function.Surjective (fun p : N × D => ι p.1 * κ p.2) ∧
      ∀ K : Set G, IsCompact K → ∃ C : Set (N × D), IsCompact C ∧
        K ⊆ (fun p : N × D => ι p.1 * κ p.2) '' C := by
  have hopen := isOpenMap_factorProduct_of_map_nhds_one ι κ hlocal
  have hnhds : Set.range (fun p : N × D => ι p.1 * κ p.2) ∈ 𝓝 (1 : G) := by
    rw [← hlocal]
    exact Filter.mem_map.mpr (by simp)
  have hsurj := cartanMultiplication_surjective_of_range_mem_nhds ι κ φ hconj hnhds
  refine ⟨?_, fun K hK => exists_compact_cartan_factor_lifts ι κ φ hconj hnhds hopen hK⟩
  intro g
  obtain ⟨z, hz⟩ := hsurj g
  exact ⟨(z.left, z.right), hz⟩

end PolycyclicRecognition

end

end OAI
