import OAI.Analysis.KadisonSimilarity.Derivation.QuadraticSandwich
import OAI.Analysis.KadisonSimilarity.Representation.FiniteOrbitComparison
import OAI.Analysis.KadisonSimilarity.Similarity.SimilarityMetric
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! A positive functional comparable to a cyclic orbit gives an actual
invertible intertwiner with its GNS representation. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def boundedHomOrbit (π : BoundedUnitalHom A H) (ξ : H) : A →L[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H ξ).comp ⟨π.1.toLinearMap, π.2⟩

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
@[simp] theorem boundedHomOrbit_apply (π : BoundedUnitalHom A H) (ξ : H) (a : A) :
    boundedHomOrbit π ξ a = π.1 a ξ := rfl

theorem similarity_of_cyclic_orbit_sandwich (π : BoundedUnitalHom A H) (ξ : H)
    (hcyc : DenseRange (fun a : A => π.1 a ξ)) (ω : A →ₚ[ℂ] ℂ)
    {K : ℝ} (hK : 0 ≤ K)
    (hω : ∀ a, ‖π.1 a ξ‖ ^ 2 ≤ (ω (star a * a)).re ∧
      (ω (star a * a)).re ≤ K * ‖π.1 a ξ‖ ^ 2) : SimilarToStar A H π := by
  let e := boundedHomOrbit π ξ
  let g := NaimarkZFC.gnsOrbit ω
  have he : DenseRange e.toLinearMap := hcyc
  have hg : DenseRange g.toLinearMap := NaimarkZFC.gnsOrbit_dense ω
  have hgnorm (a : A) : ‖g a‖ ^ 2 = (ω (star a * a)).re := by
    simp only [g, NaimarkZFC.gnsOrbit_apply, UniformSpace.Completion.norm_coe,
      PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS]
    exact Real.sq_sqrt (ω.map_nonneg (star_mul_self_nonneg a)).1
  have heg (a : A) : ‖e a‖ ≤ 1 * ‖g a‖ := by
    rw [one_mul]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hgnorm]
    exact (hω a).1
  have hge (a : A) : ‖g a‖ ≤ Real.sqrt K * ‖e a‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hK, hgnorm]
    exact (hω a).2
  let W : H →L[ℂ] ω.GNS := g.toLinearMap.extendOfNorm e.toLinearMap
  let L : ω.GNS →L[ℂ] H := e.toLinearMap.extendOfNorm g.toLinearMap
  have hW (a : A) : W (e a) = g a :=
    LinearMap.extendOfNorm_eq he ⟨Real.sqrt K, hge⟩ a
  have hL (a : A) : L (g a) = e a :=
    LinearMap.extendOfNorm_eq hg ⟨1, heg⟩ a
  have hLW : L.comp W = 1 := by
    ext x
    exact he.induction (by
      rintro y ⟨a, rfl⟩
      change L (W (e a)) = e a
      rw [hW, hL]) (isClosed_eq (L.continuous.comp W.continuous) continuous_id) x
  have hWL : W.comp L = 1 := by
    ext x
    exact hg.induction (by
      rintro y ⟨a, rfl⟩
      change W (L (g a)) = g a
      rw [hL, hW]) (isClosed_eq (W.continuous.comp L.continuous) continuous_id) x
  have hinter (a : A) : W.comp (π.1 a) = (ω.gnsStarAlgHom a).comp W := by
    ext x
    change W (π.1 a x) = ω.gnsStarAlgHom a (W x)
    refine he.induction ?_ (isClosed_eq (W.continuous.comp (π.1 a).continuous)
      ((ω.gnsStarAlgHom a).continuous.comp W.continuous)) x
    rintro y ⟨b, rfl⟩
    change W (π.1 a (e b)) = ω.gnsStarAlgHom a (W (e b))
    have heab : π.1 a (e b) = e (a * b) := by simp [e, map_mul, mul_apply_eq_comp]
    rw [heab, hW, hW]
    simp only [g, NaimarkZFC.gnsOrbit_apply, NaimarkZFC.gns_apply_coe]
  obtain ⟨S, _, hS⟩ := quantitative_similarity_of_intertwiner π ω.gnsStarAlgHom W L hLW hWL hinter
  exact ⟨S, hS⟩

/-- Every bounded cyclic representation is similar to a star representation.
The proof uses only the established little Grothendieck estimate and GNS. -/
theorem cyclic_similarity (π : BoundedUnitalHom A H) (ξ : H)
    (hcyc : DenseRange (fun a : A => π.1 a ξ)) : SimilarToStar A H π := by
  let f : A →L[ℂ] (H →L[ℂ] H) := ⟨π.1.toLinearMap, π.2⟩
  obtain ⟨ω, hω⟩ := exists_positive_orbit_sandwich π ξ ((2 * ‖f‖ ^ 4) ^ 2)
    (fun a b hab => list_equal_square_orbit_comparison π (norm_nonneg f)
      (fun a => f.le_opNorm a) a b hab ξ)
  exact similarity_of_cyclic_orbit_sandwich π ξ hcyc ω (sq_nonneg _) hω

end KadisonSimilarity

end

end OAI
