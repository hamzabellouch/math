import OAI.Analysis.OperatorAlgebra.GNSVectorDensity

namespace OAI

/-! Range criteria for a GNS inclusion with a normalized vector formula. -/
noncomputable section
open scoped ComplexOrder Topology
namespace WeakPureInfiniteness

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma normalizedCornerGNSInclusion_gnsVector
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (W : K →ₗᵢ[ℂ] H) (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (z : H)
    (hf : ∀ a, f a = inner ℂ
      (((‖z‖⁻¹ : ℝ) : ℂ) • W.toContinuousLinearMap.adjoint z)
      (π a (((‖z‖⁻¹ : ℝ) : ℂ) • W.toContinuousLinearMap.adjoint z))) (a : A) :
    normalizedCornerGNSInclusion W f π z hf (gnsVector f a) =
      (((‖z‖⁻¹ : ℝ) : ℂ)) • isometricCornerLift W (π a) z :=
  normalizedCornerGNSInclusion_vector W f π z hf a

omit [CompleteSpace H] in
lemma gnsInclusion_fixed_of_vectors (f : A →ₚ[ℂ] ℂ)
    (V : gnsHilbert f →ₗᵢ[ℂ] H) (P : H →L[ℂ] H)
    (c : ℂ) (v : A → H) (hV : ∀ a, V (gnsVector f a) = c • v a)
    (hv : ∀ a, P (v a) = v a) (x : gnsHilbert f) : P (V x) = V x := by
  apply gnsVector_induction_on f x
  · exact isClosed_eq (P.continuous.comp V.continuous) V.continuous
  · intro a
    rw [hV, map_smul, hv]

omit [CompleteSpace H] in
lemma gnsInclusion_range_of_dense_vectors (f : A →ₚ[ℂ] ℂ)
    (V : gnsHilbert f →ₗᵢ[ℂ] H) (P : H →L[ℂ] H)
    (c : ℂ) (hc : c ≠ 0) (v : A → H) (hV : ∀ a, V (gnsVector f a) = c • v a)
    {ι : Type*} (T : ι → H) (hT : DenseRange T) (a : ι → A)
    (hP : ∀ i, P (T i) = v (a i)) (x : H) : P x ∈ Set.range V := by
  have hclosed : IsClosed (Set.range V) := V.isometry.isClosedEmbedding.isClosed_range
  refine hT.induction_on x (hclosed.preimage P.continuous) ?_
  intro i
  refine ⟨c⁻¹ • gnsVector f (a i), ?_⟩
  rw [map_smul, hV, smul_smul, inv_mul_cancel₀ hc, one_smul, hP]

lemma isometricCornerProjection_eq_of_range
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : K →ₗᵢ[ℂ] H) (P : H →L[ℂ] H) (hP : IsStarProjection P)
    (hV : ∀ x, P (V x) = V x) (hR : ∀ x, P x ∈ Set.range V) :
    P = isometricCornerProjection V := by
  let Q := isometricCornerProjection V
  have hQ : IsStarProjection Q := isometricCornerProjection_isStarProjection V
  have h₁ : P * Q = Q := by
    apply ContinuousLinearMap.ext
    intro x
    exact hV _
  have h₂ : Q * P = P := by
    apply ContinuousLinearMap.ext
    intro x
    obtain ⟨y, hy⟩ := hR x
    change Q (P x) = P x
    rw [← hy]
    exact isometricCornerProjection_inclusion V y
  have h₃ : P * Q = P := by
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq]
      using congrArg star h₂
  exact h₃.symm.trans h₁

end WeakPureInfiniteness

end

end OAI
