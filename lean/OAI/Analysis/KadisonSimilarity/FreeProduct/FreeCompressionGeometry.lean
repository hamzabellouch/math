import OAI.Analysis.KadisonSimilarity.Tensor.MultiplicityClassification
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeCompression
import OAI.Analysis.KadisonSimilarity.Representation.Amplification

namespace OAI

/-! The overlap of a small corner with words starting in the other free
factor. The estimate follows from the displayed tensor geometry. -/

noncomputable section
namespace KadisonSimilarity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem norm_hilbertTensorInsert_le (Ω : E) :
    ‖hilbertTensorInsert (H := F) Ω‖ ≤ ‖Ω‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Ω)
  intro x
  rw [norm_hilbertTensorInsert]

/-- The unit vector insertion is an isometry, expressed by its adjoint. -/
theorem hilbertTensorInsert_adjoint_comp (Ω : E) (hΩ : ‖Ω‖ = 1) :
    (hilbertTensorInsert (H := F) Ω).adjoint.comp (hilbertTensorInsert Ω) =
      ContinuousLinearMap.id ℂ F := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((hilbertTensorInsert Ω).adjoint (hilbertTensorInsert Ω x)) =
    inner ℂ y x
  rw [ContinuousLinearMap.adjoint_inner_right, inner_hilbertTensorInsert,
    inner_self_eq_norm_sq_to_K, hΩ]
  simp

/-- Projection onto the chosen first tensor coordinate and a tail subspace. -/
def firstLetterProjection (Ω : E) (Q : F →L[ℂ] F) :
    HilbertTensor E F →L[ℂ] HilbertTensor E F :=
  (hilbertTensorInsert Ω).comp (Q.comp (hilbertTensorInsert Ω).adjoint)

theorem firstLetterProjection_idempotent (Ω : E) (hΩ : ‖Ω‖ = 1)
    (Q : F →L[ℂ] F) (hQ : Q * Q = Q) :
    firstLetterProjection Ω Q * firstLetterProjection Ω Q = firstLetterProjection Ω Q := by
  let J := hilbertTensorInsert (H := F) Ω
  have hJ : J.adjoint.comp J = ContinuousLinearMap.id ℂ F :=
    hilbertTensorInsert_adjoint_comp Ω hΩ
  change (J.comp (Q.comp J.adjoint)).comp (J.comp (Q.comp J.adjoint)) =
    J.comp (Q.comp J.adjoint)
  have heq : (J.comp (Q.comp J.adjoint)).comp (J.comp (Q.comp J.adjoint)) =
      J.comp ((Q.comp (J.adjoint.comp J)).comp (Q.comp J.adjoint)) := by
    simp only [ContinuousLinearMap.comp_assoc]
  rw [heq, hJ, ContinuousLinearMap.comp_id, ← ContinuousLinearMap.comp_assoc Q Q]
  change J.comp ((Q * Q).comp J.adjoint) = _
  rw [hQ]

theorem firstLetterProjection_adjoint (Ω : E) (Q : F →L[ℂ] F)
    (hQ : Q.adjoint = Q) :
    (firstLetterProjection Ω Q).adjoint = firstLetterProjection Ω Q := by
  simp only [firstLetterProjection, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hQ, ContinuousLinearMap.comp_assoc]

/-- Multiplication in the first factor only sees the small vector `eΩ` on
the range of the first-letter projection. -/
theorem norm_corner_firstLetterProjection_le
    (Ω eΩ : E) (hΩ : ‖Ω‖ = 1) (Q : F →L[ℂ] F) (hQ : ‖Q‖ ≤ 1)
    (e : HilbertTensor E F →L[ℂ] HilbertTensor E F)
    (hact : ∀ x : F, e (hilbertTensorInsert Ω x) = hilbertTensorInsert eΩ x) :
    ‖e * firstLetterProjection Ω Q‖ ≤ ‖eΩ‖ := by
  let J := hilbertTensorInsert (H := F) Ω
  have hJ : ‖J‖ ≤ 1 := by simpa only [J, hΩ] using norm_hilbertTensorInsert_le (F := F) Ω
  have hEJ : ‖e.comp J‖ ≤ ‖eΩ‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg eΩ)
    intro x
    change ‖e (hilbertTensorInsert Ω x)‖ ≤ _
    rw [hact, norm_hilbertTensorInsert]
  change ‖e.comp (J.comp (Q.comp J.adjoint))‖ ≤ _
  rw [← ContinuousLinearMap.comp_assoc]
  calc
    _ ≤ ‖e.comp J‖ * ‖Q.comp J.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖eΩ‖ * (‖Q‖ * ‖J.adjoint‖) :=
      mul_le_mul hEJ (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg _) (norm_nonneg _)
    _ ≤ ‖eΩ‖ * (1 * 1) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      gcongr
    _ = ‖eΩ‖ := by ring

/-- The tracial vector identity gives the square-root overlap in both orders. -/
theorem norm_corner_overlap_le
    (Ω eΩ : E) (hΩ : ‖Ω‖ = 1) (Q : F →L[ℂ] F)
    (hQ : Q.adjoint = Q) (hQnorm : ‖Q‖ ≤ 1)
    (e : HilbertTensor E F →L[ℂ] HilbertTensor E F) (he : e.adjoint = e)
    (hact : ∀ x : F, e (hilbertTensorInsert Ω x) = hilbertTensorInsert eΩ x)
    {u : ℝ} (hu : 0 ≤ u) (hsq : ‖eΩ‖ ^ 2 = u) :
    ‖e * firstLetterProjection Ω Q‖ ≤ Real.sqrt u ∧
      ‖firstLetterProjection Ω Q * e‖ ≤ Real.sqrt u := by
  have hn : ‖eΩ‖ ≤ Real.sqrt u := by
    nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg u, norm_nonneg eΩ]
  have hleft := (norm_corner_firstLetterProjection_le Ω eΩ hΩ Q hQnorm e hact).trans hn
  refine ⟨hleft, ?_⟩
  have hadj : (e * firstLetterProjection Ω Q).adjoint = firstLetterProjection Ω Q * e := by
    change (e.comp (firstLetterProjection Ω Q)).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp, firstLetterProjection_adjoint Ω Q hQ, he]
    rfl
  rw [← hadj, ContinuousLinearMap.adjoint.norm_map]
  exact hleft

/-- The free-letter three blocks and the first-coordinate geometry give the
full norm bound for a compressed centered selfadjoint letter. -/
theorem norm_free_compression_from_tensor_geometry
    (Ω eΩ : E) (hΩ : ‖Ω‖ = 1) (Q : F →L[ℂ] F)
    (hQ : Q.adjoint = Q) (hQsq : Q * Q = Q) (hQnorm : ‖Q‖ ≤ 1)
    (e T : HilbertTensor E F →L[ℂ] HilbertTensor E F)
    (he : e.adjoint = e) (hesq : e * e = e)
    (hact : ∀ x : F, e (hilbertTensorInsert Ω x) = hilbertTensorInsert eΩ x)
    {u b₂ : ℝ} (hu : 0 ≤ u) (hsq : ‖eΩ‖ ^ 2 = u) (hb₂ : 0 ≤ b₂)
    (hzero : (1 - firstLetterProjection Ω Q) * T * (1 - firstLetterProjection Ω Q) = 0)
    (hcreate : ‖firstLetterProjection Ω Q * T * (1 - firstLetterProjection Ω Q)‖ ≤ b₂)
    (hannihilate : ‖(1 - firstLetterProjection Ω Q) * T * firstLetterProjection Ω Q‖ ≤ b₂) :
    ‖e * T * e‖ ≤ 2 * Real.sqrt u * b₂ + u * ‖T‖ := by
  have hov := norm_corner_overlap_le Ω eΩ hΩ Q hQ hQnorm e he hact hu hsq
  exact norm_free_compression_le e (firstLetterProjection Ω Q) T
    (firstLetterProjection_idempotent Ω hΩ Q hQsq) hu hb₂
    (norm_projection_le_one e he hesq) hov.1 hov.2 hzero hcreate hannihilate

omit [CompleteSpace F] in
/-- For a selfadjoint free letter the annihilation block is adjoint to the
creation block, so only the latter needs to be estimated. -/
theorem norm_annihilation_eq_creation
    (P T : HilbertTensor E F →L[ℂ] HilbertTensor E F)
    (hP : P.adjoint = P) (hT : T.adjoint = T) :
    ‖(1 - P) * T * P‖ = ‖P * T * (1 - P)‖ := by
  have hs : (P * T * (1 - P)).adjoint = (1 - P) * T * P := by
    change ((P.comp T).comp (1 - P)).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      map_sub, hP, hT]
    rw [ContinuousLinearMap.adjoint_one]
    rfl
  rw [← hs, ContinuousLinearMap.adjoint.norm_map]

/-- The narrow arc has an order-`u` compression solely from the tensor
geometry, the standard creation block, and its scalar moment bounds. -/
theorem norm_narrow_arc_from_tensor_geometry
    (Ω eΩ : E) (hΩ : ‖Ω‖ = 1) (Q : F →L[ℂ] F)
    (hQ : Q.adjoint = Q) (hQsq : Q * Q = Q) (hQnorm : ‖Q‖ ≤ 1)
    (e T : HilbertTensor E F →L[ℂ] HilbertTensor E F)
    (he : e.adjoint = e) (hesq : e * e = e) (hT : T.adjoint = T)
    (hact : ∀ x : F, e (hilbertTensorInsert Ω x) = hilbertTensorInsert eΩ x)
    {u b₂ : ℝ} (hu : 0 ≤ u) (hsq : ‖eΩ‖ ^ 2 = u) (hb₂ : 0 ≤ b₂)
    (hzero : (1 - firstLetterProjection Ω Q) * T * (1 - firstLetterProjection Ω Q) = 0)
    (hcreate : ‖firstLetterProjection Ω Q * T * (1 - firstLetterProjection Ω Q)‖ ≤ b₂)
    (h₂ : b₂ ^ 2 ≤ u) (hnorm : ‖T‖ ≤ 1) :
    ‖e * T * e‖ ≤ 3 * u := by
  have hov := norm_corner_overlap_le Ω eΩ hΩ Q hQ hQnorm e he hact hu hsq
  have hann : ‖(1 - firstLetterProjection Ω Q) * T * firstLetterProjection Ω Q‖ ≤ b₂ := by
    rw [norm_annihilation_eq_creation _ T (firstLetterProjection_adjoint Ω Q hQ) hT]
    exact hcreate
  exact norm_narrow_arc_compression_le e (firstLetterProjection Ω Q) T
    (firstLetterProjection_idempotent Ω hΩ Q hQsq) hu hb₂
    (norm_projection_le_one e he hesq) hov.1 hov.2 hzero hcreate hann h₂ hnorm

end KadisonSimilarity

end

end OAI
