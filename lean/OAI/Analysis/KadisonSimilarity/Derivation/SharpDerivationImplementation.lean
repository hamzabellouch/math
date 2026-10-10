import OAI.Analysis.KadisonSimilarity.Derivation.DerivationDefectSpace
import OAI.Analysis.KadisonSimilarity.Representation.CenteredProjectionNorm

namespace OAI

/-! A factorized derivation has an implementer with half the product norm.
The defect projection can be centered because the two factors have zero product. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem sharp_implementation_of_factorization
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (π : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (U : K →L[ℂ] H) (W : H →L[ℂ] K) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = (σ a).comp (δ b) + (δ a).comp (σ b))
    (hF : ∀ a, U.comp ((π a).comp W) = δ a) (hUW : U.comp W = 0) :
    ∃ V : H →L[ℂ] H, (∀ a, δ a = V.comp (σ a) - (σ a).comp V) ∧
      ‖V‖ ≤ ‖U‖ * ‖W‖ / 2 := by
  let Q := derivationDefectSpace σ π W
  let P := Q.toSubmodule.starProjection
  have hP : IsStarProjection P := isStarProjection_starProjection (U := Q.toSubmodule)
  have hmem (x : K) : P x ∈ Q := Q.toSubmodule.starProjection_apply_mem x
  have hcomm (a : A) : Commute P (π a) :=
    orthogonal_projection_commutes π (fun a => π.map_star' a) Q
      (fun a x hx => derivationDefectSpace_invariant σ π W a x hx) a
  have hfix (a : A) (x : H) : P (derivationDefect σ π W a x) =
      derivationDefect σ π W a x :=
    Q.toSubmodule.starProjection_eq_self_iff.mpr (derivationDefect_mem σ π W a x)
  have hUd (a : A) : U.comp (derivationDefect σ π W a) = δ a := by
    simp only [derivationDefect, ContinuousLinearMap.comp_sub,
      ← ContinuousLinearMap.comp_assoc, hUW, ContinuousLinearMap.zero_comp, sub_zero]
    exact hF a
  let Z : H →L[ℂ] H := U.comp (P.comp W)
  have himpl (a : A) : δ a = (σ a).comp Z - Z.comp (σ a) := by
    ext x
    have hd := congrArg (fun T : H →L[ℂ] H => T x) (hUd a)
    change U (derivationDefect σ π W a x) = δ a x at hd
    have hc := congrArg (fun T : K →L[ℂ] K => T (W x)) (hcomm a).eq
    change P (π a (W x)) = π a (P (W x)) at hc
    calc
      δ a x = U (P (derivationDefect σ π W a x)) := by rw [hfix]; exact hd.symm
      _ = U (P (π a (W x))) - U (P (W (σ a x))) := by
        simp only [derivationDefect, _root_.sub_apply, ContinuousLinearMap.comp_apply, map_sub]
      _ = U (π a (P (W x))) - U (P (W (σ a x))) := by rw [hc]
      _ = σ a (U (P (W x))) - U (P (W (σ a x))) := by
        rw [derivationDefectSpace_intertwines σ π U W δ hδ hF hUW a _ (hmem (W x))]
      _ = ((σ a).comp Z - Z.comp (σ a)) x := rfl
  have hcenter : Z = U.comp ((P - (1 / 2 : ℝ) • 1).comp W) := by
    ext x
    have hz := congrArg (fun T : H →L[ℂ] H => T x) hUW
    change U (W x) = 0 at hz
    change U (P (W x)) = U ((P - (1 / 2 : ℝ) • 1) (W x))
    simp only [_root_.sub_apply, _root_.smul_apply, one_apply_eq_self, map_sub]
    rw [U.map_smul_of_tower (1 / 2 : ℝ), hz, smul_zero, sub_zero]
  have hnorm : ‖Z‖ ≤ ‖U‖ * ‖W‖ / 2 := by
    rw [hcenter]
    calc
      _ ≤ ‖U‖ * ‖(P - (1 / 2 : ℝ) • 1).comp W‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖U‖ * (‖P - (1 / 2 : ℝ) • 1‖ * ‖W‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ ‖U‖ * ((1 / 2 : ℝ) * ‖W‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (norm_projection_sub_half_le P hP) (norm_nonneg _))
          (norm_nonneg _)
      _ = ‖U‖ * ‖W‖ / 2 := by ring
  refine ⟨-Z, ?_, by simpa only [norm_neg] using hnorm⟩
  intro a
  rw [himpl]
  ext x
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, neg_apply, map_neg]
  abel

end KadisonSimilarity

end

end OAI
