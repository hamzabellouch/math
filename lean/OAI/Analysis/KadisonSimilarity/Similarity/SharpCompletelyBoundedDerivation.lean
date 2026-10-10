import OAI.Analysis.KadisonSimilarity.Derivation.SharpDerivationImplementation
import OAI.Analysis.KadisonSimilarity.Similarity.PaulsenDischarge

namespace OAI

/-! The sharp implementation bound for completely bounded derivations,
using the proved completely bounded factorization. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
theorem derivation_map_one_eq_zero
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = (σ a).comp (δ b) + (δ a).comp (σ b)) : δ 1 = 0 := by
  have h := hδ 1 1
  simp only [one_mul, map_one, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] at h
  have hz : δ 1 + 0 = δ 1 + δ 1 := by simpa only [add_zero] using h
  exact (add_left_cancel hz).symm

theorem sharp_implementation_of_complete_bound
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = (σ a).comp (δ b) + (δ a).comp (σ b))
    {C : ℝ} (hC : 0 < C)
    (hcb : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map δ.toLinearMap‖ ≤ C * ‖X‖) :
    ∃ V : H →L[ℂ] H, (∀ a, δ a = V.comp (σ a) - (σ a).comp V) ∧ ‖V‖ ≤ C / 2 := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    refine ⟨0, fun _ => Subsingleton.elim _ _, ?_⟩
    simpa only [norm_zero] using (div_nonneg hC.le (by norm_num : (0 : ℝ) ≤ 2))
  · let := hH
    have h01 : (0 : A) ≠ 1 := by
      intro h
      have he := congrArg σ h
      exact zero_ne_one (by simpa only [map_zero, map_one] using he)
    let : Nontrivial A := ⟨⟨0, 1, h01⟩⟩
    obtain ⟨F⟩ := BoundedHochschild.KadisonRingrose.factorization_of_complete_bound
      δ.toLinearMap hC hcb
    have hUW : F.leftMap.adjoint.comp F.rightMap = 0 := by
      have h := F.factorization 1
      change δ 1 = F.leftMap.adjoint.comp ((F.representation 1).comp F.rightMap) at h
      rw [derivation_map_one_eq_zero σ δ hδ] at h
      simpa only [map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using h.symm
    obtain ⟨V, hV, hn⟩ := sharp_implementation_of_factorization σ F.representation
      F.leftMap.adjoint F.rightMap δ hδ (fun a => (F.factorization a).symm) hUW
    refine ⟨V, hV, hn.trans ?_⟩
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simpa only [ContinuousLinearMap.adjoint.norm_map] using F.bound

end KadisonSimilarity

end

end OAI
