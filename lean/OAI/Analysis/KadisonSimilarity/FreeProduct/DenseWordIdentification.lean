import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialDihedralColumns

namespace OAI

/-! Normalize a tensor-word endpoint and identify the completed column from dense vectors. -/

noncomputable section
namespace KadisonSimilarity

universe u
section DenseIdentification
variable {E F : Type u} {K H B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : ℕ → Type*} [∀ n, NormedAddCommGroup (J n)]
  [∀ n, InnerProductSpace ℂ (J n)] [∀ n, CompleteSpace (J n)]

omit [CompleteSpace K] [CompleteSpace H] [∀ n, CompleteSpace (J n)] in
/-- Equality on the dense algebra vectors identifies a normalized word
column. The unnormalized endpoint is the one occurring in the raw formula. -/
theorem repeatedWordInclusion_eq_of_dense
    (U : OrthogonalWordLevels (MultiplicityWordSpace J E F) H)
    (n : ℕ) (R : K →ₗᵢ[ℂ] J n) (e : E) (r : F) (c : ℂ)
    (he : ‖c • e‖ = 1) (hr : ‖r‖ = 1)
    (L : K →ₗᵢ[ℂ] H) (VA : B → K) (hdense : DenseRange VA)
    (hword : ∀ b, L (VA b) = c • U.inclusion n
      (hilbertTensorInsert (R (VA b)) (endpointWord e (fun _ : Fin n => r)))) :
    repeatedWordInclusion U n R (c • e) r he hr = L := by
  ext v
  refine hdense.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  rw [repeatedWordInclusion_apply]
  exact (include_scaled_endpoint (U.inclusion n).toContinuousLinearMap
    (R (VA b)) e (fun _ : Fin n => r) c).trans (hword b).symm

end DenseIdentification

end KadisonSimilarity

end

end OAI
