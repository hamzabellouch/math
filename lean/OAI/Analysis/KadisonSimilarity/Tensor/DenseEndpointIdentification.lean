import OAI.Analysis.KadisonSimilarity.FreeProduct.DenseWordIdentification

namespace OAI

/-! A named normalized endpoint can be identified before instantiating the
dense-word equality. This avoids unfolding its Hilbert-space construction. -/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u} {K H B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {J : ℕ → Type*} [∀ n, NormedAddCommGroup (J n)]
  [∀ n, InnerProductSpace ℂ (J n)]

/-- Use a proved endpoint identity while keeping its normed-space data opaque. -/
theorem repeatedWordInclusion_eq_of_dense_endpoint
    (U : OrthogonalWordLevels (MultiplicityWordSpace J E F) H)
    (n : ℕ) (R : K →ₗᵢ[ℂ] J n) (d e : E) (r : F) (c : ℂ)
    (hd : ‖d‖ = 1) (hr : ‖r‖ = 1) (heq : d = c • e)
    (L : K →ₗᵢ[ℂ] H) (VA : B → K) (hdense : DenseRange VA)
    (hword : ∀ b, L (VA b) = c • U.inclusion n
      (hilbertTensorInsert (R (VA b)) (endpointWord e (fun _ : Fin n => r)))) :
    repeatedWordInclusion U n R d r hd hr = L := by
  subst d
  exact repeatedWordInclusion_eq_of_dense U n R e r c hd hr L VA hdense hword

end KadisonSimilarity

end

end OAI
