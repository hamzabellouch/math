import OAI.Analysis.MassAction.CanonicalLocalConstructor
import OAI.Analysis.MassAction.AffineCertificateGluing

namespace OAI

noncomputable section

namespace Problem326.Affine

/-- Full arbitrary-tolerance affine approximation, with both the dimension
induction and the finite interval gluing discharged. -/
theorem fullCertificate_exists :
    ∀ d : ℕ, ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) →
      Nonempty (FullCertificate d a b E) :=
  fullCertificate_of_local_constructor localCertificate_of_lower_fullCertificates

end Problem326.Affine

end

end OAI
