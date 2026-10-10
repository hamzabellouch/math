import OAI.Analysis.MassAction.AffineCertificates
import OAI.Analysis.MassAction.FixedMinimumCertificate

namespace OAI

noncomputable section
open Filter Topology

namespace Problem326.Affine

theorem localCertificate_of_label_certificates {d : ℕ}
    {Λ : Finset (Label d)} {a b t : ℝ} {E : (Fin d → ℝ) → ℝ}
    (hbaseline : constantLabel d t ∈ Λ)
    (hslopes : ∀ L ∈ Λ, Cube t b L.slope)
    (hminima : ∀ L ∈ Λ, HasMinimum L.slope t)
    (hcert : ∀ L ∈ Λ, FixedMinimumLabelCertificate Λ a b t E L) :
    Nonempty (LocalCertificate d a b t E) := by
  obtain ⟨η, hη, hoff⟩ := exists_common_offset_decay hcert
  exact ⟨{
    labels := Λ
    baseline := hbaseline
    slopes := hslopes
    minima := hminima
    decayExponent := η
    decay_gt := hη
    offsets := hoff
    approximation := approximatesAtMinimum_of_certificates hbaseline hcert
  }⟩

end Problem326.Affine

end

end OAI
