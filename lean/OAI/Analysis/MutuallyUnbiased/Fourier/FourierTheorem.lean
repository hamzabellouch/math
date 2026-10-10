import OAI.Analysis.MutuallyUnbiased.PairTargets.Main
import OAI.Analysis.MutuallyUnbiased.PairMoments.PairInterpretation
import OAI.Analysis.MutuallyUnbiased.Fourier.FourierEndpoint

namespace OAI

noncomputable section

namespace MUB6

theorem pair_cross_certificate {H : CMatrix} (hH : IsHadamard H) :
    PairCertificateIdentity H qCross := by
  unfold PairCertificateIdentity
  rw [← Certificate.PairTargetSemantics.expanded_identity0 hH]
  exact Certificate.PairTargetSemantics.certificate_zero0 hH

theorem pair_same_certificate {H : CMatrix} (hH : IsHadamard H) :
    PairCertificateIdentity H qSame := by
  unfold PairCertificateIdentity
  rw [← Certificate.PairTargetSemantics.expanded_identity1 hH]
  exact Certificate.PairTargetSemantics.certificate_zero1 hH

/-- The exact pair certificates imply the manuscript's complete dichotomy. -/
theorem exact_dichotomy {H : CMatrix} (hH : IsHadamard H) :
    FourierZero H ∨ IsHadamard (fun i j => H i j ^ 2) :=
  dichotomy_of_pair_certificates hH (pair_cross_certificate hH) (pair_same_certificate hH)

/-- Endpoint 1: arbitrary complex entries, full Hadamard equivalence, and the
manuscript's normalized Fourier coefficient for every permuted alpha. -/
theorem fourier_vanishing {H : CMatrix} (hH : IsHadamard H)
    (hTao : ¬Equivalent H tao) (π : Equiv.Perm Coord) :
    g H (permuteCharge π alpha) = 0 :=
  fourier_vanishing_of_pair_certificates hH
    (pair_cross_certificate hH) (pair_same_certificate hH) hTao π

end MUB6

end

end OAI
