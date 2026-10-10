import OAI.Analysis.MutuallyUnbiased.Cubic.CubicClassification
import OAI.Analysis.MutuallyUnbiased.Fourier.Dichotomy

namespace OAI

noncomputable section

namespace MUB6

theorem FourierZero.permuted_charge {H : CMatrix} (h : FourierZero H)
    (π : Equiv.Perm Coord) : g H (permuteCharge π alpha) = 0 := by
  simpa only [g_row_permutation, Equiv.symm_symm] using h π.symm

/-- The structural deduction from the two exact pair identities. The final
endpoint instantiates these identities with their checked integer certificates. -/
theorem fourier_vanishing_of_pair_certificates {H : CMatrix} (hH : IsHadamard H)
    (hcross : PairCertificateIdentity H qCross) (hsame : PairCertificateIdentity H qSame)
    (hTao : ¬Equivalent H tao) (π : Equiv.Perm Coord) :
    g H (permuteCharge π alpha) = 0 := by
  rcases dichotomy_of_pair_certificates hH hcross hsame with hz | hs
  · exact hz.permuted_charge π
  · exact (hTao (hadamard_square_equivalent_tao hH hs)).elim

end MUB6

end

end OAI
