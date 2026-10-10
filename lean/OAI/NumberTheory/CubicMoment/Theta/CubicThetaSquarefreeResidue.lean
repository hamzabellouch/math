import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWeightedResidue

namespace OAI

/-! Prime coefficient relations determine every primary squarefree
coefficient, retaining its one scalar base residue explicitly. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaWeightedFourierResidue_squarefree {b : Eisenstein}
    (hb : primary b) (hs : Squarefree b) :
    cubicThetaWeightedFourierResidue b=
      star (gauss b)/(Real.sqrt (norm b):ℂ)*cubicThetaWeightedFourierResidue 1 := by
  revert hs
  refine primary_induction (P:=fun b => Squarefree b →
    cubicThetaWeightedFourierResidue b=
      star (gauss b)/(Real.sqrt (norm b):ℂ)*cubicThetaWeightedFourierResidue 1) ?_ ?_ hb
  · intro _
    simp only [gauss_one,star_one,norm_one_eq,Real.sqrt_one,Complex.ofReal_one,div_one,one_mul]
  · intro p b hp hb ih hs
    have hc : IsCoprime p b := isRelPrime_iff_isCoprime.mp (IsRelPrime.of_squarefree_mul hs)
    have hpb : ¬p∣b := hp.2.coprime_iff_not_dvd.mp hc
    rw [cubicThetaWeightedFourierResidue_prime hp b hpb,ih hs.of_mul_right,
      gauss_mul hp.1 hb,star_mul,star_mul,star_star,cubic_reciprocity hb hp.1,
      norm_mul_eq,Real.sqrt_mul (norm_nonneg p),Complex.ofReal_mul]
    ring

end CubicFirstMoment

end

end OAI
