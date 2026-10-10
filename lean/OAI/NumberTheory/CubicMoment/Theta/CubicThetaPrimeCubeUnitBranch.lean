import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeUnitPermutation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeBranchPeriodicity

namespace OAI

/-! Exact reindexing of each nonzero valuation branch of the actual
trace into a finite cubic-character-weighted translation sum. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeUnitBranch {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' u : (Residues (p^(3-k.val)))ˣ,
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        (cubicThetaPrincipalLower (p^k.val*
          residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))) • x)))=
      ∑' v : (Residues (p^(3-k.val)))ˣ,
        (cubicSymbol p (3*residueRepresentative (p^(3-k.val)) (v : Residues (p^(3-k.val)))))^k.val*
          F.val (cubicThetaPrimeCubeBranchPoint hp k
            (residueRepresentative (p^(3-k.val)) (v : Residues (p^(3-k.val)))) x) := by
  let T := fun v : (Residues (p^(3-k.val)))ˣ =>
    (cubicSymbol p (3*residueRepresentative (p^(3-k.val)) (v : Residues (p^(3-k.val)))))^k.val*
      F.val (cubicThetaPrimeCubeBranchPoint hp k
        (residueRepresentative (p^(3-k.val)) (v : Residues (p^(3-k.val)))) x)
  calc
    _ = ∑' u : (Residues (p^(3-k.val)))ˣ, T (cubicThetaPrimeCubeUnitPermutation hp k u) := by
      apply tsum_congr
      intro u
      let n := residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))
      have hn := cubicThetaPrimeCubeUnitRepresentative_not_dvd hp k u
      rw [cubicThetaPrimeCubeBranch_section hp k n hn]
      apply cubicThetaPrimeCubeBranch_term_congr hp
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq.mp
      exact (cubicThetaPrimeCubeUnitTranslation_residue hp k u).trans
        (residueRepresentative_spec _ _).symm
    _ = _ := (cubicThetaPrimeCubeUnitPermutation hp k).tsum_eq T

end CubicFirstMoment

end

end OAI
