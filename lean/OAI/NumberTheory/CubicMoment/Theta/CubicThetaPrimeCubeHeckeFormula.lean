import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeValuationSum
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeOppositeBranch
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeResidueComplement

namespace OAI

/-! The literal four-branch cubed-prime Hecke formula for actual cubic
automorphic sections, with the two intermediate cubic-character sums. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeBranchSum {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (F : CubicThetaSection) (x : CubicThetaPoint) : ℂ :=
  ∑' u : (Residues (p^(3-k.val)))ˣ,
    (cubicSymbol p (3*residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))))^k.val*
      F.val (cubicThetaPrimeCubeBranchPoint hp k
        (residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))) x)

def cubicThetaPrimeCubeFullBottomSum {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) : ℂ :=
  ∑' r : Residues (p^3), F.val (cubicThetaPrimeCubeBranchPoint hp 0 (residueRepresentative (p^3) r) x)

lemma cubicThetaPrimeCubeBranchSum_lower {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' u : (Residues (p^(3-k.val)))ˣ,cubicThetaPrimeCubeLowerValue hp F x
      (p^k.val*residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))))=
        cubicThetaPrimeCubeBranchSum hp k F x :=
  cubicThetaPrimeCubeUnitBranch hp k F x

lemma cubicThetaPrimeCubeBranchSum_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' u : (Residues (p^3))ˣ,cubicThetaPrimeCubeLowerValue hp F x
      (residueRepresentative (p^3) (u : Residues (p^3))))=
        cubicThetaPrimeCubeBranchSum hp 0 F x := by
  simpa only [cubicThetaPrimeCubeLowerValue,cubicThetaPrimeCubeBranchSum,
    Fin.val_zero,Nat.sub_zero,pow_zero,one_mul] using cubicThetaPrimeCubeUnitBranch hp 0 F x

lemma cubicThetaPrimeCubeBranchSum_one {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' u : (Residues (p^2))ˣ,cubicThetaPrimeCubeLowerValue hp F x
      (p*residueRepresentative (p^2) (u : Residues (p^2))))=
        cubicThetaPrimeCubeBranchSum hp 1 F x := by
  simpa only [cubicThetaPrimeCubeLowerValue,cubicThetaPrimeCubeBranchSum,
    Fin.val_one,Nat.reduceSub,pow_one] using cubicThetaPrimeCubeUnitBranch hp 1 F x

lemma cubicThetaPrimeCubeBranchSum_two {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' u : (Residues p)ˣ,cubicThetaPrimeCubeLowerValue hp F x
      (p^2*residueRepresentative p (u : Residues p)))=
        cubicThetaPrimeCubeBranchSum hp (⟨2,by decide⟩ : Fin 3) F x := by
  calc
    _ = ∑' u : (Residues (p^1))ˣ,cubicThetaPrimeCubeLowerValue hp F x
        (p^2*residueRepresentative (p^1) (u : Residues (p^1))) := by
      exact (congrArg (fun q : Eisenstein => ∑' u : (Residues q)ˣ,
        cubicThetaPrimeCubeLowerValue hp F x (p^2*residueRepresentative q (u : Residues q)))
          (pow_one p)).symm
    _ = _ := by
      with_reducible_and_instances exact
        cubicThetaPrimeCubeBranchSum_lower hp (⟨2,by decide⟩ : Fin 3) F x

lemma cubicThetaPrimeCubeLowerValue_branches {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' r : Residues (p^3),cubicThetaPrimeCubeLowerValue hp F x (residueRepresentative (p^3) r))=
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)+
        cubicThetaPrimeCubeBranchSum hp 0 F x+cubicThetaPrimeCubeBranchSum hp 1 F x+
          cubicThetaPrimeCubeBranchSum hp (⟨2,by decide⟩ : Fin 3) F x := by
  rw [cubicThetaPrimeCubeLowerValue_sum,cubicThetaPrimeCubeLowerValue_zero,
    cubicThetaPrimeCubeBranchSum_zero,cubicThetaPrimeCubeBranchSum_one,
    cubicThetaPrimeCubeBranchSum_two]

lemma cubicThetaPrimeCubeBottomValue_split {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeFullBottomSum hp F x=cubicThetaPrimeCubeBranchSum hp 0 F x+
      ∑' r : cubicThetaPrimeCubeUpperParameter p,
        F.val (cubicThetaPrimeCubeBranchPoint hp 0 (residueRepresentative (p^3) r.val) x) := by
  simpa only [cubicThetaPrimeCubeFullBottomSum,cubicThetaPrimeCubeBranchSum,
    Fin.val_zero,Nat.sub_zero,pow_zero,one_mul] using
      cubicThetaPrimeCubeResidueComplement_sum hp
        (fun r => F.val (cubicThetaPrimeCubeBranchPoint hp 0 (residueRepresentative (p^3) r) x))

theorem cubicThetaPrimeCubeHecke_fourBranches {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeCubeHecke hp F).val x=
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)+
        cubicThetaPrimeCubeFullBottomSum hp F x+
        cubicThetaPrimeCubeBranchSum hp 1 F x+cubicThetaPrimeCubeBranchSum hp (⟨2,by decide⟩ : Fin 3) F x := by
  have hu : (∑' r : cubicThetaPrimeCubeUpperParameter p,
      star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
          (cubicThetaPrimeCubeUpperRepresentative hp r • x)))=
      ∑' r : cubicThetaPrimeCubeUpperParameter p,
        F.val (cubicThetaPrimeCubeBranchPoint hp 0 (residueRepresentative (p^3) r.val) x) :=
    tsum_congr (cubicThetaPrimeCubeUpperBranch hp F x)
  rw [cubicThetaPrimeCubeHecke_expansion,hu,cubicThetaPrimeCubeBottomValue_split]
  change (∑' r : Residues (p^3),cubicThetaPrimeCubeLowerValue hp F x
    (residueRepresentative (p^3) r))+_= _
  rw [cubicThetaPrimeCubeLowerValue_branches]
  ring

end CubicFirstMoment

end

end OAI
