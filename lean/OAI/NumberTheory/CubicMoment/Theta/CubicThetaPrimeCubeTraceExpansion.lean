import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeChartEquiv

namespace OAI

/-! The cubed-prime trace as two explicit finite sums. Both the actual
integral representatives and their Kubota phases are retained. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeTraceSection_expansion {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) (x : CubicThetaPoint) :
    (cubicThetaPrimeCubeTraceSection hp F).val x=
      (∑' r : Residues (p^3),
        F.val (cubicThetaPrincipalLower (residueRepresentative (p^3) r) • x))+
      (∑' r : cubicThetaPrimeCubeUpperParameter p,
        star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
          F.val (cubicThetaPrimeCubeUpperRepresentative hp r • x)) := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Finite (cubicThetaPrimeCubeUpperParameter p) := by
    unfold cubicThetaPrimeCubeUpperParameter
    infer_instance
  change (∑' t : cubicThetaPrimeCubeTransversal p,cubicThetaPrimeCubeTraceTerm p F t.val x)=_
  rw [←(cubicThetaPrimeCubeChartEquiv hp).tsum_eq,
    Summable.tsum_sum Summable.of_finite Summable.of_finite]
  congr 1
  · apply tsum_congr
    intro r
    change cubicThetaPrimeCubeTraceTerm p F
      (cubicThetaPrimeCubeCoset p (cubicThetaPrincipalLower (residueRepresentative (p^3) r))).val x=_
    rw [cubicThetaPrimeCubeTraceTerm_coset]
    simp only [cubicThetaPrimeCubeTraceTerm,cubicThetaPrincipalLower_value,star_one,one_mul]
  · apply tsum_congr
    intro r
    change cubicThetaPrimeCubeTraceTerm p F
      (cubicThetaPrimeCubeCoset p (cubicThetaPrimeCubeUpperRepresentative hp r)).val x=_
    rw [cubicThetaPrimeCubeTraceTerm_coset]
    simp only [cubicThetaPrimeCubeTraceTerm,cubicThetaPrimeCubeUpperRepresentative,
      cubicThetaKubotaValue_mul,cubicThetaPrincipalTranslation_value,mul_one]

theorem cubicThetaPrimeCubeHecke_expansion {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeCubeHecke hp F).val x=
      (∑' r : Residues (p^3), F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        (cubicThetaPrincipalLower (residueRepresentative (p^3) r) • x)))+
      (∑' r : cubicThetaPrimeCubeUpperParameter p,
        star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
          F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
            (cubicThetaPrimeCubeUpperRepresentative hp r • x))) :=
  cubicThetaPrimeCubeTraceSection_expansion hp (cubicThetaPrimeCubeDilationSection hp F) x

end CubicFirstMoment

end

end OAI
