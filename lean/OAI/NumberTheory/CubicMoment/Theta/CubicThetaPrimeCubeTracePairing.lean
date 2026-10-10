import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeAtkinPairing

namespace OAI

/-! The literal cubed-prime trace is adjoint to restriction for actual
square-integrable sections, with the exact unnormalized cover measure. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeTrace_pair_point {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) (G : CubicThetaSection) (x : CubicThetaPoint) :
    star (G.val x)*(cubicThetaPrimeCubeTraceSection hp F).val x=
      ∑' t : cubicThetaPrimeCubeTransversal p,star (G.val (t.val • x))*F.val (t.val • x) := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  change star (G.val x)*(∑' t : cubicThetaPrimeCubeTransversal p,
    cubicThetaPrimeCubeTraceTerm p F t.val x)=_
  rw [tsum_fintype,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [G.property,star_mul,cubicThetaPrimeCubeTraceTerm]
  ring

theorem cubicThetaPrimeCubeTrace_pairing {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) (G : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hG : IntegrableOn (fun x => ‖G.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,
      star (G.val x)*(cubicThetaPrimeCubeTraceSection hp F).val x ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,star (G.val x)*F.val x ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have hGc := cubicThetaPrimeCubeInvariant_integrable hp hG (cubicThetaOriginal_norm_invariant G)
  have hi := cubicThetaSquareIntegrablePair G.val F.val G.val.continuous F.val.continuous hGc hF
  simp_rw [cubicThetaPrimeCubeTrace_pair_point,tsum_fintype]
  rw [integral_finsetSum Finset.univ (fun t _ => cubicThetaPrimeCubeComplexSheet_integrable hp hi t),
    cubicThetaPrimeCubeComplexSheetIntegral hp hi,tsum_fintype]

end CubicFirstMoment

end

end OAI
