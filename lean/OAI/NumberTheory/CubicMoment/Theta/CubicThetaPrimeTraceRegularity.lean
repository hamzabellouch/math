import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeTraceSection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeC1Energy

namespace OAI

/-! First differentiability of the actual finite trace. The expression
is the finite sum of the geometric sheet pullbacks with their cubic phases. -/
noncomputable section
open Set
namespace CubicFirstMoment

local instance primeTraceRegularity_fintype {p : Eisenstein} (hp : primaryPrime p) :
    Fintype (cubicThetaPrimeTransversal hp) := Fintype.ofFinite _

lemma cubicThetaPrimeTraceSection_function {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaSectionFunction (cubicThetaPrimeTraceSection hp F) y=
      ∑ t : cubicThetaPrimeTransversal hp, star (cubicThetaKubotaValue t.val)*
        cubicThetaPrimeSectionFunction hp F (cubicThetaMobius (cubicThetaPrincipalComplex t.val) y) := by
  rw [cubicThetaSectionFunction_apply _ hy]
  change (∑ t : cubicThetaPrimeTransversal hp, cubicThetaPrimeTraceTerm hp F t.val ⟨y,hy⟩)=_
  apply Finset.sum_congr rfl
  intro t _
  rw [cubicThetaPrimeSectionFunction_apply hp F (cubicThetaMobius_height_pos _ hy)]
  rfl

lemma cubicThetaPrimeTraceSection_c1 {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeC1Sections hp) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (cubicThetaPrimeTraceSection hp F.val))
      {y : ℂ × ℝ | 0<y.2} := by
  have ht (t : cubicThetaPrimeTransversal hp) :
      ContDiffOn ℝ 1 (fun y => star (cubicThetaKubotaValue t.val)*
        cubicThetaPrimeSectionFunction hp F.val (cubicThetaMobius (cubicThetaPrincipalComplex t.val) y))
        {y : ℂ × ℝ | 0<y.2} := by
    have hm : ContDiffOn ℝ 1 (cubicThetaMobius (cubicThetaPrincipalComplex t.val))
        {y : ℂ × ℝ | 0<y.2} := fun _ hy =>
      ((cubicThetaMobius_contDiffAt _ hy).of_le (by simp)).contDiffWithinAt
    exact contDiffOn_const.mul (F.property.comp hm (fun _ hy => cubicThetaMobius_height_pos _ hy))
  exact (ContDiffOn.sum (fun t _ => ht t)).congr
    (fun _ hy => cubicThetaPrimeTraceSection_function hp F.val hy)

end CubicFirstMoment

end

end OAI
