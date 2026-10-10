import OAI.Analysis.KadisonKastler.ModularProductTest
import OAI.Analysis.KadisonKastler.IsometryGraphShift

namespace OAI

/-! # The centered test is preserved by the remote graph shifts -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem centeredTest_decomposition (a : Algebra M) :
    modularCenteredTest d a = (star a*a).val*d.rightAction 1 -
      (star a).val*d.rightAction (star a) - a.val*d.rightAction a := by
  change star (a.val-d.rightAction (star a))*(a.val-d.rightAction (star a))-
    star (d.rightAction (star a))*d.rightAction (star a)=_
  rw [star_sub,sub_mul,mul_sub,mul_sub,← d.rightAction_star,star_star,
    ← d.rightAction_commute a a,d.rightAction_one,mul_one]
  change (star a.val*a.val-star a.val*d.rightAction (star a))-
    (a.val*d.rightAction a-d.rightAction a*d.rightAction (star a))-
    d.rightAction a*d.rightAction (star a)=_
  simp only [MulMemClass.coe_mul,StarMemClass.coe_star]
  abel

theorem coisometry_centeredTest_tendsto (v : ℕ → Algebra M)
    (hconv : ∀ (a : Algebra M) (η : H),
      Tendsto (fun n => (v n*a*star (v n)).val η) atTop (𝓝 (a.val η)))
    (a : Algebra M) (ζ : H) :
    Tendsto (fun n => inner ℂ (d.rightAction (v n) ζ)
      (modularCenteredTest d a (d.rightAction (v n) ζ))) atTop
      (𝓝 (inner ℂ ζ (modularCenteredTest d a ζ))) := by
  have h1 := d.coisometry_coefficient_tendsto v hconv (star a*a) 1 ζ
  have h2 := d.coisometry_coefficient_tendsto v hconv (star a) (star a) ζ
  have h3 := d.coisometry_coefficient_tendsto v hconv a a ζ
  simpa only [d.centeredTest_decomposition,sub_apply,inner_sub_right] using (h1.sub h2).sub h3

theorem isometry_centeredTest_tendsto (v : ℕ → Algebra M)
    (hconv : ∀ (a : Algebra M) (η : H),
      Tendsto (fun n => (v n*a*star (v n)).val η) atTop (𝓝 (a.val η)))
    (a : Algebra M) (ζ : H) :
    Tendsto (fun n => inner ℂ ((star (v n)).val ζ)
      (modularCenteredTest d a ((star (v n)).val ζ))) atTop
      (𝓝 (inner ℂ ζ (modularCenteredTest d a ζ))) := by
  have h1 := d.isometry_coefficient_tendsto v hconv (star a*a) 1 ζ
  have h2 := d.isometry_coefficient_tendsto v hconv (star a) (star a) ζ
  have h3 := d.isometry_coefficient_tendsto v hconv a a ζ
  simpa only [d.centeredTest_decomposition,sub_apply,inner_sub_right] using (h1.sub h2).sub h3

end ModularConjugationData

end

end KadisonKastler

end OAI
