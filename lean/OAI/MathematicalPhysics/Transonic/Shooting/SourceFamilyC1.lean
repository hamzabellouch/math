import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyJets
import OAI.MathematicalPhysics.Transonic.Shooting.FamilyQuotient

namespace OAI

section
noncomputable section

namespace SepticProfile.ParametricJets
open Polynomial FamilyC1
variable {A : Type*} [TopologicalSpace A]

def polynomialC1 (p : Polynomial C(A,ℝ)) :
    Data (fun a v => aeval v.1 (specialize a p)) where
  D := fun a v => aeval v.1 (specialize a p.derivative) • ContinuousLinearMap.fst ℂ ℂ ℂ
  continuous_h := (continuous_aeval_specialize p).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  continuous_D := ((continuous_aeval_specialize p.derivative).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).smul continuous_const
  hasFD := fun a v => by
    simpa only [specialize_derivative,Function.comp_def] using
      ((specialize a p).hasDerivAt_aeval v.1).comp_hasFDerivAt v hasFDerivAt_fst

end SepticProfile.ParametricJets

namespace SepticProfile.SourceFamily
open FamilyC1 ParametricJets Polynomial
open scoped NNReal

 def numerator (J : FamilyJet) (a : Parameter) (v : V) : ℂ :=
  -Remainder.jetE (sig a:ℂ) (kap a:ℂ) (cst a:ℂ) (rho a:ℂ) v.1
    (aeval v.1 (specialize a J.p)) (aeval v.1 (specialize a J.p.derivative))
    (aeval v.1 (specialize a J.S)) (aeval v.1 (specialize a J.E)) v.2 74
 def denominator (J : FamilyJet) (a : Parameter) (v : V) : ℂ :=
  Remainder.jetA (sig a:ℂ) v.1 (aeval v.1 (specialize a J.p))
    (aeval v.1 (specialize a J.p1)) v.2 74
 def H (J : FamilyJet) (a : Parameter) (v : V) : ℂ := numerator J a v/denominator J a v

 def numeratorC1 (J : FamilyJet) : Data (numerator J) := by
  unfold numerator Remainder.jetE Remainder.quad Remainder.pref Remainder.trans
    Remainder.amp Remainder.denDiff
  repeat' first
    | exact Data.fst
    | exact Data.snd
    | exact polynomialC1 _
    | apply Data.const; fun_prop
    | apply Data.neg
    | apply Data.add
    | apply Data.sub
    | apply Data.mul

 def denominatorC1 (J : FamilyJet) : Data (denominator J) := by
  unfold denominator Remainder.jetA Remainder.denQuot Remainder.pref Remainder.denDiff
  repeat' first
    | exact Data.fst
    | exact Data.snd
    | exact polynomialC1 _
    | apply Data.const; fun_prop
    | apply Data.neg
    | apply Data.add
    | apply Data.sub
    | apply Data.mul

 lemma denominator_zero_ne (J : FamilyJet) (a : Parameter) : denominator J a 0 ≠ 0 := by
  simp only [denominator,Prod.fst_zero,Prod.snd_zero,Remainder.jetA_zero,
    ← coeff_zero_eq_aeval_zero',coeff_specialize,J.p1_zero]
  have hd := ShootingParameters.sonic_divisor_ne a.property
  change 2*(1-sig a)*slp a ≠ 0 at hd
  have hdc : (2:ℂ)*(1-(sig a:ℂ))*(slp a:ℂ) ≠ 0 := by exact_mod_cast hd
  simpa only [Complex.coe_algebraMap,neg_mul] using neg_ne_zero.mpr hdc

 lemma H_sourceH (J : FamilyJet) (a : Parameter) : H J a =
     SourceSonic.sourceH (sig a) (kap a) (cst a) (rho a)
       (specialize a J.p) (specialize a J.p1) (specialize a J.S) (specialize a J.E) 74 := by
  funext v
  simp only [H,numerator,denominator,SourceSonic.sourceH,specialize_derivative]

 theorem uniform_bounds (J : FamilyJet) :
    ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ≥0, ∃ M : ℝ, 0 ≤ M ∧
      (∀ a v, v ∈ Metric.closedBall 0 R → denominator J a v ≠ 0) ∧
      (∀ a, DifferentiableOn ℂ (H J a) (Metric.closedBall 0 R)) ∧
      (∀ a, LipschitzOnWith K (H J a) (Metric.closedBall 0 R)) ∧
      Continuous (fun p : Parameter × ↥(Metric.closedBall (0:V) R) => H J p.1 p.2) ∧
      ∀ a, ‖H J a 0‖ ≤ M :=
  exists_uniform_quotient_bounds (numeratorC1 J) (denominatorC1 J) (denominator_zero_ne J)

end SepticProfile.SourceFamily

end
end

end OAI
