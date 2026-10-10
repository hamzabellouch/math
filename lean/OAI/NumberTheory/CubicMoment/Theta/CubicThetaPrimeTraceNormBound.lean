import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeEnergyDomainNorm
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeTraceLinear
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeSheetIntegral

namespace OAI

/-! The finite trace has operator norm at most the square root of the
covering degree, separately for actual mass and derivative energy. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

local instance primeTraceNorm_fintype {p : Eisenstein} (hp : primaryPrime p) :
    Fintype (cubicThetaPrimeTransversal hp) := Fintype.ofFinite _

lemma cubicThetaPrimeTraceSection_norm_sq_le {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (x : CubicThetaPoint) :
    ‖(cubicThetaPrimeTraceSection hp F).val x‖^2≤
      ((cubicThetaPrimeCoverGroup hp).index:ℝ)*
        ∑ t : cubicThetaPrimeTransversal hp, ‖F.val (t.val • x)‖^2 := by
  have hn := norm_sum_le Finset.univ (fun t : cubicThetaPrimeTransversal hp =>
    cubicThetaPrimeTraceTerm hp F t.val x)
  have ht (t : cubicThetaPrimeTransversal hp) :
      ‖cubicThetaPrimeTraceTerm hp F t.val x‖=‖F.val (t.val • x)‖ := by
    rw [cubicThetaPrimeTraceTerm,norm_mul,norm_star,cubicThetaKubotaValue_norm,one_mul]
  simp_rw [ht] at hn
  have hs := mul_self_le_mul_self (_root_.norm_nonneg _) hn
  rw [←pow_two,←pow_two] at hs
  apply hs.trans
  have hsum := sq_sum_le_card_mul_sum_sq (s:=Finset.univ)
    (f:=fun t : cubicThetaPrimeTransversal hp => ‖F.val (t.val • x)‖)
  rwa [Finset.card_univ,←Nat.card_eq_fintype_card,
    (cubicThetaPrimeTransversal_complement hp).card_right] at hsum

def cubicThetaPrimeTraceMassMajorant {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteSections hp) (x : CubicThetaPoint) : ℝ :=
  ((cubicThetaPrimeCoverGroup hp).index:ℝ)*
    ∑ t : cubicThetaPrimeTransversal hp, ‖F.val.val (t.val • x)‖^2

lemma cubicThetaPrimeTraceMassMajorant_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteSections hp) :
    IntegrableOn (cubicThetaPrimeTraceMassMajorant hp F)
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  exact (integrable_finsetSum Finset.univ (fun t _ =>
    (cubicThetaPrimeSheet_memLp hp F t).integrable_norm_pow
      (by norm_num : (2:ℕ)≠0))).const_mul _

lemma cubicThetaPrimeTraceMassMajorant_integral {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteSections hp) :
    (∫ x in cubicThetaFundamentalDomain, cubicThetaPrimeTraceMassMajorant hp F x
      ∂cubicThetaPointMeasure)=
      ((cubicThetaPrimeCoverGroup hp).index:ℝ)*
        ∫ x in cubicThetaPrimeCoverDomain hp, ‖F.val.val x‖^2 ∂cubicThetaPointMeasure := by
  have ht (t : cubicThetaPrimeTransversal hp) :
      IntegrableOn (fun x : CubicThetaPoint => ‖F.val.val (t.val • x)‖^2)
        cubicThetaFundamentalDomain cubicThetaPointMeasure :=
    (cubicThetaPrimeSheet_memLp hp F t).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  unfold cubicThetaPrimeTraceMassMajorant
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun t _ => ht t)]
  have hf := (cubicThetaPrimeSection_memLp_domain hp F).integrable_norm_pow
    (by norm_num : (2:ℕ)≠0)
  exact congrArg (fun r : ℝ => ((cubicThetaPrimeCoverGroup hp).index:ℝ)*r)
    (cubicThetaPrimeSheetIntegral hp hf).symm

lemma cubicThetaPrimeTrace_mass_integral_le {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteSections hp) :
    (∫ x in cubicThetaFundamentalDomain, ‖(cubicThetaPrimeTraceSection hp F.val).val x‖^2
      ∂cubicThetaPointMeasure)≤
      ((cubicThetaPrimeCoverGroup hp).index:ℝ)*
        ∫ x in cubicThetaPrimeCoverDomain hp, ‖F.val.val x‖^2 ∂cubicThetaPointMeasure := by
  rw [←cubicThetaPrimeTraceMassMajorant_integral hp F]
  exact integral_mono
    ((cubicThetaPrimeTraceSection_memLp_domain hp F).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    (cubicThetaPrimeTraceMassMajorant_integrable hp F)
    (cubicThetaPrimeTraceSection_norm_sq_le hp F.val)

theorem cubicThetaPrimeTraceFinite_value_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    ‖cubicThetaFiniteEnergyValue (cubicThetaPrimeTraceFiniteEnergy hp F)‖^2≤
      ((cubicThetaPrimeCoverGroup hp).index:ℝ)*‖cubicThetaPrimeEnergyValue hp F‖^2 := by
  rw [cubicThetaFiniteEnergyValue_domain_norm_sq,cubicThetaPrimeEnergyValue_domain_norm_sq]
  exact cubicThetaPrimeTrace_mass_integral_le hp ⟨F.val.val,F.property.1⟩

theorem cubicThetaPrimeTraceFinite_gradient_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    ‖cubicThetaFiniteEnergyGradient (cubicThetaPrimeTraceFiniteEnergy hp F)‖^2≤
      ((cubicThetaPrimeCoverGroup hp).index:ℝ)*‖cubicThetaPrimeEnergyGradient hp F‖^2 := by
  rw [cubicThetaFiniteEnergyGradient_domain_norm_sq,cubicThetaPrimeEnergyGradient_domain_norm_sq]
  calc
    _ ≤ ∫ x in cubicThetaFundamentalDomain,
        ((cubicThetaPrimeCoverGroup hp).index:ℝ)*
          ∑ t : cubicThetaPrimeTransversal hp, cubicThetaPrimeSectionEnergy hp F.val.val (t.val • x)
            ∂cubicThetaPointMeasure :=
      integral_mono (cubicThetaPrimeTraceEnergy_integrable_domain hp F)
        ((integrable_finsetSum Finset.univ (fun t _ => cubicThetaPrimeEnergy_integrable_sheet hp F t)).const_mul _)
        (cubicThetaPrimeTraceSection_energy_le hp F.val)
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum Finset.univ
        (fun t _ => cubicThetaPrimeEnergy_integrable_sheet hp F t),
        ←cubicThetaPrimeSheetIntegral hp (cubicThetaPrimeEnergy_integrable_domain hp F)]

end CubicFirstMoment

end

end OAI
