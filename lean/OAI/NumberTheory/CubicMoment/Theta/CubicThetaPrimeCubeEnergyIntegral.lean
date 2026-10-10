import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeckeEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeInvariantDilation

namespace OAI

/-! The literal Hecke trace preserves integrable derivative energy,
with the same degree-squared bound as its mass. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeSheet_integrable {p : Eisenstein}
    {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (t : cubicThetaPrimeCubeTransversal p) :
    IntegrableOn (fun x => f (t.val • x)) cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hs : IntegrableOn f ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
      cubicThetaPointMeasure :=
    hf.mono_set (subset_iUnion (fun u : cubicThetaPrimeCubeTransversal p =>
      (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t)
  exact ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul t.val)).mp hs

lemma cubicThetaPrimeCubeHeckeMatrix_action {p : Eisenstein} (hp : primaryPrime p)
    (t : cubicThetaPrimeCubeTransversal p) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeHeckeMatrix hp t • x=
      cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (t.val • x) := by
  rw [cubicThetaPrimeCubeHeckeMatrix,mul_smul]
  rfl

lemma cubicThetaPrimeCubeHecke_energy_majorant {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hE : IntegrableOn (cubicThetaSectionEnergy F) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    IntegrableOn (fun x => ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
      ∑' t : cubicThetaPrimeCubeTransversal p,
        cubicThetaSectionEnergy F (cubicThetaPrimeCubeHeckeMatrix hp t • x))
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have hd := cubicThetaPrimeCubeScalarDilation_integrable hp hE (cubicThetaC1Energy_invariant F hF)
  simp_rw [tsum_fintype,cubicThetaPrimeCubeHeckeMatrix_action]
  exact (integrable_finsetSum Finset.univ (fun t _ => cubicThetaPrimeCubeSheet_integrable hd t)).const_mul _

lemma cubicThetaPrimeCubeHecke_energy_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hE : IntegrableOn (cubicThetaSectionEnergy F) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    IntegrableOn (cubicThetaSectionEnergy (cubicThetaPrimeCubeHecke hp F))
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCubeHecke_energy_majorant hp F hF hE).mono'
    (cubicThetaC1Energy_continuous _ (cubicThetaPrimeCubeHecke_c1 hp F hF)).aestronglyMeasurable
  filter_upwards with x
  have hn : 0≤cubicThetaSectionEnergy (cubicThetaPrimeCubeHecke hp F) x :=
    mul_nonneg (sq_nonneg _) (cubicThetaTangentEnergy_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  exact cubicThetaPrimeCubeHecke_energy_le hp F hF x

theorem cubicThetaPrimeCubeHecke_energy_integral_le {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hE : IntegrableOn (cubicThetaSectionEnergy F) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,cubicThetaSectionEnergy (cubicThetaPrimeCubeHecke hp F) x
      ∂cubicThetaPointMeasure)≤((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*
        ∫ x in cubicThetaFundamentalDomain,cubicThetaSectionEnergy F x ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have hd := cubicThetaPrimeCubeScalarDilation_integrable hp hE (cubicThetaC1Energy_invariant F hF)
  calc
    _ ≤ ∫ x in cubicThetaFundamentalDomain,((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∑' t : cubicThetaPrimeCubeTransversal p,
          cubicThetaSectionEnergy F (cubicThetaPrimeCubeHeckeMatrix hp t • x) ∂cubicThetaPointMeasure :=
      integral_mono (cubicThetaPrimeCubeHecke_energy_integrable hp F hF hE)
        (cubicThetaPrimeCubeHecke_energy_majorant hp F hF hE) (cubicThetaPrimeCubeHecke_energy_le hp F hF)
    _ = ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∫ x in cubicThetaPrimeCubeCoverDomain p,
          cubicThetaSectionEnergy F (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)
            ∂cubicThetaPointMeasure := by
      simp_rw [cubicThetaPrimeCubeHeckeMatrix_action,tsum_fintype]
      rw [integral_const_mul,integral_finsetSum Finset.univ
        (fun t _ => cubicThetaPrimeCubeSheet_integrable hd t),cubicThetaPrimeCubeSheetIntegral hp hd,tsum_fintype]
    _ = _ := by
      rw [cubicThetaPrimeCubeScalarDilation_integral hp hE (cubicThetaC1Energy_invariant F hF)]
      ring

end CubicFirstMoment

end

end OAI
