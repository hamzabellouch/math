import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSheetIntegral

namespace OAI

/-! The actual finite trace has its Cauchy--Schwarz mass bound with the
exact covering index. The integrability assertion is proved from this
bound, so it will pass to the completed operator. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeTrace_norm_sq_le {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) (x : CubicThetaPoint) :
    ‖(cubicThetaPrimeCubeTraceSection hp F).val x‖^2≤
      ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∑' t : cubicThetaPrimeCubeTransversal p,‖F.val (t.val • x)‖^2 := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have he : (cubicThetaPrimeCubeTraceSection hp F).val x=
      ∑' t : cubicThetaPrimeCubeTransversal p,cubicThetaPrimeCubeTraceTerm p F t.val x := rfl
  rw [he,tsum_fintype,tsum_fintype]
  have hn := norm_sum_le Finset.univ (fun t : cubicThetaPrimeCubeTransversal p =>
    cubicThetaPrimeCubeTraceTerm p F t.val x)
  have ht (t : cubicThetaPrimeCubeTransversal p) :
      ‖cubicThetaPrimeCubeTraceTerm p F t.val x‖=‖F.val (t.val • x)‖ := by
    rw [cubicThetaPrimeCubeTraceTerm,norm_mul,norm_star,cubicThetaKubotaValue_norm,one_mul]
  simp_rw [ht] at hn
  have hs := mul_self_le_mul_self (_root_.norm_nonneg _) hn
  rw [←pow_two,←pow_two] at hs
  apply hs.trans
  have hc := sq_sum_le_card_mul_sum_sq (s:=Finset.univ)
    (f:=fun t : cubicThetaPrimeCubeTransversal p => ‖F.val (t.val • x)‖)
  rwa [Finset.card_univ,←Nat.card_eq_fintype_card,
    (cubicThetaPrimeCubeTransversal_complement p).card_right] at hc

lemma cubicThetaPrimeCubeSection_sheet_integrable {p : Eisenstein} (_hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (t : cubicThetaPrimeCubeTransversal p) :
    IntegrableOn (fun x => ‖F.val (t.val • x)‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hs : IntegrableOn (fun x => ‖F.val x‖^2)
      ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain) cubicThetaPointMeasure :=
    hF.mono_set (subset_iUnion (fun u : cubicThetaPrimeCubeTransversal p =>
      (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t)
  exact ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul t.val)).mp hs

lemma cubicThetaPrimeCubeTrace_majorant_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    IntegrableOn (fun x => ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
      ∑' t : cubicThetaPrimeCubeTransversal p,‖F.val (t.val • x)‖^2)
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  simp_rw [tsum_fintype]
  exact (integrable_finsetSum Finset.univ (fun t _ =>
    cubicThetaPrimeCubeSection_sheet_integrable hp F hF t)).const_mul _

lemma cubicThetaPrimeCubeTrace_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    IntegrableOn (fun x => ‖(cubicThetaPrimeCubeTraceSection hp F).val x‖^2)
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCubeTrace_majorant_integrable hp F hF).mono'
    (((cubicThetaPrimeCubeTraceSection hp F).val.continuous.norm.pow 2).aestronglyMeasurable)
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact cubicThetaPrimeCubeTrace_norm_sq_le hp F x

theorem cubicThetaPrimeCubeTrace_mass_integral_le {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,‖(cubicThetaPrimeCubeTraceSection hp F).val x‖^2
      ∂cubicThetaPointMeasure)≤((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∫ x in cubicThetaPrimeCubeCoverDomain p,‖F.val x‖^2 ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  calc
    _ ≤ ∫ x in cubicThetaFundamentalDomain,((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∑' t : cubicThetaPrimeCubeTransversal p,‖F.val (t.val • x)‖^2 ∂cubicThetaPointMeasure :=
      integral_mono (cubicThetaPrimeCubeTrace_integrable hp F hF)
        (cubicThetaPrimeCubeTrace_majorant_integrable hp F hF) (cubicThetaPrimeCubeTrace_norm_sq_le hp F)
    _ = _ := by
      simp_rw [tsum_fintype]
      rw [integral_const_mul,integral_finsetSum Finset.univ
        (fun t _ => cubicThetaPrimeCubeSection_sheet_integrable hp F hF t),
        cubicThetaPrimeCubeSheetIntegral hp hF,tsum_fintype]

end CubicFirstMoment

end

end OAI
