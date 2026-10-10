import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarMonotone

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma G_nonneg (β : ℝ) : 0 ≤ G β := by
  apply integral_nonneg
  intro h
  exact div_nonneg (v_pos h).le (by linarith [w_pos h])

lemma l_temperature_monotone {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) : l β ≤ l z := by
  rw [l_eq,l_eq]
  linarith [a_temperature_antitone hβ hβz]

lemma memLp_F_other (β z : ℝ) : MemLp (F β) 2 (fieldLaw z) := by
  convert! (((((memLp_field_v z).add ((memLp_field z).const_mul (a β))).add
      (memLp_mv.const_mul (2*β^2))).add (memLp_v.const_mul (50/100-β^2*a β/l β))).add
      (memLp_m.const_mul (12/100:ℝ))).add (memLp_g.const_mul (3*β^2*G β)) using 1
  ext h
  dsimp [F]
  ring

lemma F_sub_F (β z h : ℝ) : F β h-F z h =
    (a β-a z)*h+(2*(β^2-z^2))*(m h*v h)+
      (z^2*a z/l z-β^2*a β/l β)*v h+(3*(β^2*G β-z^2*G z))*g h := by
  unfold F
  ring

lemma sd_F_difference (β z : ℝ) : sd (fieldLaw z) (fun h => F β h-F z h) ≤
    |a β-a z| *|z|+2*|β^2-z^2| *sd (fieldLaw z) (fun h => m h*v h)+
      |z^2*a z/l z-β^2*a β/l β| *sd (fieldLaw z) v+
      3*|β^2*G β-z^2*G z| *sd (fieldLaw z) g := by
  let A := fun h : ℝ => (a β-a z)*h
  let B := fun h : ℝ => (2*(β^2-z^2))*(m h*v h)
  let C := fun h : ℝ => (z^2*a z/l z-β^2*a β/l β)*v h
  let D := fun h : ℝ => (3*(β^2*G β-z^2*G z))*g h
  have hA : MemLp A 2 (fieldLaw z) := (memLp_field z).const_mul _
  have hB : MemLp B 2 (fieldLaw z) := memLp_mv.const_mul _
  have hC : MemLp C 2 (fieldLaw z) := memLp_v.const_mul _
  have hD : MemLp D 2 (fieldLaw z) := memLp_g.const_mul _
  have hAB : MemLp (fun h => A h+B h) 2 (fieldLaw z) := hA.add hB
  have hABC : MemLp (fun h => A h+B h+C h) 2 (fieldLaw z) := hAB.add hC
  have h1 := sd_add hA hB
  have h2 := sd_add hAB hC
  have h3 := sd_add hABC hD
  have hsum : sd (fieldLaw z) (fun h => A h+B h+C h+D h) ≤
      sd (fieldLaw z) A+sd (fieldLaw z) B+sd (fieldLaw z) C+sd (fieldLaw z) D := by linarith
  simp_rw [F_sub_F]
  have hzsd : sd (fieldLaw z) (fun h : ℝ => h) = |z| := by
    have hh := variance_id_gaussianReal (μ := z^2) (v := variance z)
    rw [variance_eq_integral measurable_id.aemeasurable] at hh
    change ∫ h, (h-(∫ t, t ∂fieldLaw z))^2 ∂fieldLaw z = _ at hh
    rw [variance_coe] at hh
    unfold sd l2Norm centered
    rw [hh,sqrt_sq_eq_abs]
  have hAsd : sd (fieldLaw z) A = |a β-a z| * |z| := by
    change sd (fieldLaw z) (fun h => (a β-a z)*(fun x : ℝ => x) h) = _
    rw [sd_const_mul,hzsd]
  rw [hAsd] at hsum
  dsimp [B,C,D] at hsum
  simp only [sd_const_mul,abs_mul,show |(2:ℝ)|=2 from by norm_num,
    show |(3:ℝ)|=3 from by norm_num] at hsum
  exact hsum

lemma abs_sub_le_interval {x y L U : ℝ} (hxL : L ≤ x) (hxU : x ≤ U)
    (hyL : L ≤ y) (hyU : y ≤ U) : |x-y| ≤ U-L := by
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma temp_a_ratio_bounds {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) :
    j^2*a z/l z ≤ β^2*a β/l β ∧ β^2*a β/l β ≤ z^2*a j/l j := by
  have hβ : 0 < β := hj.trans_le hjβ
  have ha1 := a_temperature_antitone hj hjβ
  have ha2 := a_temperature_antitone hβ hβz
  have hl1 := l_temperature_monotone hj hjβ
  have hl2 := l_temperature_monotone hβ hβz
  have hb1 : j^2*a z ≤ β^2*a β := mul_le_mul (by nlinarith) ha2 (a_nonneg _) (sq_nonneg _)
  have hb2 : β^2*a β ≤ z^2*a j := mul_le_mul (by nlinarith) ha1 (a_nonneg _) (sq_nonneg _)
  exact ⟨(div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (a_nonneg _)) (l_pos β) hl2).trans
      (div_le_div_of_nonneg_right hb1 (l_pos β).le),
    (div_le_div_of_nonneg_right hb2 (l_pos β).le).trans
      (div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (a_nonneg _)) (l_pos j) hl1)⟩

lemma temp_G_bounds {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) :
    j^2*G z ≤ β^2*G β ∧ β^2*G β ≤ z^2*G j := by
  have hβ : 0 < β := hj.trans_le hjβ
  exact ⟨mul_le_mul (by nlinarith) (G_temperature_antitone hβ hβz) (G_nonneg _) (sq_nonneg _),
    mul_le_mul (by nlinarith) (G_temperature_antitone hj hjβ) (G_nonneg _) (sq_nonneg _)⟩

def crossBound (j z : ℝ) : ℝ := sqrt (densityFactor j z)*
  (sd (fieldLaw z) (F z)+(a j-a z)*z+
    2*(z^2-j^2)*sd (fieldLaw z) (fun h => m h*v h)+
    (z^2*a j/l j-j^2*a z/l z)*sd (fieldLaw z) v+
    3*(z^2*G j-j^2*G z)*sd (fieldLaw z) g)

theorem sd_F_interval {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) :
    sd (fieldLaw β) (F β) ≤ crossBound j z := by
  have hβ : 0 < β := hj.trans_le hjβ
  have hz : 0 < z := hβ.trans_le hβz
  have hfchg := sd_temperature_interval_bound hj hjβ hβz (memLp_F β) (memLp_F_other β z)
  have hfd := sd_F_difference β z
  have hftriangle := abs_sd_sub_le (memLp_F_other β z) (memLp_F z)
  have haβ := a_temperature_antitone hβ hβz
  have haj := a_temperature_antitone hj hjβ
  have ha : |a β-a z| ≤ a j-a z := by rw [abs_of_nonneg (sub_nonneg.mpr haβ)]; linarith
  have hsqβ : β^2 ≤ z^2 := by nlinarith
  have hj2 : j^2 ≤ β^2 := by nlinarith
  have hb : |β^2-z^2| ≤ z^2-j^2 := by rw [abs_of_nonpos (sub_nonpos.mpr hsqβ)]; linarith
  have hal1 := temp_a_ratio_bounds hj hjβ hβz
  have hal2 := temp_a_ratio_bounds hj (hjβ.trans hβz) (le_refl z)
  have hc := abs_sub_le_interval hal2.1 hal2.2 hal1.1 hal1.2
  have hgl1 := temp_G_bounds hj hjβ hβz
  have hgl2 := temp_G_bounds hj (hjβ.trans hβz) (le_refl z)
  have hd := abs_sub_le_interval hgl1.1 hgl1.2 hgl2.1 hgl2.2
  rw [abs_of_pos hz] at hfd
  have hupper : sd (fieldLaw z) (F β) ≤
      sd (fieldLaw z) (F z)+(a j-a z)*z+
      2*(z^2-j^2)*sd (fieldLaw z) (fun h => m h*v h)+
      (z^2*a j/l j-j^2*a z/l z)*sd (fieldLaw z) v+
      3*(z^2*G j-j^2*G z)*sd (fieldLaw z) g := by
    have hat := mul_le_mul_of_nonneg_right ha hz.le
    have hbt := mul_le_mul_of_nonneg_right hb (sd_nonneg (μ := fieldLaw z) (fun h => m h*v h))
    have hct := mul_le_mul_of_nonneg_right hc (sd_nonneg (μ := fieldLaw z) v)
    have hdt := mul_le_mul_of_nonneg_right hd (sd_nonneg (μ := fieldLaw z) g)
    have htri := (le_abs_self _).trans hftriangle
    nlinarith only [hfd,htri,hat,hbt,hct,hdt]
  exact hfchg.trans (mul_le_mul_of_nonneg_left hupper (sqrt_nonneg _))

def slackBound₀ (j z : ℝ) : ℝ := l j+18/1000+
  j^2*(a z^2/l z-a z-(3/2)*G j^2)-z^2*R z

def slackBound₁ (j z : ℝ) : ℝ := 4644/10000-z*sd (fieldLaw z) v/2+
  j^2*(∫ h, m h*v h ∂fieldLaw j)-z^2*((3/2)*sd (fieldLaw z) g^2+R z)

theorem U₁_interval {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) (hz : z ≤ 1) :
    slackBound₁ j z ≤ U₁ β := by
  have hβ : 0 < β := hj.trans_le hjβ
  have hv := weighted_sd_temperature_mono' hβ hβz hz memLp_v memLp_v
  have hm := weighted_mv_temperature_mono hj hjβ (hβz.trans hz)
  have hg := weighted_sd_temperature_mono hβ hβz hz memLp_g memLp_g
  have hr := weighted_R_temperature_mono hβ hβz hz
  unfold slackBound₁ U₁
  nlinarith only [hv,hm,hg,hr]

lemma coherent_a_slack_mono {x y t : ℝ} (ht : 0 < t) (_hy : 0 ≤ y)
    (hyx : y ≤ x) (hreg : t ≤ 2*y) : y^2/t-y ≤ x^2/t-x := by
  apply (mul_le_mul_iff_of_pos_right ht).mp
  field_simp
  have hp := mul_nonneg (sub_nonneg.mpr hyx) (show 0 ≤ x+y-t by linarith)
  nlinarith only [hp]

theorem U₀_interval {j β z : ℝ} (hj : 0 < j) (hjβ : j ≤ β) (hβz : β ≤ z) (hz : z ≤ 1)
    (hreg : l z ≤ 2*a z) (hc : 0 ≤ a z^2/l z-a z-(3/2)*G j^2) :
    slackBound₀ j z ≤ U₀ β := by
  have hβ : 0 < β := hj.trans_le hjβ
  have hj2 : j^2 ≤ β^2 := by nlinarith
  have ha := a_temperature_antitone hβ hβz
  have hg := G_temperature_antitone hj hjβ
  have hl1 := l_temperature_monotone hj hjβ
  have hl2 := l_temperature_monotone hβ hβz
  have hh1 := coherent_a_slack_mono (l_pos z) (a_nonneg z) ha hreg
  have hh2 := div_le_div_of_nonneg_left (sq_nonneg (a β)) (l_pos β) hl2
  have hg2 : G β^2 ≤ G j^2 := (sq_le_sq₀ (G_nonneg β) (G_nonneg j)).mpr hg
  have hcoef : a z^2/l z-a z-(3/2)*G j^2 ≤ a β^2/l β-a β-(3/2)*G β^2 := by
    linarith
  have hprod := mul_le_mul hj2 hcoef hc (sq_nonneg β)
  have hr := weighted_R_temperature_mono hβ hβz hz
  unfold slackBound₀ U₀
  linarith

end SKRatio.Scalar

end

end OAI
