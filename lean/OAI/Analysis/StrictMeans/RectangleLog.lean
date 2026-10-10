import OAI.Analysis.StrictMeans.Model

namespace OAI

section
open Set MeasureTheory Complex
open scoped ENNReal Topology
namespace StrictInverseFirstPower
noncomputable section

def complexBox (S a b : ℝ) : Set ℂ := {z | |z.re| ≤ S ∧ a ≤ z.im ∧ z.im ≤ b}

lemma measurableSet_complexBox (S a b : ℝ) : MeasurableSet (complexBox S a b) :=
  ((isClosed_le Complex.continuous_re.abs continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im continuous_const))).measurableSet

lemma lintegral_inv_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ y in Icc a b, ENNReal.ofReal (y⁻¹)) = ENNReal.ofReal (Real.log b-Real.log a) := by
  have hc : ContinuousOn (fun y : ℝ=>y⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun y hy=>(ha.trans_le hy.1).ne')
  have hi : IntegrableOn (fun y : ℝ=>y⁻¹) (Icc a b) := hc.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact inv_nonneg.mpr (ha.le.trans hy.1)),integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab,integral_inv (notMem_uIcc_of_lt ha (ha.trans_le hab)),
    Real.log_div (ha.trans_le hab).ne' ha.ne']

lemma lintegral_complexBox_inv {S a b : ℝ} (_hS : 0 ≤ S) (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ z in complexBox S a b, ENNReal.ofReal (z.im⁻¹)) =
      ENNReal.ofReal (2*S*(Real.log b-Real.log a)) := by
  let E := Complex.measurableEquivRealProd
  let R : Set (ℝ × ℝ) := Icc (-S) S ×ˢ Icc a b
  have hR : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have he : E ⁻¹' R = complexBox S a b := by
    ext z
    simp [E,R,complexBox,abs_le,and_assoc,and_left_comm,and_comm]
  have hm : Measurable (fun p : ℝ × ℝ=>ENNReal.ofReal (p.2⁻¹)) :=
    measurable_snd.inv.ennreal_ofReal
  have hi := Complex.volume_preserving_equiv_real_prod.lintegral_comp (hm.indicator hR)
  rw [← lintegral_indicator (measurableSet_complexBox S a b)]
  have hp : (fun z : ℂ=>(complexBox S a b).indicator
      (fun z=>ENNReal.ofReal (z.im⁻¹)) z) =
      (fun z=>(R.indicator (fun p=>ENNReal.ofReal (p.2⁻¹))) (E z)) := by
    funext z
    rw [← he]
    rfl
  rw [hp,hi,lintegral_indicator hR,Measure.volume_eq_prod,← Measure.prod_restrict]
  rw [lintegral_prod _ (hm.aemeasurable)]
  dsimp only
  rw [lintegral_inv_Icc ha hab,lintegral_const,
    Measure.restrict_apply_univ,Real.volume_Icc,← ENNReal.ofReal_mul]
  · congr 1
    ring
  · exact sub_nonneg.mpr (Real.log_le_log ha hab)

end
end StrictInverseFirstPower

end

end OAI
