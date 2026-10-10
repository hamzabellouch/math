import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRankinUnfold
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveStripFubini
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalEnergy

namespace OAI

/-! The exact radial integral of the positive scalar Rankin seed. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaRankin_height_power {v : ℝ} (hv : 0<v) (σ : ℝ) :
    ((v^(2+2*σ):ℝ):ℂ)/(v:ℂ)^3=((v^(2*σ-1):ℝ):ℂ) := by
  have hr : v^(2+2*σ)/v^3=v^(2*σ-1) := by
    rw [←Real.rpow_natCast,←Real.rpow_sub hv]
    congr 1
    ring
  exact_mod_cast hr

def cubicThetaRankinRadialEnergy (σ v : ℝ) : ℂ :=
  ((v^(2*σ-1):ℝ):ℂ)*(((cubicThetaConstant*v^(2/3:ℝ))^2:ℝ)+
    ‖cubicThetaArithmeticBaseScalar‖^2*cubicThetaArithmeticFourierEnergy v)

lemma cubicThetaScalarEnergySeed_radial {σ : ℝ}
    (hi : Integrable (cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ)
      cubicThetaPointMeasure) :
    (∫ p,(cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ p:ℂ)
      ∂cubicThetaPointMeasure)=((9*Real.sqrt 3/2:ℝ):ℂ)*
        ∫ v in Ioc (0:ℝ) 1,cubicThetaRankinRadialEnergy σ v := by
  let f : ℂ × ℝ → ℂ := fun y => if y.2≤1 then
    ((y.2^(2+2*σ):ℝ):ℂ)*(‖cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar y‖^2:ℂ) else 0
  have hseed (p : CubicThetaPoint) :
      (cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ p:ℂ)=
        if p.val.1∈cubicThetaHorizontalCell then f p.val else 0 := by
    simp only [cubicThetaScalarEnergySeed,cubicThetaScalarHeightSeed,
      cubicThetaScalarHeightWeight,cubicThetaArithmeticModelSection,f]
    split_ifs <;> simp_all only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_zero,zero_mul]
    rfl
  have hstrip : ∀ p∈cubicThetaCuspStrip 0,
      (cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ p:ℂ)=f p.val := by
    intro p hp
    change 0<p.val.2 ∧ p.val.1∈cubicThetaHorizontalCell at hp
    rw [hseed,ite_eq_left hp.2]
  have hfi : IntegrableOn (fun p : CubicThetaPoint => f p.val)
      (cubicThetaCuspStrip 0) cubicThetaPointMeasure := by
    apply hi.ofReal.integrableOn.congr
    filter_upwards [ae_restrict_mem (cubicThetaCuspStrip_measurable 0)] with p hp
    exact hstrip p hp
  have hout : ∀ p∉cubicThetaCuspStrip 0,
      (cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ p:ℂ)=0 := by
    intro p hp
    rw [hseed]
    exact ite_eq_right (fun hc => hp ⟨p.property,hc⟩)
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  rw [setIntegral_congr_fun (cubicThetaCuspStrip_measurable 0) hstrip]
  have hfub := cubicThetaPositiveCuspStrip_fubini (le_refl (0:ℝ)) f hfi
  change (∫ p in cubicThetaCuspStrip 0,f p.val ∂cubicThetaPointMeasure)=_ at hfub
  rw [hfub]
  have hz (v : ℝ) (hv : 0<v) :
      (∫ z in cubicThetaHorizontalCell,f (z,v)/(v:ℂ)^3)=
        if v≤1 then ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicThetaRankinRadialEnergy σ v else 0 := by
    by_cases hv1 : v≤1
    · simp only [f,ite_eq_left hv1]
      have he (z : ℂ) : ((v^(2+2*σ):ℝ):ℂ)*
          (‖cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (z,v)‖^2:ℂ)/(v:ℂ)^3=
            (((v^(2+2*σ):ℝ):ℂ)/(v:ℂ)^3)*
              (‖cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (z,v)‖^2:ℂ) := by ring
      simp_rw [he]
      rw [integral_const_mul,cubicThetaArithmeticModel_horizontal_energy _ hv,
        cubicThetaRankin_height_power hv]
      unfold cubicThetaRankinRadialEnergy
      ring
    · simp only [f,ite_eq_right hv1,zero_div,integral_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hz]
  have he : (fun v : ℝ => if v≤1 then
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicThetaRankinRadialEnergy σ v else 0)=
      (Iic (1:ℝ)).indicator (fun v => ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicThetaRankinRadialEnergy σ v) := rfl
  rw [he,integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic (1:ℝ)∩Ioi 0=Ioc 0 1 := by ext v; simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc,and_comm]
  rw [hset,integral_const_mul]

end CubicFirstMoment

end

end OAI
