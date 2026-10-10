import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactExponential
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierStripSupport

namespace OAI

/-! The compact strip contribution of the incoming arithmetic series is
entire in the spectral parameter. It contributes no pole to Fourier tests. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaIncomingTerm_point_continuous (r : CubicThetaBottomRow) (s : ℂ) :
    Continuous (fun p : CubicThetaPoint => cubicThetaIncomingTerm r p.val s) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact ((cubicThetaIncomingTerm_contDiffAt r s p.property).continuousAt.comp
    continuous_subtype_val.continuousAt)

lemma cubicThetaRowLogHeight_point_continuous (r : CubicThetaBottomRow) :
    Continuous (fun p : CubicThetaPoint => Real.log (r.height p.val)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (((r.height_contDiffAt p.property).continuousAt.log (r.height_pos p.property).ne').comp
    continuous_subtype_val.continuousAt)

lemma cubicThetaIncomingTerm_exponential (r : CubicThetaBottomRow) (p : CubicThetaPoint) (s : ℂ) :
    cubicThetaIncomingTerm r p.val s=cubicThetaIncomingTerm r p.val 0*
      Complex.exp (s*(Real.log (r.height p.val):ℂ)) := by
  have hp := r.height_pos p.property
  simp only [cubicThetaIncomingTerm,cubicThetaEisensteinTerm,Complex.cpow_zero,mul_one]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),←Complex.ofReal_log hp.le]
  rw [mul_comm (Real.log (r.height p.val):ℂ) s]
  ring

lemma cubicThetaIncomingCompactIntegral_differentiable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    Differentiable ℂ (fun s : ℂ => ∫ p,
      star (cubicThetaFourierStripSeed h W p)*cubicThetaIncomingEisenstein p.val s
        ∂cubicThetaPointMeasure) := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaFourierStripSeed_compact h W hε hW
  have hKC : IsCompact (cubicThetaPointCoordinates '' K) :=
    hK.image cubicThetaPointCoordinates_continuous
  obtain ⟨S,hS⟩ := cubicThetaIncomingEisenstein_compact_sum hKC
    (by rintro _ ⟨p,_,rfl⟩; exact p.property)
  have he (s : ℂ) : (∫ p,star (cubicThetaFourierStripSeed h W p)*
      cubicThetaIncomingEisenstein p.val s ∂cubicThetaPointMeasure)=
      ∑ r∈S,∫ p in K,star (cubicThetaFourierStripSeed h W p)*
        cubicThetaIncomingTerm r p.val s ∂cubicThetaPointMeasure := by
    rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=K) (by
      intro p hp
      have hz : cubicThetaFourierStripSeed h W p=0 := not_not.mp (fun hn => hp (hsub hn))
      rw [hz,star_zero,zero_mul])]
    calc
      _ = ∫ p in K,∑ r∈S,star (cubicThetaFourierStripSeed h W p)*
          cubicThetaIncomingTerm r p.val s ∂cubicThetaPointMeasure := by
        apply setIntegral_congr_fun hK.measurableSet
        intro p hp
        dsimp only
        rw [hS p.val ⟨p,hp,rfl⟩ s,Finset.mul_sum]
      _ = _ := integral_finsetSum S (fun r _ =>
        (cubicThetaFourierStripSeed_mul_integrable h W hε hW _
          (cubicThetaIncomingTerm_point_continuous r s)).integrableOn)
  have hterm (r : CubicThetaBottomRow) : Differentiable ℂ (fun s : ℂ => ∫ p in K,
      star (cubicThetaFourierStripSeed h W p)*cubicThetaIncomingTerm r p.val s
        ∂cubicThetaPointMeasure) := by
    have hd := cubicThetaCompactExponential_differentiable hK
      (fun p => star (cubicThetaFourierStripSeed h W p)*cubicThetaIncomingTerm r p.val 0)
      (cubicThetaFourierStripSeed_mul_integrable h W hε hW _
        (cubicThetaIncomingTerm_point_continuous r 0)).integrableOn
      (fun p => Real.log (r.height p.val)) (cubicThetaRowLogHeight_point_continuous r).continuousOn
    convert hd using 1
    funext s
    apply setIntegral_congr_fun hK.measurableSet
    intro p _
    dsimp only
    rw [cubicThetaIncomingTerm_exponential]
    ring
  have hf : (fun s : ℂ => ∫ p,star (cubicThetaFourierStripSeed h W p)*
      cubicThetaIncomingEisenstein p.val s ∂cubicThetaPointMeasure)=
      (fun s => ∑ r∈S,∫ p in K,star (cubicThetaFourierStripSeed h W p)*
        cubicThetaIncomingTerm r p.val s ∂cubicThetaPointMeasure) := funext he
  rw [hf]
  exact Differentiable.fun_sum (fun r _ => hterm r)

end CubicFirstMoment

end

end OAI
