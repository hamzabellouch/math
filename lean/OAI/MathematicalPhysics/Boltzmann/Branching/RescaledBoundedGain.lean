import OAI.MathematicalPhysics.Boltzmann.Approximation.CapColdBounds
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedKernelAction
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedRemainderMeasure

namespace OAI

section

/-! # A principal positive action plus a vanishing error for the actual cold gain -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def coldGainErrorConstant (s₀ η K α d₀ q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (JetRemainderSheet.uniformConstant K)*
    SheetTotal.bound q (2*Real.exp (16*(1+α)^2))+
  ENNReal.ofReal (JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0))*
    ENNReal.ofReal (HotApplication.realBound q)

theorem coldGainErrorConstant_ne_top (s₀ η K α d₀ q : ℝ) :
    coldGainErrorConstant s₀ η K α d₀ q ≠ ∞ := by
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (SheetTotal.bound_lt_top _ _).ne,ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩

theorem CapApproximation.rescaled_cold_gain_majorant (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T)
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (hfone : ∀ z, f z ≤ 1) :
    ∀ᵐ v : Velocity,
      chartGain (volume.withDensity (fun p => ENNReal.ofReal (r*(H q p*F.coldTotal
        (r*x.1,(JetPeriodicDatum.spatialMap (r • x.2),p))))))
        (fun p => ENNReal.ofReal (H q p/H q v)*f (x,p)) v ≤
      ChartKernel.action (selectedFreeKernel r s₀ η K α γ d₀ q N) f (x,v)+
        ENNReal.ofReal r*coldGainErrorConstant s₀ η K α d₀ q := by
  let E := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0)
  have hE : 0 ≤ E := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _
  have hc := F.rescaled_cold_measure_majorant hr hs₀ hsmax hη hηmax hK hα hγ hd₀
    hsmall hq₂ hT hTmax x ht
  have hesc : volume.withDensity (fun p => ENNReal.ofReal
      (r*(H q p*F.escapedTotal ((r*x.1,r • x.2),p)))) ≤
      ENNReal.ofReal (r*E) • volume.withDensity (fun p => ENNReal.ofReal (H q p)) := by
    rw [← withDensity_smul _ (ChartKernel.measurable_H q).ennreal_ofReal]
    apply withDensity_mono
    filter_upwards [] with p
    change ENNReal.ofReal (r*(H q p*_)) ≤ ENNReal.ofReal (r*E)*ENNReal.ofReal (H q p)
    rw [← ENNReal.ofReal_mul (mul_nonneg hr.le hE)]
    have he := F.escapedTotal_bound_global hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hdmax
      hsmall hq₂ hT hTmax 0 (z := ((r*x.1,r • x.2),p)) ht
    simp only [Real.rpow_zero,mul_one] at he
    apply ENNReal.ofReal_le_ofReal
    calc
      r*(H q p*F.escapedTotal ((r*x.1,r • x.2),p)) =
          (r*H q p)*F.escapedTotal ((r*x.1,r • x.2),p) := by ring
      _ ≤ (r*H q p)*E := mul_le_mul_of_nonneg_left he (mul_nonneg hr.le (H_nonneg q p))
      _ = (r*E)*H q p := by ring
  filter_upwards [ChartKernel.normalized_weight_scaled_bound hcarleman hq₁ hq₂
    (ENNReal.ofReal (r*E)),SheetApplication.ae_transverse_ne_zero] with v hv haxis
  have hg := chartGain_le_principal_add_remainders hc q v (fun p => hfone (x,p))
  have hrm := selectedRemainder_gain_bound (γ := γ) (N := N) hr hs₀ hsmax hη hηmax hK hα hd₀ hdmax hq₁ hq₂
    x (by nlinarith [ht.1]) haxis
  have hem : normalizedChartGain (volume.withDensity (fun p => ENNReal.ofReal
      (r*(H q p*F.escapedTotal ((r*x.1,r • x.2),p))))) q v ≤
      ENNReal.ofReal (r*E)*ENNReal.ofReal (HotApplication.realBound q) :=
    (chartGain_mono_measure hesc _ v).trans hv
  have haction : chartGain (selectedColdKernel r s₀ η K α γ d₀ N x)
      (fun p => ENNReal.ofReal (H q p/H q v)*f (x,p)) v =
      ChartKernel.action (selectedFreeKernel r s₀ η K α γ d₀ q N) f (x,v) := by
    rw [ChartKernel.action,selectedFreeKernel,ChartKernel.offAxis_apply _ _ haxis]
    exact (ChartKernel.lintegral_inputKernel_eq_gain
      (selectedColdKernel r s₀ η K α γ d₀ N) q (x,v) (f := fun p => f (x,p))
      (hf.comp (measurable_const.prodMk measurable_id))).symm
  apply (hg.trans (add_le_add (add_le_add le_rfl hrm) hem)).trans_eq
  rw [haction,ENNReal.ofReal_mul hr.le]
  simp only [coldGainErrorConstant,mul_add,mul_assoc,add_assoc,E]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual cap-sized hot input retains the same principal cold action -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

theorem action_const_mul {X : Type*} [MeasurableSpace X]
    (K : Kernel (X × Velocity) Velocity) (f : X × Velocity → ℝ≥0∞)
    (a : ℝ≥0∞) (ha : a ≠ ∞) (z : X × Velocity) :
    action K (fun w => a*f w) z = a*action K f z :=
  lintegral_const_mul' a _ ha

end BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.rescaled_cold_gain_majorant_two (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T)
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (hftwo : ∀ z, f z ≤ 2) :
    ∀ᵐ v : Velocity,
      chartGain (volume.withDensity (fun p => ENNReal.ofReal (r*(H q p*F.coldTotal
        (r*x.1,(JetPeriodicDatum.spatialMap (r • x.2),p))))))
        (fun p => ENNReal.ofReal (H q p/H q v)*f (x,p)) v ≤
      ChartKernel.action (selectedFreeKernel r s₀ η K α γ d₀ q N) f (x,v)+
        2*(ENNReal.ofReal r*coldGainErrorConstant s₀ η K α d₀ q) := by
  let a : ℝ≥0∞ := 1/2
  have ha : a ≠ ∞ := by norm_num [a]
  have hcancel : (2:ℝ≥0∞)*a = 1 := by
    dsimp only [a]
    rw [one_div]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hbound (z) : a*f z ≤ 1 := by
    calc
      _ ≤ a*2 := mul_le_mul' le_rfl (hftwo z)
      _ = 1 := by rw [mul_comm,hcancel]
  have h := F.rescaled_cold_gain_majorant (f := fun z => a*f z) hcarleman hr hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hdmax hsmall hq₁ hq₂ hT hTmax x ht (measurable_const.mul hf) hbound
  filter_upwards [h] with v hv
  have hfunc : (fun p => ENNReal.ofReal (H q p/H q v)*(a*f (x,p))) =
      (fun p => a*(ENNReal.ofReal (H q p/H q v)*f (x,p))) := by
    funext p
    ac_rfl
  rw [hfunc,chartGain_const_mul_right _ a ha,ChartKernel.action_const_mul _ _ a ha] at hv
  have htwo := mul_le_mul' (le_rfl : (2:ℝ≥0∞) ≤ 2) hv
  simpa only [mul_add,← mul_assoc,hcancel,one_mul] using htwo

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
