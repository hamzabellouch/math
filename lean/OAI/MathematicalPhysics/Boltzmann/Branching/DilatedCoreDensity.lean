import OAI.MathematicalPhysics.Boltzmann.Jets.FreeCoreMismatch

namespace OAI

section

/-! # Positive gain kernels under the actual cap dilation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCoreSheet

def dilatedColdKernel (r η K α γ s d : ℝ) (sign : Bool) : Kernel SpaceTime Velocity :=
  ((kineticColdKernel η K α γ s d sign).comap
    (fun z : SpaceTime => (r*z.1,r • z.2)) (by fun_prop)).withDensity
      (fun _ _ => ENNReal.ofReal r)

instance dilatedColdKernel_sFinite (r η K α γ s d : ℝ) (sign : Bool) :
    IsSFiniteKernel (dilatedColdKernel r η K α γ s d sign) := by
  unfold dilatedColdKernel
  exact Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

theorem dilatedColdKernel_apply (r η K α γ s d : ℝ) (sign : Bool) (z : SpaceTime) :
    dilatedColdKernel r η K α γ s d sign z =
      ENNReal.ofReal r • kineticColdKernel η K α γ s d sign (r*z.1,r • z.2) := by
  rw [dilatedColdKernel,Kernel.withDensity_apply _ measurable_const,withDensity_const]
  rfl

def dilatedFreeKernel (r η K α γ s d q : ℝ) (sign : Bool) : Kernel KineticPhase Velocity :=
  ChartKernel.offAxis (ChartKernel.inputKernel (dilatedColdKernel r η K α γ s d sign) q)

instance dilatedFreeKernel_sFinite (r η K α γ s d q : ℝ) (sign : Bool) :
    IsSFiniteKernel (dilatedFreeKernel r η K α γ s d q sign) := by
  unfold dilatedFreeKernel
  infer_instance

theorem dilatedFreeKernel_bound {r K α γ s d q : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16)
    (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (sign : Bool)
    (z : KineticPhase) (ht : 0 < z.1.1) :
    dilatedFreeKernel r η K α γ s d q sign z univ ≤
      ENNReal.ofReal (growthConstant K α γ q/z.1.1) := by
  by_cases hv : VelocityWeight.transverse z.2 = 0
  · rw [dilatedFreeKernel,ChartKernel.offAxis_axis _ _ hv]
    exact bot_le
  · rw [dilatedFreeKernel,ChartKernel.offAxis_apply _ _ hv,ChartKernel.inputKernel_mass,
      dilatedColdKernel_apply,normalizedChartGain,chartGain_smul_measure]
    have hb := kineticFreeKernel_bound hK hα hγ hs hd hdmax hq₁ hq₂ η sign
      ((r*z.1.1,r • z.1.2),z.2) (mul_pos hr ht)
    rw [kineticFreeKernel,ChartKernel.offAxis_apply _ ((r*z.1.1,r • z.1.2),z.2) hv,
      ChartKernel.inputKernel_mass] at hb
    calc
      _ ≤ ENNReal.ofReal r*ENNReal.ofReal (growthConstant K α γ q/(r*z.1.1)) :=
        mul_le_mul' le_rfl hb
      _ = _ := by
        rw [← ENNReal.ofReal_mul hr.le]
        congr 1
        field_simp

theorem iterate_dilatedFreeKernel_bound {r K α γ s d q a T B : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s)
    (hd : 0 < d) (hdmax : d ≤ 1/16) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hB : 0 ≤ B) (η : ℝ) (sign : Bool) {f : KineticPhase → ℝ≥0∞}
    (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ ENNReal.ofReal B)
    (n : ℕ) (z : KineticPhase) (hz : z.1.1 ∈ Icc a T) :
    PositiveIteration.iterate a (dilatedFreeKernel r η K α γ s d q sign) f n z ≤
      ENNReal.ofReal (B*(growthConstant K α γ q*Real.log (z.1.1/a))^n) := by
  apply PositiveIteration.iterate_bound ha (growthConstant_nonneg hK α γ q) hB _
    (fun w hw => dilatedFreeKernel_bound hr hK hα hγ hs hd hdmax hq₁ hq₂ η sign w
      (ha.trans_le hw.1)) hf n z hz

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Density representatives for the dilated free-core measures -/

noncomputable section

open MeasureTheory ProbabilityTheory
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCoreSheet

def dilatedCoreDensity (r η K α γ s d : ℝ) (sign : Bool) (z : KineticPhase) : ℝ≥0∞ :=
  ENNReal.ofReal r*kineticCoreDensity η K α γ s d sign ((r*z.1.1,r • z.1.2),z.2)

theorem dilatedCoreDensity_measurable (r η K α γ s d : ℝ) (sign : Bool) :
    Measurable (dilatedCoreDensity r η K α γ s d sign) := by
  change Measurable (fun z : KineticPhase => ENNReal.ofReal r*
    kineticCoreDensity η K α γ s d sign ((r*z.1.1,r • z.1.2),z.2))
  exact measurable_const.mul ((kineticCoreDensity_measurable η K α γ s d sign).comp (by fun_prop))

theorem dilatedColdKernel_density (r η K α γ s d : ℝ) (sign : Bool) (x : SpaceTime) :
    dilatedColdKernel r η K α γ s d sign x =
      volume.withDensity (fun v => dilatedCoreDensity r η K α γ s d sign (x,v)) := by
  rw [dilatedColdKernel_apply,kineticColdKernel_apply]
  have hm : Measurable (fun v => kineticCoreDensity η K α γ s d sign ((r*x.1,r • x.2),v)) :=
    (kineticCoreDensity_measurable η K α γ s d sign).comp (measurable_const.prodMk measurable_id)
  change ENNReal.ofReal r • volume.withDensity (fun v =>
    kineticCoreDensity η K α γ s d sign ((r*x.1,r • x.2),v)) = _
  rw [← withDensity_smul _ hm]
  rfl

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
