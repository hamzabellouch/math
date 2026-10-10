import OAI.Geometry.RCD.Transport.RenyiPerturbationIntegral
import OAI.Geometry.RCD.Transport.RenyiSemicontinuity

namespace OAI

/-! # Strict Rényi improvement for a measure replacement

This converts the scalar replacement estimate to the actual measure
obtained by replacing a portion of a transport plan.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem exists_measure_renyi_increase (μ ν η : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure η]
    (hac : ν ≪ μ) {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 0 < C)
    (hη : η ≤ ENNReal.ofReal C • μ)
    (hmass : η univ = ν {x | C < (ν.rnDeriv μ x).toReal})
    (hbad : ¬ν ≤ ENNReal.ofReal C • μ) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      (∫ x, (ν.rnDeriv μ x).toReal^q ∂μ) <
      ∫ x, ((ν-ENNReal.ofReal a • ν.restrict {x | C < (ν.rnDeriv μ x).toReal}+
        ENNReal.ofReal a • η).rnDeriv μ x).toReal^q ∂μ := by
  classical
  let ρ := fun x => (ν.rnDeriv μ x).toReal
  let h := fun x => min C (η.rnDeriv μ x).toReal
  have hρ : Measurable ρ := (ν.measurable_rnDeriv μ).ennreal_toReal
  have hh : Measurable h := measurable_const.min (η.measurable_rnDeriv μ).ennreal_toReal
  have hρ0 : ∀ x, 0 ≤ ρ x := fun _ => ENNReal.toReal_nonneg
  have hh0 : ∀ x, 0 ≤ h x := fun _ => le_min hC.le ENNReal.toReal_nonneg
  have hhC : ∀ x, h x ≤ C := fun _ => min_le_left _ _
  have hηac : η ≪ μ := hη.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  have hh_eq : h =ᵐ[μ] fun x => (η.rnDeriv μ x).toReal := by
    filter_upwards [rnDeriv_le_const_of_le_smul μ η hη,Measure.rnDeriv_lt_top η μ] with x hx hxt
    apply min_eq_right
    exact (ENNReal.toReal_le_toReal hxt.ne ENNReal.ofReal_ne_top).mpr hx |>.trans_eq
      (ENNReal.toReal_ofReal hC.le)
  have hνeq : μ.withDensity (fun x => ENNReal.ofReal (ρ x)) = ν :=
    withDensity_ofReal_rnDeriv μ ν hac
  have hηeq : μ.withDensity (fun x => ENNReal.ofReal (h x)) = η := by
    calc
      _ = μ.withDensity (fun x => ENNReal.ofReal (η.rnDeriv μ x).toReal) :=
        withDensity_congr_ae (hh_eq.fun_comp ENNReal.ofReal)
      _ = η := withDensity_ofReal_rnDeriv μ η hηac
  have hD : ∃ D : ℝ, C < D ∧ μ {x | D ≤ ρ x} ≠ 0 := by
    by_contra hn
    push Not at hn
    have hae : ∀ᵐ x ∂μ, ρ x ≤ C := (ae_le_const_iff_forall_gt_measure_zero ρ C).mpr hn
    apply hbad
    rw [←hνeq,←withDensity_const]
    exact withDensity_mono (hae.mono fun x hx => ENNReal.ofReal_le_ofReal hx)
  obtain ⟨D,hDC,hDp⟩ := hD
  have hMi : (∫ x, h x ∂μ) = ∫ x in {x | C < ρ x}, ρ x ∂μ := by
    rw [integral_congr_ae hh_eq,Measure.integral_toReal_rnDeriv hηac,
      Measure.setIntegral_toReal_rnDeriv hac]
    exact congrArg ENNReal.toReal hmass
  obtain ⟨a,ha0,ha1,_,hp⟩ := exists_renyi_increasing_perturbation μ hρ hh hρ0 hh0
    Measure.integrable_toReal_rnDeriv hq0 hq1 hC hDC hhC hDp hMi
  refine ⟨a,ha0,ha1,?_⟩
  let p := fun x => entropyPerturb C a (ρ x) (h x)
  have hpM : Measurable p := by
    change Measurable ({x | C < ρ x}.piecewise (fun x => (1-a)*ρ x+a*h x)
      (fun x => ρ x+a*h x))
    exact ((hρ.const_mul _).add (hh.const_mul _)).piecewise
      (measurableSet_lt measurable_const hρ) (hρ.add (hh.const_mul _))
  have hp0 : ∀ x, 0 ≤ p x := fun x =>
    entropyPerturb_nonneg ha0.le ha1.le (hρ0 x) (hh0 x)
  have hpEq : μ.withDensity (fun x => ENNReal.ofReal (p x)) =
      ν-ENNReal.ofReal a • ν.restrict {x | C < ρ x}+ENNReal.ofReal a • η := by
    rw [entropyPerturb_withDensity μ hρ hh hρ0 hh0 Measure.integrable_toReal_rnDeriv
      C ha0.le ha1.le,hνeq,hηeq]
  have heq : (fun x => ((ν-ENNReal.ofReal a • ν.restrict {x | C < ρ x}+
      ENNReal.ofReal a • η).rnDeriv μ x).toReal) =ᵐ[μ] p := by
    rw [←hpEq]
    filter_upwards [Measure.rnDeriv_withDensity μ hpM.ennreal_ofReal] with x hx
    rw [hx,ENNReal.toReal_ofReal (hp0 x)]
  exact hp.trans_eq (integral_congr_ae (heq.fun_comp fun r => r^q)).symm

end RegularPointCoordinates

end

end OAI
