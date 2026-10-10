import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TfFunctional
import OAI.Analysis.CoulombRadii.FieldAnalysis.MinimizerMidpointControl

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
lemma tfFunctional_gap_control {c : ℝ} (hc : 0 < c) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f)
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ f, TFNonneg f → ∀ g, TFNonneg g → ‖f‖ ≤ R → ‖g‖ ≤ R →
      ‖f-g‖^(5/3:ℝ) ≤ C * ((tfFunctional c L B f+tfFunctional c L B g)/2 -
        tfFunctional c L B ((1/2:ℝ) • (f+g)))^(5/6:ℝ) := by
  let A : ℝ := (36/5:ℝ)/c
  let U : ℝ := 2*R+‖(tfOne : TFLp μ)‖
  have hA : 0 < A := div_pos (by norm_num) hc
  have hU : 0 < U := by dsimp [U]; linarith [norm_nonneg (tfOne : TFLp μ)]
  refine ⟨A^(5/6:ℝ)*U^(5/18:ℝ),mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hU _),?_⟩
  intro f hf g hg hfR hgR
  let d := (‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2 - ‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ)
  let e := (tfFunctional c L B f+tfFunctional c L B g)/2 - tfFunctional c L B ((1/2:ℝ) • (f+g))
  have hd : 0 ≤ d := tfLp_gap_nonneg hf hg
  have he : 0 ≤ e := sub_nonneg.mpr (tfFunctional_midpoint_nonneg hc.le L B hB hf hg)
  have hde : c*d ≤ e := by
    have H := tfFunctional_midpoint c L B f g
    have HB := hB (f-g)
    dsimp [d,e]
    linarith
  have hAc : A*c = 36/5 := by dsimp [A]; field_simp
  have hbase : (36/5:ℝ)*d ≤ A*e := by
    have H := mul_le_mul_of_nonneg_left hde hA.le
    nlinarith
  have hp := Real.rpow_le_rpow (mul_nonneg (by norm_num : (0:ℝ)≤36/5) hd) hbase
    (by norm_num : (0:ℝ)≤5/6)
  have hn : ‖f‖+‖g‖+‖(tfOne : TFLp μ)‖ ≤ U := by dsimp [U]; linarith
  have hnp := Real.rpow_le_rpow (by positivity : 0 ≤ ‖f‖+‖g‖+‖(tfOne : TFLp μ)‖) hn
    (by norm_num : (0:ℝ)≤5/18)
  calc
    _ ≤ ((36/5:ℝ)*d)^(5/6:ℝ)*(‖f‖+‖g‖+‖(tfOne : TFLp μ)‖)^(5/18:ℝ) := tfLp_midpoint_gap hf hg
    _ ≤ (A*e)^(5/6:ℝ)*U^(5/18:ℝ) := mul_le_mul hp hnp (by positivity) (by positivity)
    _ = _ := by rw [Real.mul_rpow hA.le he]; ring
lemma tfFunctional_exists_minimizer {c : ℝ} (hc : 0 < c) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f) :
    ∃ f : TFLp μ, TFNonneg f ∧ ∀ g, TFNonneg g → tfFunctional c L B f ≤ tfFunctional c L B g := by
  apply exists_minimizer_of_midpoint_control tfNonneg_closed ⟨0,tfNonneg_zero⟩
    (fun f hf g hg => (hf.add hg).smul (by norm_num : (0:ℝ)≤1/2))
    (tfFunctional_continuous c L B) (tfFunctional_bddBelow hc L B hB _)
    (fun f hf g hg => tfFunctional_midpoint_nonneg hc.le L B hB hf hg)
  · intro a
    obtain ⟨R,hR,hRb⟩ := tfFunctional_sublevel_bound hc L B hB a
    exact ⟨R,hR,fun f _ => hRb f⟩
  · exact fun R hR => tfFunctional_gap_control hc L B hB hR
lemma tfFunctional_minimizer_unique {c : ℝ} (hc : 0 < c) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f)
    {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g)
    (hfm : ∀ h, TFNonneg h → tfFunctional c L B f ≤ tfFunctional c L B h)
    (hgm : ∀ h, TFNonneg h → tfFunctional c L B g ≤ tfFunctional c L B h) : f = g := by
  have hfg : tfFunctional c L B f = tfFunctional c L B g := le_antisymm (hfm g hg) (hgm f hf)
  have hmid := hfm ((1/2:ℝ) • (f+g)) ((hf.add hg).smul (by norm_num : (0:ℝ)≤1/2))
  have hmid' := tfFunctional_midpoint_nonneg hc.le L B hB hf hg
  have he : (tfFunctional c L B f+tfFunctional c L B g)/2 - tfFunctional c L B ((1/2:ℝ) • (f+g)) = 0 := by
    linarith
  obtain ⟨C,hC,hCb⟩ := tfFunctional_gap_control hc L B hB
    (show (0:ℝ)<‖f‖+‖g‖+1 by positivity)
  have H := hCb f hf g hg (by linarith [norm_nonneg g]) (by linarith [norm_nonneg f])
  rw [he,Real.zero_rpow (by norm_num : (5/6:ℝ) ≠ 0),mul_zero] at H
  have hz : ‖f-g‖^(5/3:ℝ) = 0 := le_antisymm H (Real.rpow_nonneg (norm_nonneg _) _)
  have hn : ‖f-g‖ = 0 := (Real.rpow_eq_zero (norm_nonneg _) (by norm_num : (5/3:ℝ)≠0)).mp hz
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
noncomputable abbrev TFFieldExponent : ℝ≥0∞ := ENNReal.ofReal (5/2:ℝ)
instance : Fact (1 ≤ TFFieldExponent) := ⟨by norm_num [TFFieldExponent]⟩
noncomputable abbrev TFLq {α : Type*} [MeasurableSpace α] (μ : Measure α) := Lp ℝ TFFieldExponent μ
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
lemma tfLq_norm (W : TFLq μ) :
    ‖W‖ = (∫ x, ‖W x‖^(5/2:ℝ) ∂μ)^(2/5:ℝ) := by
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num [TFFieldExponent]) (by simp)
      (Lp.memLp W).aestronglyMeasurable]
  norm_num [TFFieldExponent]
noncomputable def tfFieldPairing (W : TFLq μ) (f : TFLp μ) : ℝ := ∫ x, W x*f x ∂μ
lemma tfFieldPairing_integrable (W : TFLq μ) (f : TFLp μ) : Integrable (fun x => W x*f x) μ := by
  have : ENNReal.HolderConjugate TFFieldExponent TFExponent := coulomb_holder_exponents.ennrealOfReal
  exact (Lp.memLp W).integrable_mul (Lp.memLp f)
lemma tfFieldPairing_bound (W : TFLq μ) (f : TFLp μ) : ‖tfFieldPairing W f‖ ≤ ‖W‖*‖f‖ := by
  have H := integral_mul_norm_le_Lp_mul_Lq coulomb_holder_exponents (Lp.memLp W) (Lp.memLp f)
  rw [tfLq_norm,tfLp_norm]
  calc
    _ ≤ ∫ x, ‖W x*f x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖W x‖*‖f x‖ ∂μ := by simp only [norm_mul]
    _ ≤ _ := by convert H using 1; norm_num
lemma tfFieldPairing_add_left (U W : TFLq μ) (f : TFLp μ) :
    tfFieldPairing (U+W) f = tfFieldPairing U f+tfFieldPairing W f := by
  unfold tfFieldPairing
  rw [← integral_add (tfFieldPairing_integrable U f) (tfFieldPairing_integrable W f)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add U W] with x hx
  simp only [hx,Pi.add_apply,add_mul]
lemma tfFieldPairing_smul_left (c : ℝ) (W : TFLq μ) (f : TFLp μ) :
    tfFieldPairing (c • W) f = c*tfFieldPairing W f := by
  unfold tfFieldPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c W] with x hx
  simp only [hx,Pi.smul_apply,smul_eq_mul,mul_assoc]
lemma tfFieldPairing_add_right (W : TFLq μ) (f g : TFLp μ) :
    tfFieldPairing W (f+g) = tfFieldPairing W f+tfFieldPairing W g := by
  unfold tfFieldPairing
  rw [← integral_add (tfFieldPairing_integrable W f) (tfFieldPairing_integrable W g)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with x hx
  simp only [hx,Pi.add_apply,mul_add]
lemma tfFieldPairing_smul_right (c : ℝ) (W : TFLq μ) (f : TFLp μ) :
    tfFieldPairing W (c • f) = c*tfFieldPairing W f := by
  unfold tfFieldPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp only [hx,Pi.smul_apply,smul_eq_mul]
  ring
noncomputable def tfFieldLinear : TFLq μ →ₗ[ℝ] TFLp μ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ tfFieldPairing tfFieldPairing_add_left tfFieldPairing_smul_left
    tfFieldPairing_add_right tfFieldPairing_smul_right
noncomputable def tfFieldContinuous : TFLq μ →L[ℝ] TFLp μ →L[ℝ] ℝ :=
  tfFieldLinear.mkContinuous₂ 1 (fun W f => by
    change ‖tfFieldPairing W f‖ ≤ 1*‖W‖*‖f‖
    simpa only [one_mul] using tfFieldPairing_bound W f)
lemma tfFieldContinuous_apply (W : TFLq μ) (f : TFLp μ) :
    tfFieldContinuous W f = ∫ x, W x*f x ∂μ := rfl
lemma tfFieldContinuous_bound (W : TFLq μ) : ‖tfFieldContinuous W‖ ≤ ‖W‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (tfFieldContinuous W) (norm_nonneg W) (fun f => ?_)
  rw [tfFieldContinuous_apply]
  exact tfFieldPairing_bound W f
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
noncomputable def tfEnergy (c : ℝ) (W : TFLq (volume.restrict Ω))
    (f : TFLp (volume.restrict Ω)) : ℝ :=
  tfFunctional c (tfFieldContinuous W) (tfCoulombContinuous hΩ) f
lemma tfEnergy_formula (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfEnergy hΩ c W f = c*(∫ x in Ω, (f x)^(5/3:ℝ)) -
      (∫ x in Ω, W x*f x) + tfCoulomb Ω f f/2 := by
  unfold tfEnergy tfFunctional
  rw [tfLp_nonneg_power hf]
  rfl
lemma tfEnergy_exists_unique_minimizer {c : ℝ} (hc : 0 < c)
    (W : TFLq (volume.restrict Ω)) :
    ∃! f : TFLp (volume.restrict Ω), TFNonneg f ∧
      ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g := by
  have hB : ∀ f, 0 ≤ (tfCoulombContinuous hΩ) f f := tfCoulomb_self_nonneg hΩ
  obtain ⟨f,hf,hfm⟩ := tfFunctional_exists_minimizer hc (tfFieldContinuous W) (tfCoulombContinuous hΩ) hB
  refine ⟨f,⟨hf,hfm⟩,?_⟩
  rintro g ⟨hg,hgm⟩
  exact tfFunctional_minimizer_unique hc _ _ hB hg hf hgm hfm
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
