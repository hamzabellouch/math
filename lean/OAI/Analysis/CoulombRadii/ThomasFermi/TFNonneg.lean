import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TFExponent

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
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
def TFNonneg (f : TFLp μ) : Prop := ∀ᵐ x ∂μ, 0 ≤ f x
lemma tfNonneg_zero : TFNonneg (0 : TFLp μ) := by
  change ∀ᵐ x ∂μ, 0 ≤ (0 : Lp ℝ TFExponent μ) x
  filter_upwards [Lp.coeFn_zero ℝ TFExponent μ] with x hx
  rw [hx]
  rfl
lemma TFNonneg.add {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) : TFNonneg (f+g) := by
  filter_upwards [hf,hg,Lp.coeFn_add f g] with x hx hy hz
  simpa only [hz, Pi.add_apply] using add_nonneg hx hy
lemma TFNonneg.smul {f : TFLp μ} (hf : TFNonneg f) {c : ℝ} (hc : 0 ≤ c) : TFNonneg (c • f) := by
  filter_upwards [hf,Lp.coeFn_smul c f] with x hx hz
  simpa only [hz, Pi.smul_apply, smul_eq_mul] using mul_nonneg hc hx
lemma tfNonneg_closed : IsClosed {f : TFLp μ | TFNonneg f} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨ns, hns, hn⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  filter_upwards [hn, ae_all_iff.mpr hf] with x hx hy
  exact ge_of_tendsto hx (Filter.Eventually.of_forall (fun n => hy (ns n)))
lemma tfLp_nonneg_power {f : TFLp μ} (hf : TFNonneg f) :
    (∫ x, (f x)^(5/3:ℝ) ∂μ) = ‖f‖^(5/3:ℝ) := by
  rw [tfLp_norm_power]
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  rw [Real.norm_of_nonneg hx]
lemma tfLp_midpoint_power {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) :
    (∫ x, ((f x+g x)/2)^(5/3:ℝ) ∂μ) = ‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ) := by
  rw [← tfLp_nonneg_power ((hf.add hg).smul (by norm_num : (0:ℝ)≤1/2))]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul (1/2:ℝ) (f+g), Lp.coeFn_add f g] with x hx hy
  simp only [hx,hy,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  congr 1; ring
noncomputable def tfOne [IsFiniteMeasure μ] : TFLp μ :=
  (memLp_const (p := TFExponent) (1:ℝ)).toLp (fun _ => 1)
lemma tfOne_coe [IsFiniteMeasure μ] : (tfOne : TFLp μ) =ᵐ[μ] fun _ => 1 :=
  MemLp.coeFn_toLp _
lemma tfNonneg_one [IsFiniteMeasure μ] : TFNonneg (tfOne : TFLp μ) := by
  filter_upwards [tfOne_coe (μ := μ)] with x hx
  simp [hx]
lemma tfLp_gap_nonneg {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) :
    0 ≤ (‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2 - ‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ) := by
  rw [← tfLp_nonneg_power hf, ← tfLp_nonneg_power hg, ← tfLp_midpoint_power hf hg]
  have hi := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) (Lp.memLp f) hf
  have hj := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) (Lp.memLp g) hg
  have hk : Integrable (fun x => ((f x+g x)/2)^(5/3:ℝ)) μ := by
    apply integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3)
      (by simpa only [TFExponent,div_eq_mul_inv, Pi.add_apply] using ((Lp.memLp f).add (Lp.memLp g)).mul_const (2:ℝ)⁻¹)
      (by filter_upwards [hf,hg] with x hx hy; positivity)
  rw [← integral_add hi hj, ← integral_div, ← integral_sub (by exact (hi.add hj).div_const 2) hk]
  apply integral_nonneg_of_ae
  filter_upwards [hf,hg] with x hx hy
  exact tf_midpoint_gap_nonneg hx hy
lemma tfLp_midpoint_gap [IsFiniteMeasure μ] {f g : TFLp μ}
    (hf : TFNonneg f) (hg : TFNonneg g) :
    ‖f-g‖^(5/3:ℝ) ≤
      ((36/5:ℝ)*((‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2 - ‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ)))^(5/6:ℝ) *
        (‖f‖+‖g‖+‖(tfOne : TFLp μ)‖)^(5/18:ℝ) := by
  have H := tf_integrated_midpoint_gap (Lp.memLp f) (Lp.memLp g) hf hg
  rw [tfLp_nonneg_power hf, tfLp_nonneg_power hg, tfLp_midpoint_power hf hg] at H
  have he : (∫ x, ‖f x-g x‖^(5/3:ℝ) ∂μ) = ‖f-g‖^(5/3:ℝ) := by
    rw [tfLp_norm_power]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f g] with x hx
    rw [hx]; rfl
  rw [he] at H
  have hi : (∫ x, (f x+g x+1)^(5/3:ℝ) ∂μ) = ‖f+g+tfOne‖^(5/3:ℝ) := by
    rw [← tfLp_nonneg_power ((hf.add hg).add tfNonneg_one)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (f+g) tfOne,Lp.coeFn_add f g,tfOne_coe (μ := μ)] with x hx hy hz
    simp only [hx,hy,hz,Pi.add_apply]
  rw [hi, ← Real.rpow_mul (norm_nonneg _)] at H
  have hnorm : ‖f+g+tfOne‖ ≤ ‖f‖+‖g‖+‖(tfOne : TFLp μ)‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le f g) le_rfl)
  have hnormp := Real.rpow_le_rpow (norm_nonneg _) hnorm (by norm_num : (0:ℝ)≤5/18)
  have hg0 := tfLp_gap_nonneg hf hg
  have hp : 0 ≤ (36/5:ℝ)*((‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2-‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ)) :=
    mul_nonneg (by norm_num) hg0
  have hb : (36/5:ℝ)*(‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2-(36/5:ℝ)*‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ) =
      (36/5:ℝ)*((‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2-‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ)) := by ring
  rw [hb, show (5/3:ℝ)*(1/6)=5/18 by norm_num] at H
  exact H.trans (mul_le_mul_of_nonneg_left hnormp (Real.rpow_nonneg hp _))
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma tfExtend_add_ae {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (f g : TFLp (volume.restrict Ω)) :
    tfExtend Ω (f+g) =ᵐ[volume] fun x => tfExtend Ω f x + tfExtend Ω g x := by
  filter_upwards [(ae_restrict_iff' hΩ).mp (Lp.coeFn_add f g)] with x hx
  by_cases h : x ∈ Ω
  · simpa only [tfExtend, Set.indicator_of_mem h, Pi.add_apply] using hx h
  · simp [tfExtend, h]
lemma tfExtend_smul_ae {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (c : ℝ) (f : TFLp (volume.restrict Ω)) :
    tfExtend Ω (c • f) =ᵐ[volume] fun x => c * tfExtend Ω f x := by
  filter_upwards [(ae_restrict_iff' hΩ).mp (Lp.coeFn_smul c f)] with x hx
  by_cases h : x ∈ Ω
  · simpa only [tfExtend, Set.indicator_of_mem h, Pi.smul_apply, smul_eq_mul] using hx h
  · simp [tfExtend, h]
lemma tfCoulomb_symm {Ω : Set Space} (f g : TFLp (volume.restrict Ω)) :
    tfCoulomb Ω f g = tfCoulomb Ω g f := by
  unfold tfCoulomb
  rw [Measure.volume_eq_prod]
  rw [← integral_prod_swap (fun p : Space × Space => tfExtend Ω g p.1*tfExtend Ω f p.2*coulombKernel (p.1-p.2))]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [Prod.swap, coulombKernel, norm_sub_rev]
  ring
lemma tfCoulomb_add_left {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (f g h : TFLp (volume.restrict Ω)) :
    tfCoulomb Ω (f+g) h = tfCoulomb Ω f h + tfCoulomb Ω g h := by
  have H := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space)) (ν := (volume : Measure Space))).ae_eq_comp (tfExtend_add_ae hΩ f g)
  change _ =ᵐ[(volume : Measure Space).prod volume] _ at H
  unfold tfCoulomb
  rw [← integral_add (tfCoulomb_integrable hΩ f h) (tfCoulomb_integrable hΩ g h)]
  apply integral_congr_ae
  filter_upwards [H] with p hp
  dsimp only [Function.comp_def] at hp
  rw [hp]
  ring
lemma tfCoulomb_smul_left {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (c : ℝ) (f g : TFLp (volume.restrict Ω)) :
    tfCoulomb Ω (c • f) g = c * tfCoulomb Ω f g := by
  have H := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space)) (ν := (volume : Measure Space))).ae_eq_comp (tfExtend_smul_ae hΩ c f)
  change _ =ᵐ[(volume : Measure Space).prod volume] _ at H
  unfold tfCoulomb
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [H] with p hp
  dsimp only [Function.comp_def] at hp
  rw [hp]
  ring
lemma tfCoulomb_bound {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (f g : TFLp (volume.restrict Ω)) :
    ‖tfCoulomb Ω f g‖ ≤
      ((volume.real Ω)^(2/5:ℝ)*((8*Real.pi)^(2/5:ℝ)+(volume.real Ω)^(2/5:ℝ)))*‖f‖*‖g‖ := by
  let A := ((8*Real.pi)^(2/5:ℝ)+(volume.real Ω)^(2/5:ℝ))*‖g‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hi := (tfCoulomb_integrable hΩ f g).norm
  have hiter : (∫ p : Space × Space, ‖tfExtend Ω f p.1*tfExtend Ω g p.2*coulombKernel (p.1-p.2)‖) =
      ∫ x, ‖tfExtend Ω f x‖*(∫ y, coulombKernel (x-y)*‖tfExtend Ω g y‖) := by
    rw [Measure.volume_eq_prod, integral_prod _ hi]
    congr 1; funext x
    simp_rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)]
    simp_rw [mul_assoc, mul_comm ‖tfExtend Ω g _‖ (coulombKernel _)]
    rw [integral_const_mul]
  calc
    _ ≤ ∫ p : Space × Space, ‖tfExtend Ω f p.1*tfExtend Ω g p.2*coulombKernel (p.1-p.2)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := hiter
    _ ≤ ∫ x, ‖tfExtend Ω f x‖*A := by
      apply integral_mono
      · convert hi.integral_prod_left using 1
        funext x
        simp_rw [norm_mul, Real.norm_of_nonneg (coulombKernel_nonneg _)]
        simp_rw [mul_assoc, mul_comm ‖tfExtend Ω g _‖ (coulombKernel _)]
        rw [integral_const_mul]
      · exact (tfExtend_integrable hΩ f).norm.mul_const A
      · intro x
        exact mul_le_mul_of_nonneg_left (tfExtend_convolution_bound hΩ g x) (norm_nonneg _)
    _ = (∫ x in Ω, ‖f x‖)*A := by rw [integral_mul_const, tfExtend_norm_integral hΩ]
    _ ≤ ((volume.real Ω)^(2/5:ℝ)*‖f‖)*A := by
      apply mul_le_mul_of_nonneg_right _ hA
      simpa only [Measure.real, Measure.restrict_apply_univ] using tfLp_integral_norm_le f
    _ = _ := by dsimp [A]; ring
noncomputable def tfCoulombLinear {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] :
    TFLp (volume.restrict Ω) →ₗ[ℝ] TFLp (volume.restrict Ω) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (tfCoulomb Ω) (tfCoulomb_add_left hΩ)
    (fun c f g => tfCoulomb_smul_left hΩ c f g)
    (fun f g h => by rw [tfCoulomb_symm, tfCoulomb_add_left hΩ, tfCoulomb_symm g, tfCoulomb_symm h])
    (fun c f g => by rw [tfCoulomb_symm, tfCoulomb_smul_left hΩ, tfCoulomb_symm g]; rfl)
noncomputable def tfCoulombContinuous {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] :
    TFLp (volume.restrict Ω) →L[ℝ] TFLp (volume.restrict Ω) →L[ℝ] ℝ :=
  (tfCoulombLinear hΩ).mkContinuous₂
    ((volume.real Ω)^(2/5:ℝ)*((8*Real.pi)^(2/5:ℝ)+(volume.real Ω)^(2/5:ℝ)))
    (tfCoulomb_bound hΩ)
lemma tfCoulomb_continuous {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] :
    Continuous (fun p : TFLp (volume.restrict Ω) × TFLp (volume.restrict Ω) => tfCoulomb Ω p.1 p.2) :=
  (tfCoulombContinuous hΩ).continuous₂
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
