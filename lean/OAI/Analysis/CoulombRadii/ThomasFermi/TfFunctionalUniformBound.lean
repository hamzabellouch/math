import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.TfGradientField

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
omit [IsFiniteMeasure μ] in
lemma tfFunctional_uniform_bound {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f) :
    ∃ R : ℝ, 0 < R ∧ ∀ (L : TFLp μ →L[ℝ] ℝ), ‖L‖ ≤ K →
      ∀ f, tfFunctional c L B f ≤ 0 → ‖f‖ ≤ R := by
  obtain ⟨R,hR,hRb⟩ := tf_superlinear_bound hc hK
  refine ⟨R,hR,?_⟩
  intro L hL f hf
  by_contra! hn
  have H := hRb ‖f‖ hn.le
  have Hl := tfFunctional_lower (c := c) L B hB f
  have HK := mul_le_mul_of_nonneg_right hL (norm_nonneg f)
  linarith
omit [IsFiniteMeasure μ] in
lemma tfFunctional_minimizer_gap (c : ℝ) (L L' : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) {f g : TFLp μ}
    (hf : TFNonneg f) (hg : TFNonneg g)
    (hmf : ∀ h, TFNonneg h → tfFunctional c L B f ≤ tfFunctional c L B h)
    (hmg : ∀ h, TFNonneg h → tfFunctional c L' B g ≤ tfFunctional c L' B h)
    {R : ℝ} (hfR : ‖f‖ ≤ R) (hgR : ‖g‖ ≤ R) :
    (tfFunctional c L B f+tfFunctional c L B g)/2 -
      tfFunctional c L B ((1/2:ℝ) • (f+g)) ≤ R*‖L'-L‖ := by
  have Hm := hmf _ ((hf.add hg).smul (by norm_num : (0:ℝ)≤1/2))
  have Hg := hmg f hf
  have He : tfFunctional c L B g-tfFunctional c L B f =
      tfFunctional c L' B g-tfFunctional c L' B f+(L'-L) (g-f) := by
    simp only [tfFunctional,map_sub,_root_.sub_apply]
    ring
  have Hn : (L'-L) (g-f) ≤ ‖L'-L‖*(2*R) := by
    exact (le_abs_self _).trans ((L'-L).le_opNorm (g-f) |>.trans
      (mul_le_mul_of_nonneg_left ((norm_sub_le g f).trans (by linarith)) (norm_nonneg _)))
  nlinarith
lemma tfFunctional_minimizers_tendsto {ι : Type*} {l : Filter ι} {c : ℝ} (hc : 0 < c)
    {L : TFLp μ →L[ℝ] ℝ} {Ls : ι → TFLp μ →L[ℝ] ℝ} (hL : Tendsto Ls l (𝓝 L))
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f)
    {f : TFLp μ} {fs : ι → TFLp μ} (hf : TFNonneg f) (hfs : ∀ i, TFNonneg (fs i))
    (hmf : ∀ g, TFNonneg g → tfFunctional c L B f ≤ tfFunctional c L B g)
    (hmfs : ∀ i g, TFNonneg g → tfFunctional c (Ls i) B (fs i) ≤ tfFunctional c (Ls i) B g) :
    Tendsto fs l (𝓝 f) := by
  let K := ‖L‖+1
  obtain ⟨R,hR,hRb⟩ := tfFunctional_uniform_bound hc
    (show (0:ℝ) ≤ K by dsimp [K]; positivity) B hB
  have hmin0 (L' : TFLp μ →L[ℝ] ℝ) (f' : TFLp μ)
      (hm : ∀ g, TFNonneg g → tfFunctional c L' B f' ≤ tfFunctional c L' B g) :
      tfFunctional c L' B f' ≤ 0 := by
    have H := hm 0 tfNonneg_zero
    simpa [tfFunctional] using H
  have hfR : ‖f‖ ≤ R := hRb L (by dsimp [K]; linarith) f (hmin0 _ _ hmf)
  have hev : ∀ᶠ i in l, ‖fs i‖ ≤ R := by
    filter_upwards [hL.norm.eventually (gt_mem_nhds (show ‖L‖ < K by dsimp [K]; linarith))] with i hi
    exact hRb (Ls i) hi.le (fs i) (hmin0 _ _ (hmfs i))
  obtain ⟨C,hC,hCb⟩ := tfFunctional_gap_control hc L B hB hR
  have hlimit : Tendsto (fun i => C*(R*‖Ls i-L‖)^(5/6:ℝ)) l (𝓝 0) := by
    have H := (hL.sub_const L).norm
    have H1 : Tendsto (fun i => R*‖Ls i-L‖) l (𝓝 (0:ℝ)) := by simpa using H.const_mul R
    simpa using (H1.rpow_const (p := (5/6:ℝ)) (Or.inr (by norm_num))).const_mul C
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεp := Real.rpow_pos_of_pos hε (5/3:ℝ)
  filter_upwards [hev,hlimit.eventually (gt_mem_nhds hεp)] with i hi hlim
  have H := hCb f hf (fs i) (hfs i) hfR hi
  have Hgap := tfFunctional_minimizer_gap c L (Ls i) B hf (hfs i) hmf (hmfs i) hfR hi
  have Hnon := sub_nonneg.mpr (tfFunctional_midpoint_nonneg hc.le L B hB hf (hfs i))
  have Hup := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow Hnon Hgap (by norm_num : (0:ℝ)≤5/6)) hC.le
  have Hd : ‖f-fs i‖ < ε := (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le (by norm_num : (0:ℝ)<5/3)).mp
    (H.trans Hup |>.trans_lt hlim)
  simpa only [dist_eq_norm,norm_sub_rev] using Hd
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma tf_complementarity_solve {a r w : ℝ} (ha : 0 < a) (hr : 0 ≤ r)
    (hg : 0 ≤ a*r^(2/3:ℝ)-w) (hc : (a*r^(2/3:ℝ)-w)*r=0) :
    r = (max w 0/a)^(3/2:ℝ) ∧ a*r^(2/3:ℝ)-w = max (-w) 0 := by
  by_cases hz : r=0
  · subst r
    simp only [Real.zero_rpow (by norm_num : (2/3:ℝ)≠0),mul_zero,zero_sub] at hg ⊢
    have hw : w ≤ 0 := by linarith
    simp [max_eq_right hw,max_eq_left hg]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have he : a*r^(2/3:ℝ)-w=0 := (mul_eq_zero.mp hc).resolve_right hz
    have hw : 0 < w := by nlinarith [Real.rpow_pos_of_pos hrp (2/3:ℝ)]
    have hdiv : w/a=r^(2/3:ℝ) := (div_eq_iff ha.ne').mpr (by linarith [he])
    rw [max_eq_left hw.le,hdiv,←Real.rpow_mul hr]
    norm_num only [show (2/3:ℝ)*(3/2)=1 by norm_num,Real.rpow_one]
    exact ⟨True.intro,by rw [he,max_eq_right (by linarith)]⟩
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
lemma tfEuler_equation {c : ℝ} (hc : 0 < c) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    ∀ᵐ x ∂volume.restrict Ω,
      f x = (max (W x-tfPotential f x) 0/(c*(5/3:ℝ)))^(3/2:ℝ) ∧
      tfGradientField hΩ c W f x = max (tfPotential f x-W x) 0 := by
  filter_upwards [hf,tfEuler_complementarity hΩ c W hf hm,tfGradientField_coe hΩ c W hf] with x hx hh he
  have H := tf_complementarity_solve (show 0<c*(5/3:ℝ) by positivity) hx
    (show 0 ≤ c*(5/3:ℝ)*(f x)^(2/3:ℝ)-(W x-tfPotential f x) by linarith [hh.1])
    (by convert hh.2 using 1; ring)
  refine ⟨H.1,?_⟩
  calc
    _ = c*(5/3:ℝ)*(f x)^(2/3:ℝ)-(W x-tfPotential f x) := by rw [he]; ring
    _ = max (-(W x-tfPotential f x)) 0 := H.2
    _ = _ := by rw [neg_sub]
noncomputable def tfMinimizer {c : ℝ} (hc : 0 < c) (W : TFLq (volume.restrict Ω)) : TFLp (volume.restrict Ω) :=
  Classical.choose (tfEnergy_exists_unique_minimizer hΩ hc W)
lemma tfMinimizer_nonneg {c : ℝ} (hc : 0 < c) (W : TFLq (volume.restrict Ω)) :
    TFNonneg (tfMinimizer hΩ hc W) := (Classical.choose_spec (tfEnergy_exists_unique_minimizer hΩ hc W)).1.1
lemma tfMinimizer_min {c : ℝ} (hc : 0 < c) (W : TFLq (volume.restrict Ω)) :
    ∀ g, TFNonneg g → tfEnergy hΩ c W (tfMinimizer hΩ hc W) ≤ tfEnergy hΩ c W g :=
  (Classical.choose_spec (tfEnergy_exists_unique_minimizer hΩ hc W)).1.2
lemma tfMinimizer_unique {c : ℝ} (hc : 0 < c) (W : TFLq (volume.restrict Ω))
    {g : TFLp (volume.restrict Ω)} (hg : TFNonneg g)
    (hm : ∀ f, TFNonneg f → tfEnergy hΩ c W g ≤ tfEnergy hΩ c W f) :
    g=tfMinimizer hΩ hc W := (Classical.choose_spec (tfEnergy_exists_unique_minimizer hΩ hc W)).2 g ⟨hg,hm⟩
lemma tfMinimizer_continuous {c : ℝ} (hc : 0 < c) : Continuous (tfMinimizer hΩ hc) := by
  rw [continuous_iff_continuousAt]
  intro W
  exact tfFunctional_minimizers_tendsto hc (tfFieldContinuous.continuous.tendsto W)
    (tfCoulombContinuous hΩ) (tfCoulomb_self_nonneg hΩ) (tfMinimizer_nonneg hΩ hc W)
    (tfMinimizer_nonneg hΩ hc) (tfMinimizer_min hΩ hc W) (tfMinimizer_min hΩ hc)
lemma tfMinimizer_measurable {c : ℝ} (hc : 0 < c) :
    @Measurable _ _ (borel (TFLq (volume.restrict Ω))) (borel (TFLp (volume.restrict Ω)))
      (tfMinimizer hΩ hc) := by
  let : MeasurableSpace (TFLq (volume.restrict Ω)) := borel _
  have : BorelSpace (TFLq (volume.restrict Ω)) := ⟨rfl⟩
  let : MeasurableSpace (TFLp (volume.restrict Ω)) := borel _
  have : BorelSpace (TFLp (volume.restrict Ω)) := ⟨rfl⟩
  exact (tfMinimizer_continuous hΩ hc).measurable
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma tf_power_tangent {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 ≤ s^(5/3:ℝ)-r^(5/3:ℝ)-(5/3:ℝ)*r^(2/3:ℝ)*(s-r) := by
  have H := Real.young_inequality_of_nonneg (Real.rpow_nonneg hr (2/3:ℝ)) hs coulomb_holder_exponents
  rw [←Real.rpow_mul hr] at H
  norm_num only [show (2/3:ℝ)*(5/2)=5/3 by norm_num] at H
  have he := Real.rpow_add_one' hr (by norm_num : (2/3:ℝ)+1≠0)
  norm_num at he
  nlinarith
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
noncomputable def tfBregman (f g : TFLp μ) : ℝ :=
  ‖g‖^(5/3:ℝ)-‖f‖^(5/3:ℝ)-(5/3:ℝ)*tfFieldContinuous (tfKineticField f) (g-f)
lemma tfKinetic_pair_integrable {f : TFLp μ} (hf : TFNonneg f) (g : TFLp μ) :
    Integrable (fun x => (f x)^(2/3:ℝ)*g x) μ := by
  apply (tfFieldPairing_integrable (tfKineticField f) g).congr
  filter_upwards [tfKineticField_coe f,hf] with x hx hy
  rw [hx,Real.norm_of_nonneg hy]
lemma tfBregman_integrable {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) :
    Integrable (fun x => (g x)^(5/3:ℝ)-(f x)^(5/3:ℝ)-
      (5/3:ℝ)*(f x)^(2/3:ℝ)*(g x-f x)) μ := by
  have hi := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) (Lp.memLp f) hf
  have hj := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) (Lp.memLp g) hg
  have hk := (tfKinetic_pair_integrable hf (g-f)).const_mul (5/3:ℝ)
  apply (hj.sub hi |>.sub hk).congr
  filter_upwards [Lp.coeFn_sub g f] with x hx
  simp only [hx,Pi.sub_apply,mul_assoc]
lemma tfBregman_formula {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) :
    tfBregman f g = ∫ x, (g x)^(5/3:ℝ)-(f x)^(5/3:ℝ)-
      (5/3:ℝ)*(f x)^(2/3:ℝ)*(g x-f x) ∂μ := by
  have hi := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) (Lp.memLp f) hf
  have hj := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) (Lp.memLp g) hg
  have hk := (tfKinetic_pair_integrable hf (g-f)).const_mul (5/3:ℝ)
  have hij : Integrable (fun x => (g x)^(5/3:ℝ)-(f x)^(5/3:ℝ)) μ := hj.sub hi
  unfold tfBregman
  rw [←tfLp_nonneg_power hf,←tfLp_nonneg_power hg,tfKineticField_pair hf,←integral_const_mul,
    ←integral_sub hj hi,←integral_sub hij hk]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub g f] with x hx
  simp only [hx,Pi.sub_apply,mul_assoc]
lemma tfBregman_nonneg {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) :
    0 ≤ tfBregman f g := by
  rw [tfBregman_formula hf hg]
  apply integral_nonneg_of_ae
  filter_upwards [hf,hg] with x hx hy
  exact tf_power_tangent hx hy
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
lemma tfEnergy_expansion (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfEnergy hΩ c W g-tfEnergy hΩ c W f =
      tfCoulomb Ω (g-f) (g-f)/2+c*tfBregman f g+
        tfFieldContinuous (tfGradientField hΩ c W f) (g-f) := by
  rw [tfGradientField_pair hΩ c W hf,←tfKineticField_pair hf]
  change tfFunctional c (tfFieldContinuous W) (tfCoulombContinuous hΩ) g-
    tfFunctional c (tfFieldContinuous W) (tfCoulombContinuous hΩ) f = _
  have he : tfCoulomb Ω (g-f) (g-f) = tfCoulomb Ω g g-tfCoulomb Ω g f-
      tfCoulomb Ω f g+tfCoulomb Ω f f := by
    change (tfCoulombContinuous hΩ) (g-f) (g-f) = _
    simp only [map_sub,_root_.sub_apply]
    change tfCoulomb Ω g g-tfCoulomb Ω f g-(tfCoulomb Ω g f-tfCoulomb Ω f f) = _
    ring
  have he' : tfCoulomb Ω (g-f) f = tfCoulomb Ω g f-tfCoulomb Ω f f := by
    change (tfCoulombContinuous hΩ) (g-f) f = _
    simp only [map_sub,_root_.sub_apply]
    rfl
  rw [he,he',tfCoulomb_symm f g]
  simp only [tfFunctional,tfBregman,map_sub]
  change c*‖g‖^(5/3:ℝ)-tfFieldContinuous W g+tfCoulomb Ω g g/2 -
    (c*‖f‖^(5/3:ℝ)-tfFieldContinuous W f+tfCoulomb Ω f f/2) = _
  ring
lemma tfEnergy_minimizer_expansion {c : ℝ} (hc : 0 < c) (W : TFLq (volume.restrict Ω))
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ h, TFNonneg h → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W h) :
    tfEnergy hΩ c W g-tfEnergy hΩ c W f =
      tfCoulomb Ω (g-f) (g-f)/2+c*tfBregman f g+
        ∫ x in Ω, max (tfPotential f x-W x) 0*g x := by
  rw [tfEnergy_expansion hΩ c W hf,map_sub,tfGradientField_self hΩ c W hf hm,sub_zero,
    tfFieldContinuous_apply]
  congr 1
  apply integral_congr_ae
  filter_upwards [tfEuler_equation hΩ hc W hf hm] with x hx
  rw [hx.2]
lemma tfEnergy_gap_controls (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (hg : TFNonneg g)
    (hm : ∀ h, TFNonneg h → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W h) :
    tfCoulomb Ω (g-f) (g-f)/2+c*tfBregman f g ≤ tfEnergy hΩ c W g-tfEnergy hΩ c W f := by
  rw [tfEnergy_expansion hΩ c W hf,map_sub,tfGradientField_self hΩ c W hf hm,sub_zero]
  apply le_add_of_nonneg_right
  rw [tfFieldContinuous_apply]
  apply integral_nonneg_of_ae
  filter_upwards [tfGradientField_nonneg hΩ c W hf hm,hg] with x hx hy
  exact mul_nonneg hx hy
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
