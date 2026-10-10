import Mathlib
import OAI.Probability.SphericalField.Poisson.Superposition
import OAI.Probability.SphericalField.Gibbs.Thermal

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace

namespace SphericalPerceptron
section ThermalL1
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_mean_centered_abs_sq_le {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A) (hYB : ∀ x, |Y x| ≤ B) :
    (tiltMean μ H (fun x => |Y x-tiltMean μ H Y 1|) 1)^2 ≤
      tiltMean μ H (fun x => Y x*Y x) 1-(tiltMean μ H Y 1)^2 := by
  have := tilt_law_probability μ hH hA hHA 1
  let ν := tiltLaw μ H 1
  have hLp : MemLp Y 2 ν := MemLp.of_bound hY.aestronglyMeasurable B (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hYB x)
  have hh := integral_centered_abs_le_sqrt_variance ν hLp
  have hnon : 0 ≤ ∫ x, |Y x-∫ y, Y y ∂ν| ∂ν := integral_nonneg fun _ => abs_nonneg _
  have hsq := pow_le_pow_left₀ hnon hh 2
  rw [Real.sq_sqrt (variance_nonneg Y ν),variance_eq_sub hLp] at hsq
  simp only [Pi.pow_apply] at hsq
  change (∫ x, |Y x-∫ y, Y y ∂tiltLaw μ H 1| ∂tiltLaw μ H 1)^2 ≤
    (∫ x, (Y x)^2 ∂tiltLaw μ H 1) - (∫ x, Y x ∂tiltLaw μ H 1)^2 at hsq
  simp_rw [tilt_law_integral μ hH hA hHA 1] at hsq
  simpa only [pow_two] using hsq

omit [IsProbabilityMeasure μ] in
lemma tiltMean_nonneg {H F : S → ℝ} (hF : ∀ x, 0 ≤ F x) (t : ℝ) : 0 ≤ tiltMean μ H F t := by
  exact div_nonneg (integral_nonneg fun x => mul_nonneg (Real.exp_pos _).le (hF x))
    (integral_nonneg fun _ => (Real.exp_pos _).le)

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma annealed_thermal_abs_sq_le {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    {A B : Ω → ℝ} (hA : ∀ ω, 0 ≤ A ω) (hB : ∀ ω, 0 ≤ B ω)
    (hHA : ∀ ω x, |H ω x| ≤ A ω) (hYB : ∀ ω x, |Y ω x| ≤ B ω)
    (hB2 : MemLp B 2 P) (t : ℝ) :
    (∫ ω, tiltMean μ (fun x => H ω x+t*Y ω x)
      (fun x => |Y ω x-tiltMean μ (fun x => H ω x+t*Y ω x) (Y ω) 1|) 1 ∂P)^2 ≤
        ∫ ω, thermalVar μ (H ω) (Y ω) t ∂P := by
  let T := fun ω x => H ω x+t*Y ω x
  let M := fun ω => tiltMean μ (T ω) (Y ω) 1
  let U := fun ω => tiltMean μ (T ω) (fun x => |Y ω x-M ω|) 1
  have hT : Measurable (Function.uncurry T) := hH.add (hY.const_mul t)
  have hM : Measurable M := measurable_tiltMean_param μ hT hY
  have hU : Measurable U := measurable_tiltMean_param μ hT ((hY.sub (hM.comp measurable_fst)).abs)
  have hTm (ω) : Measurable (T ω) := hT.comp (measurable_const.prodMk measurable_id)
  have hYm (ω) : Measurable (Y ω) := hY.comp (measurable_const.prodMk measurable_id)
  have hTB (ω x) : |T ω x| ≤ A ω+|t| * B ω := affinePotential_bound (hHA ω) (hYB ω) t x
  have hTp (ω) : 0 ≤ A ω+|t| * B ω := add_nonneg (hA ω) (mul_nonneg (abs_nonneg _) (hB ω))
  have hMB (ω) : |M ω| ≤ B ω := tilt_mean_bound μ (hTm ω) (hYm ω) (hTp ω) (hB ω) (hTB ω) (hYB ω) 1
  have hUB (ω) : |U ω| ≤ 2*B ω := by
    apply tilt_mean_bound μ (hTm ω) ((hYm ω).sub_const (M ω) |>.abs) (hTp ω) (mul_nonneg (by norm_num) (hB ω)) (hTB ω) _ 1
    intro x
    rw [abs_abs]
    exact (abs_sub _ _).trans (by linarith [hYB ω x,hMB ω])
  have hULp : MemLp U 2 P := (hB2.const_mul 2).mono' hU.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hUB ω)
  have hv := variance_nonneg U P
  rw [variance_eq_sub hULp] at hv
  have hIvar : Integrable (fun ω => thermalVar μ (H ω) (Y ω) t) P :=
    ((memLp_two_iff_integrable_sq hB2.aestronglyMeasurable).mp hB2 |>.const_mul 2).mono'
      (measurable_thermalVar μ hH hY t).aestronglyMeasurable (ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs] using thermalVar_bound μ
          (show Measurable (H ω) from hH.comp (measurable_const.prodMk measurable_id)) (hYm ω) (hA ω) (hB ω) (hHA ω) (hYB ω) t)
  have hsq : (∫ ω, U ω^2 ∂P) ≤ ∫ ω, thermalVar μ (H ω) (Y ω) t ∂P := by
    apply integral_mono ((memLp_two_iff_integrable_sq hULp.aestronglyMeasurable).mp hULp) hIvar
    intro ω
    exact tilt_mean_centered_abs_sq_le μ (hTm ω) (hYm ω) (hTp ω) (hTB ω) (hYB ω)
  simp only [Pi.pow_apply] at hv
  change (∫ ω, U ω ∂P)^2 ≤ _
  linarith

end ThermalL1
end SphericalPerceptron

namespace SphericalPerceptron
section ContactL1Complete
variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable (μ : Measure S) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
lemma affineLogRoot_memLp {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    {A B : Ω → ℝ} (hA : ∀ ω, 0 ≤ A ω) (hB : ∀ ω, 0 ≤ B ω)
    (hHA : ∀ ω x, |H ω x| ≤ A ω) (hYB : ∀ ω x, |Y ω x| ≤ B ω)
    {p : ℝ≥0∞} (hAp : MemLp A p P) (hBp : MemLp B p P) (t : ℝ) :
    MemLp (fun ω => affineLogRoot μ (H ω) (Y ω) t) p P := by
  apply (hAp.add (hBp.const_mul |t|)).mono' (measurable_affineLogRoot μ hH hY t).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    simpa only [affineLogRoot,Real.norm_eq_abs,Pi.add_def] using tilt_log_partition_bound μ
      (show Measurable (fun x => H ω x+t*Y ω x) from
        (hH.comp (measurable_const.prodMk measurable_id)).add
          ((hY.comp (measurable_const.prodMk measurable_id)).const_mul t))
      (add_nonneg (hA ω) (mul_nonneg (abs_nonneg _) (hB ω))) (affinePotential_bound (hHA ω) (hYB ω) t)

lemma tilt_mean_center_triangle {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A) (hYB : ∀ x, |Y x| ≤ B)
    (a b : ℝ) :
    tiltMean μ H (fun x => |Y x-a|) 1 ≤ tiltMean μ H (fun x => |Y x-b|) 1+|b-a| := by
  have := tilt_law_probability μ hH hA hHA 1
  have hi (c : ℝ) : Integrable (fun x => |Y x-c|) (tiltLaw μ H 1) :=
    Integrable.of_bound (hY.sub_const c).abs.aestronglyMeasurable (B+|c|)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_abs] using (abs_sub (Y x) c).trans (add_le_add (hYB x) le_rfl))
  simp_rw [← tilt_law_integral μ hH hA hHA 1]
  have hc : (∫ _ : S, |b-a| ∂tiltLaw μ H 1) = |b-a| := by simp
  rw [← hc, ← integral_add (hi b) (integrable_const _)]
  apply integral_mono (hi a) ((hi b).add (integrable_const _))
  intro x
  change |Y x-a| ≤ |Y x-b|+|b-a|
  calc
    _ = |(Y x-b)+(b-a)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _

lemma contact_energy_L1_bound {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    {A B : Ω → ℝ} (hA : ∀ ω, 0 ≤ A ω) (hB : ∀ ω, 0 ≤ B ω)
    (hHA : ∀ ω x, |H ω x| ≤ A ω) (hYB : ∀ ω x, |Y ω x| ≤ B ω)
    (hA2 : MemLp A 2 P) (hB2 : MemLp B 2 P) {u a c s V : ℝ} (hs : 0 < s)
    (hmin : IsLocalMin (fun t => c*(t-a)^2-∫ ω, affineLogRoot μ (H ω) (Y ω) t ∂P) u)
    (hp : c*(u-a)^2-(∫ ω, affineLogRoot μ (H ω) (Y ω) u ∂P) ≤
      c*(u+s-a)^2-(∫ ω, affineLogRoot μ (H ω) (Y ω) (u+s) ∂P))
    (hm : c*(u-a)^2-(∫ ω, affineLogRoot μ (H ω) (Y ω) u ∂P) ≤
      c*(u-s-a)^2-(∫ ω, affineLogRoot μ (H ω) (Y ω) (u-s) ∂P))
    (hVp : variance (fun ω => affineLogRoot μ (H ω) (Y ω) (u+s)) P ≤ V)
    (hV0 : variance (fun ω => affineLogRoot μ (H ω) (Y ω) u) P ≤ V)
    (hVm : variance (fun ω => affineLogRoot μ (H ω) (Y ω) (u-s)) P ≤ V) :
    let T := fun ω x => H ω x+u*Y ω x
    let M := fun ω => tiltMean μ (T ω) (Y ω) 1
    (∫ ω, tiltMean μ (T ω) (fun x => |Y ω x-∫ η, M η ∂P|) 1 ∂P) ≤
      Real.sqrt (2*c)+c*s+4*Real.sqrt V/s := by
  dsimp only
  let L := fun t => ∫ ω, affineLogRoot μ (H ω) (Y ω) t ∂P
  let T := fun ω x => H ω x+u*Y ω x
  let M := fun ω => tiltMean μ (T ω) (Y ω) 1
  let U := fun ω => tiltMean μ (T ω) (fun x => |Y ω x-M ω|) 1
  let E := ∫ ω, M ω ∂P
  have hT : Measurable (Function.uncurry T) := hH.add (hY.const_mul u)
  have hM : Measurable M := measurable_tiltMean_param μ hT hY
  have hU : Measurable U := measurable_tiltMean_param μ hT ((hY.sub (hM.comp measurable_fst)).abs)
  have hTm (ω) : Measurable (T ω) := hT.comp (measurable_const.prodMk measurable_id)
  have hHm (ω) : Measurable (H ω) := hH.comp (measurable_const.prodMk measurable_id)
  have hYm (ω) : Measurable (Y ω) := hY.comp (measurable_const.prodMk measurable_id)
  have hTB (ω x) : |T ω x| ≤ A ω+|u| * B ω := affinePotential_bound (hHA ω) (hYB ω) u x
  have hTp (ω) : 0 ≤ A ω+|u| * B ω := add_nonneg (hA ω) (mul_nonneg (abs_nonneg _) (hB ω))
  have hMB (ω) : |M ω| ≤ B ω := tilt_mean_bound μ (hTm ω) (hYm ω) (hTp ω) (hB ω) (hTB ω) (hYB ω) 1
  have hLp (t) := affineLogRoot_memLp μ P hH hY hA hB hHA hYB hA2 hB2 t
  have hBI := hB2.integrable (by norm_num)
  have hd := annealedAffineLogRoot_deriv μ P hH hY hA hB hHA hYB (hA2.integrable (by norm_num)) hBI u
  have hc := quadratic_contact_remainders hd hmin hp hm
  have hAerr (t) (ht : variance (fun ω => affineLogRoot μ (H ω) (Y ω) t) P ≤ V) :
      (∫ ω, |affineLogRoot μ (H ω) (Y ω) t-L t| ∂P) ≤ Real.sqrt V :=
    (integral_centered_abs_le_sqrt_variance P (hLp t)).trans (Real.sqrt_le_sqrt ht)
  have hdis : (∫ ω, |M ω-E| ∂P) ≤ c*s+4*Real.sqrt V/s := by
    exact integral_convex_contact_bound P hs hM.aestronglyMeasurable
      (ae_of_all _ fun ω => ⟨affineLogRoot_convex μ (hHm ω) (hYm ω) (hA ω) (hB ω) (hHA ω) (hYB ω),
        affineLogRoot_deriv μ (hHm ω) (hYm ω) (hA ω) (hB ω) (hHA ω) (hYB ω) u⟩)
      hc.1 hc.2 ((hLp (u+s)).integrable (by norm_num))
      ((hLp u).integrable (by norm_num)) ((hLp (u-s)).integrable (by norm_num))
      (hAerr (u+s) hVp) (hAerr u hV0) (hAerr (u-s) hVm)
  have htherm : (∫ ω, U ω ∂P) ≤ Real.sqrt (2*c) := by
    have hv := contact_thermal_variance_le μ P hH hY hA hB hHA hYB
      (hA2.integrable (by norm_num)) hBI ((memLp_two_iff_integrable_sq hB2.aestronglyMeasurable).mp hB2) hmin
    have hsq := annealed_thermal_abs_sq_le μ P hH hY hA hB hHA hYB hB2 u
    have hsq' : (∫ ω, U ω ∂P)^2 ≤ 2*c := hsq.trans hv
    exact (Real.le_sqrt (integral_nonneg fun ω => tiltMean_nonneg μ (fun _ => abs_nonneg _) 1)
      (le_trans (sq_nonneg _) hsq')).mpr hsq'
  have hUI : Integrable U P := by
    apply (hBI.const_mul 2).mono' hU.aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs] using tilt_mean_bound μ (hTm ω)
        ((hYm ω).sub_const (M ω) |>.abs) (hTp ω) (mul_nonneg (by norm_num) (hB ω)) (hTB ω)
        (fun x => by rw [abs_abs]; exact (abs_sub _ _).trans (by linarith [hYB ω x,hMB ω])) 1
  have hMI : Integrable (fun ω => |M ω-E|) P :=
    ((hBI.mono' hM.aestronglyMeasurable (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hMB ω)).sub (integrable_const E)).abs
  have hQI : Integrable (fun ω => tiltMean μ (T ω) (fun x => |Y ω x-E|) 1) P := by
    apply (hBI.add (integrable_const |E|)).mono'
      (measurable_tiltMean_param μ hT
        (show Measurable (Function.uncurry (fun ω x => |Y ω x-E|)) from
          (hY.sub_const E).abs)).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs,Pi.add_apply] using tilt_mean_bound μ (hTm ω)
        ((hYm ω).sub_const E |>.abs) (hTp ω) (add_nonneg (hB ω) (abs_nonneg E)) (hTB ω)
        (fun x => by rw [abs_abs]; exact (abs_sub _ _).trans (add_le_add (hYB ω x) le_rfl)) 1
  have htri : (∫ ω, tiltMean μ (T ω) (fun x => |Y ω x-E|) 1 ∂P) ≤
      (∫ ω, U ω ∂P)+(∫ ω, |M ω-E| ∂P) := by
    rw [← integral_add hUI hMI]
    exact integral_mono hQI (hUI.add hMI) fun ω => tilt_mean_center_triangle μ (hTm ω) (hYm ω) (hTp ω) (hTB ω) (hYB ω) E (M ω)
  exact htri.trans (by linarith)

end ContactL1Complete
end SphericalPerceptron

end
end
end

end OAI
