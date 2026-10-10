import Mathlib
import OAI.Geometry.PrescribedRicci.GlobalKahlerIntegral
import OAI.Geometry.PrescribedRicci.KahlerLocalL2Comparison
import OAI.Geometry.PrescribedRicci.KahlerVolumeMeasure

namespace OAI

/-! Kahler Chart Lp. -/

section

 
noncomputable section
open Matrix Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff Classical NNReal ENNReal
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}

lemma chart_integral_upper (g : KaehlerMetric A) (i : Fin A.count)
    {K : Set X} (hK : IsCompact K) (hs : K ⊆ (A.chart i).source) :
    ∃ b : ℝ, 0 < b ∧ ∀ f : X → ℝ, Continuous f → (∀ x, 0 ≤ f x) →
      tsupport f ⊆ K → g.integral f ≤ b * ∫ z : Coordinates d, localizeFunction i f z := by
  let K' := (A.chart i) '' K
  have hK' : IsCompact K' := hK.image_of_continuousOn ((A.chart i).continuousOn.mono hs)
  have ht : K' ⊆ (A.chart i).target := by rintro z ⟨x,hx,rfl⟩; exact (A.chart i).mapsTo (hs hx)
  obtain ⟨a,b,ha,hb,hab⟩ := g.compact_volume_bounds i hK' ht
  refine ⟨b,hb,fun f hf hn hfs => ?_⟩
  have hss := hfs.trans hs
  obtain ⟨hl,hc,hlt⟩ := localizeFunction_continuous_compact i hf hss
  have hi : Integrable (localizeFunction i f) volume := hl.integrable_of_hasCompactSupport hc
  have hwi := g.chart_weighted_integrable i hf hss
  have hsup : Function.support (localizeFunction i f) ⊆ K' :=
    (localizeFunction_support i f).trans (image_mono hfs)
  rw [g.integral_chart i hf hss, g.chartIntegral_eq_localize, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_mono hwi (hi.const_mul b)
  intro z
  by_cases hz : z ∈ Function.support (localizeFunction i f)
  · have hp : 0 ≤ localizeFunction i f z := by
      unfold localizeFunction
      split_ifs <;> simp_all only [le_refl]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hab z (hsup hz)).2 hp
  · simp only [Function.notMem_support.mp hz, zero_mul, mul_zero, le_refl]

omit [T2Space X] [CompactSpace X] in
lemma tsupport_norm_rpow {f : X → ℝ} {q : ℝ} (hq : 0 < q) :
    tsupport (fun x => ‖f x‖ ^ q) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  apply subset_tsupport
  intro hz
  exact hx (by simp [hz, Real.zero_rpow hq.ne'])

omit [T2Space X] [CompactSpace X] in
lemma localize_norm_rpow (i : Fin A.count) (f : X → ℝ) {q : ℝ} (hq : 0 < q) :
    localizeFunction i (fun x => ‖f x‖ ^ q) = fun z => ‖localizeFunction i f z‖ ^ q := by
  funext z
  unfold localizeFunction
  split_ifs <;> simp [Real.zero_rpow hq.ne']

variable [MeasurableSpace X] [BorelSpace X]
lemma chart_lpNorm_bound (g : KaehlerMetric A) (i : Fin A.count)
    {K : Set X} (hK : IsCompact K) (hs : K ⊆ (A.chart i).source) :
    ∃ b : ℝ, 0 < b ∧ ∀ (ψ : SmoothRealFunction A), tsupport ψ.value ⊆ K →
      ∀ q : ℝ≥0, 0 < q → lpNorm ψ.value q g.volumeMeasure ≤
        b ^ (q : ℝ)⁻¹ * lpNorm (ψ.localized i) q volume := by
  obtain ⟨b,hb,hbnd⟩ := g.chart_integral_upper i hK hs
  refine ⟨b,hb,fun ψ hψ q hq => ?_⟩
  have hqR : (0:ℝ) < q := hq
  have hc : Continuous (fun x => ‖ψ.value x‖ ^ (q:ℝ)) :=
    ψ.continuous.norm.rpow_const (fun _ => Or.inr hqR.le)
  have hpow := hbnd (fun x => ‖ψ.value x‖ ^ (q:ℝ)) hc
    (fun x => Real.rpow_nonneg (norm_nonneg _) _) ((tsupport_norm_rpow hqR).trans hψ)
  rw [g.integral_volumeMeasure hc |>.symm, localize_norm_rpow i ψ.value hqR] at hpow
  have hloc : localizeFunction i ψ.value = ψ.localized i := rfl
  rw [hloc] at hpow
  obtain ⟨hl,hcl,_⟩ := ψ.localized_smooth_compact i (hψ.trans hs)
  rw [lpNorm_nnreal_eq_integral_norm_rpow hq.ne' ψ.continuous.aestronglyMeasurable,
    lpNorm_nnreal_eq_integral_norm_rpow hq.ne' hl.continuous.aestronglyMeasurable]
  calc
    _ ≤ (b * ∫ z, ‖ψ.localized i z‖ ^ (q:ℝ)) ^ (q:ℝ)⁻¹ :=
      Real.rpow_le_rpow (MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) hpow
        (inv_nonneg.mpr hqR.le)
    _ = _ := Real.mul_rpow hb.le (MeasureTheory.integral_nonneg (fun z => Real.rpow_nonneg (norm_nonneg _) _))

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
