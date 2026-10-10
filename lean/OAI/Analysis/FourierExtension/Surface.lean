import Mathlib

namespace OAI

/-! Positively curved surfaces and their extension operators. -/



open MeasureTheory
open scoped NNReal ENNReal ContDiff

noncomputable section

namespace DiagonalExtension

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def IsSurface (S : Set E3) : Prop :=
  IsCompact S ∧ ∀ ξ ∈ S, ∃ (U : Set E3) (F G : E3 → ℝ),
    IsOpen U ∧ ξ ∈ U ∧
    ContDiffOn ℝ ∞ F U ∧ ContDiffOn ℝ ∞ G U ∧
    S ∩ U = {y ∈ U | F y = 0 ∧ 0 ≤ G y} ∧
    fderiv ℝ F ξ ≠ 0 ∧
    (G ξ = 0 → ∃ v : E3, fderiv ℝ F ξ v = 0 ∧ fderiv ℝ G ξ v ≠ 0) ∧
    (∀ v : E3, v ≠ 0 → fderiv ℝ F ξ v = 0 →
      0 < (fderiv ℝ (fderiv ℝ F) ξ v) v)

def surfaceMeasure (S : Set E3) : Measure E3 :=
  (ENNReal.ofReal (Real.pi / 4) • (Measure.hausdorffMeasure 2 : Measure E3)).restrict S

def fourierCharacter (t : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

def extension (S : Set E3) (f : E3 → ℂ) (x : E3) : ℂ :=
  ∫ ξ, f ξ * fourierCharacter (inner ℝ x ξ) ∂surfaceMeasure S

def MainStatement : Prop :=
  ∀ (S : Set E3), IsSurface S → ∀ p : ℝ, 3 < p →
    ∃ C : ℝ≥0, ∀ f : E3 → ℂ,
      MemLp f (ENNReal.ofReal p) (surfaceMeasure S) →
      MemLp (extension S f) (ENNReal.ofReal p) volume ∧
      eLpNorm (extension S f) (ENNReal.ofReal p) volume ≤
        (C : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) (surfaceMeasure S)

open Set Filter
open scoped Topology

theorem regular_level_finiteAt {F : E3 → ℝ} {F' : E3 →L[ℝ] ℝ}
    {a : E3} {s : Set E3} (hF : HasStrictFDerivAt F F' a) (hF' : F' ≠ 0)
    (hs : ∀ᶠ x in 𝓝[s] a, F x = F a) :
    (Measure.hausdorffMeasure 2 : Measure E3).FiniteAtFilter (𝓝[s] a) := by
  have hn : (F' : E3 →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    exact hF' (ContinuousLinearMap.coe_injective h)
  have hr : (F' : E3 →ₗ[ℝ] ℝ).range = ⊤ :=
    Module.Dual.range_eq_top_of_ne_zero hn
  have hd : Module.finrank ℝ F'.ker = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hn
    simp only [finrank_euclideanSpace_fin] at h
    omega
  let e := hF.implicitToOpenPartialHomeomorph F F' hr
  let g : F'.ker → E3 := hF.implicitFunction F F' hr (F a)
  obtain ⟨K, V, hV, hLip⟩ := (hF.to_implicitFunction hr).exists_lipschitzOnWith
  obtain ⟨r, hr0, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hV
  have harea : (Measure.hausdorffMeasure 2 : Measure F'.ker)
      (Metric.closedBall 0 r) < ⊤ := by
    have hd' : (2 : ℝ) = (Module.finrank ℝ F'.ker : ℝ) := by rw [hd]; norm_num
    rw [hd']
    exact (isCompact_closedBall (0 : F'.ker) r).measure_lt_top
  have himage : (Measure.hausdorffMeasure 2 : Measure E3)
      (g '' Metric.closedBall 0 r) < ⊤ := by
    refine ((hLip.mono hrV).hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 2)).trans_lt ?_
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.coe_ne_top) harea
  refine ⟨g '' Metric.closedBall 0 r, ?_, himage⟩
  have he : ContinuousAt (fun x => (e x).2) a :=
    (e.continuousAt (hF.mem_implicitToOpenPartialHomeomorph_source hr)).snd
  have hea : (e a).2 = 0 := by simp [e]
  have heevent : ∀ᶠ x in 𝓝 a, (e x).2 ∈ Metric.closedBall 0 r := by
    change ((fun x => (e x).2) ⁻¹' Metric.closedBall 0 r) ∈ 𝓝 a
    have hh := he (Metric.closedBall_mem_nhds ((e a).2) hr0)
    simpa only [hea, Filter.mem_map] using hh
  filter_upwards [heevent.filter_mono nhdsWithin_le_nhds,
    (hF.eq_implicitFunction hr).filter_mono nhdsWithin_le_nhds, hs] with x hx hx' hFx
  refine ⟨(e x).2, hx, ?_⟩
  simpa only [g, e, hFx] using hx'

theorem IsSurface.hausdorffMeasure_lt_top {S : Set E3} (hS : IsSurface S) :
    (Measure.hausdorffMeasure 2 : Measure E3) S < ⊤ := by
  apply hS.1.measure_lt_top_of_nhdsWithin
  intro a ha
  obtain ⟨U, F, G, hU, haU, hF, _, hEq, hFn, _, _⟩ := hS.2 a ha
  have hFa : F a = 0 := by
    have : a ∈ {y ∈ U | F y = 0 ∧ 0 ≤ G y} := hEq ▸ ⟨ha, haU⟩
    exact this.2.1
  apply regular_level_finiteAt
    ((hF.contDiffAt (hU.mem_nhds haU)).hasStrictFDerivAt (by norm_num)) hFn
  have hUnear : ∀ᶠ x in 𝓝 a, x ∈ U := hU.mem_nhds haU
  filter_upwards [hUnear.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hxU hxS
  have hx : x ∈ {y ∈ U | F y = 0 ∧ 0 ≤ G y} := hEq ▸ ⟨hxS, hxU⟩
  exact hx.2.1.trans hFa.symm

theorem IsSurface.isFiniteMeasure {S : Set E3} (hS : IsSurface S) :
    IsFiniteMeasure (surfaceMeasure S) := by
  apply (isFiniteMeasure_iff _).2
  rw [surfaceMeasure, Measure.restrict_apply_univ, Measure.smul_apply]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS.hausdorffMeasure_lt_top

theorem IsSurface.integrable_of_memLp {S : Set E3} (hS : IsSurface S)
    {p : ℝ} (hp : 3 < p) {f : E3 → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) (surfaceMeasure S)) :
    Integrable f (surfaceMeasure S) := by
  let := hS.isFiniteMeasure
  apply hf.integrable
  exact_mod_cast ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)

@[simp]
theorem norm_fourierCharacter (t : ℝ) : ‖fourierCharacter t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem continuous_fourierCharacter : Continuous fourierCharacter := by
  unfold fourierCharacter
  fun_prop

theorem extension_integrand_integrable {S : Set E3} {f : E3 → ℂ}
    (hf : Integrable f (surfaceMeasure S)) (x : E3) :
    Integrable (fun ξ => f ξ * fourierCharacter (inner ℝ x ξ)) (surfaceMeasure S) := by
  apply hf.mul_bdd
    ((continuous_fourierCharacter.comp (continuous_const.inner continuous_id)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun ξ => le_of_eq (norm_fourierCharacter _))

theorem norm_extension_le {S : Set E3} {f : E3 → ℂ}
    (hf : Integrable f (surfaceMeasure S)) (x : E3) :
    ‖extension S f x‖ ≤ ∫ ξ, ‖f ξ‖ ∂surfaceMeasure S := by
  apply norm_integral_le_of_norm_le hf.norm
  exact Filter.Eventually.of_forall (fun ξ => by simp)

theorem continuous_extension {S : Set E3} {f : E3 → ℂ}
    (hf : Integrable f (surfaceMeasure S)) : Continuous (extension S f) := by
  apply continuous_of_dominated
    (fun x => (extension_integrand_integrable hf x).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall (fun ξ => by simp)) hf.norm
  exact Filter.Eventually.of_forall (fun ξ => continuous_const.mul
    (continuous_fourierCharacter.comp (continuous_id.inner continuous_const)))

end DiagonalExtension

end

end OAI
