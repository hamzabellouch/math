import OAI.Probability.SLE.LoewnerCharts
import Mathlib.Topology.ExtendFrom

namespace OAI

/-! Once finite limits at the real boundary are proved, the continuous
closed-half-plane extension and the prescribed Loewner tip follow. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology NNReal

namespace SLEExactGauge

lemma closedHalfPlane_subset_closure_upperHalfPlane :
    {z : ℂ | 0≤z.im} ⊆ closure upperHalfPlane := by
  intro z hz
  change 0≤z.im at hz
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  refine ⟨z+((ε/2:ℝ):ℂ)*Complex.I,?_,?_⟩
  · change 0<(z+((ε/2:ℝ):ℂ)*Complex.I).im
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero]
    linarith
  · rw [dist_eq_norm,norm_sub_rev]
    simp only [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,
      mul_one,abs_of_pos (half_pos hε)]
    linarith

lemma exists_halfPlane_boundary_extension {f : ℂ → ℂ}
    (hf : ContinuousOn f upperHalfPlane)
    (hreal : ∀ x : ℝ, ∃ z : ℂ, Tendsto f (𝓝[upperHalfPlane] (x:ℂ)) (𝓝 z)) :
    ∃ F : ℂ → ℂ, ContinuousOn F {z : ℂ | 0≤z.im} ∧
      ∀ z∈upperHalfPlane, F z=f z := by
  refine ⟨extendFrom upperHalfPlane f,?_,extendFrom_extends hf⟩
  apply continuousOn_extendFrom closedHalfPlane_subset_closure_upperHalfPlane
  intro z hz
  by_cases hp : 0<z.im
  · exact ⟨f z,hf z hp⟩
  · have him : z.im=0 := le_antisymm (le_of_not_gt hp) hz
    have he : z=(z.re:ℂ) := by apply Complex.ext <;> simp [him]
    rw [he]
    exact hreal z.re

lemma IsCapacityTwoWitness.boundary_extension_of_real_limits
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0)
    (hreal : ∀ x : ℝ, ∃ z : ℂ, Tendsto (F t) (𝓝[upperHalfPlane] (x:ℂ)) (𝓝 z)) :
    ∃ Fbar : ℂ → ℂ, ContinuousOn Fbar {z : ℂ | 0≤z.im} ∧
      (∀ z∈upperHalfPlane, Fbar z=F t z) ∧ Fbar (U t:ℂ)=γ t := by
  let Fbar := extendFrom upperHalfPlane (F t)
  have hFc := (hw.2.2.2.2.1 t).continuousOn
  have hext : ∀ z∈upperHalfPlane, Fbar z=F t z := extendFrom_extends hFc
  have hcont : ContinuousOn Fbar {z : ℂ | 0≤z.im} := by
    apply continuousOn_extendFrom closedHalfPlane_subset_closure_upperHalfPlane
    intro z hz
    by_cases hp : 0<z.im
    · exact ⟨F t z,hFc z hp⟩
    · have him : z.im=0 := le_antisymm (le_of_not_gt hp) hz
      have he : z=(z.re:ℂ) := by apply Complex.ext <;> simp [him]
      rw [he]
      exact hreal z.re
  obtain ⟨p,hp⟩ := hreal (U t)
  have hv : Tendsto (fun y : ℝ => (U t:ℂ)+(y:ℂ)*Complex.I)
      (𝓝[>] 0) (𝓝[upperHalfPlane] (U t:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun y : ℝ => (U t:ℂ)+(y:ℂ)*Complex.I) := by fun_prop
      simpa only [Complex.ofReal_zero,zero_mul,add_zero] using
        (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      change 0<((U t:ℂ)+(y:ℂ)*Complex.I).im
      simpa using hy
  have hpγ : p=γ t := tendsto_nhds_unique (hp.comp hv) (hw.2.2.2.2.2.2.2.2.2.2.2.2 t)
  refine ⟨Fbar,hcont,hext,?_⟩
  exact (extendFrom_eq (closedHalfPlane_subset_closure_upperHalfPlane (by simp)) hp).trans hpγ

end SLEExactGauge

end

end OAI
