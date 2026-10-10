import Mathlib
import OAI.Analysis.AffineBernstein.CapPerturbation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

lemma integrableOn_affineArea_sublevel {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u v : Space n → ℝ} (hv : ContDiffOn ℝ ∞ v Ω)
    (hp : ∀ x ∈ Ω, (hessian v x).PosDef) {b : ℝ}
    (hK : IsCompact {x | x ∈ Ω ∧ u x ≤ b}) :
    IntegrableOn (affineAreaDensity v) {x | x ∈ Ω ∧ u x < b} := by
  have hc : ContinuousOn (affineAreaDensity v) {x | x ∈ Ω ∧ u x ≤ b} := by
    intro x hx
    exact (contDiffAt_affineAreaDensity (hv.contDiffAt (hΩ.mem_nhds hx.1))
      (hp x hx.1)).continuousAt.continuousWithinAt
  exact (hc.integrableOn_compact hK).mono_set (fun _ hx => ⟨hx.1,hx.2.le⟩)

/-- Local weak maximization and a smooth convex replacement give the cap
comparison on its actual open base. -/
theorem affineMaximal_cap_area_comparison {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u q : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmax : AffineMaximalOn Ω u)
    {b ε : ℝ} (hε : 0 < ε) (hK : IsCompact {x | x ∈ Ω ∧ u x ≤ b})
    (hqtop : ∀ x, x ∈ Ω → u x < b → q x ≤ b-2*ε)
    (hqp : ∀ x, x ∈ Ω → u x < b → (hessian q x).PosDef)
    {B : Set (Space n)} (hB : IsOpen B)
    (hBE : ∀ x ∈ B, x ∈ Ω ∧ u x < b ∧ ε ≤ q x-u x) :
    (∫ x in B, affineAreaDensity q x) ≤
      ∫ x in {x | x ∈ Ω ∧ u x < b}, affineAreaDensity u x := by
  let E : Set (Space n) := {x | x ∈ Ω ∧ u x < b}
  have hE : IsOpen E := isOpen_graphSublevel hΩ hu.continuousOn b
  have hEΩ : E ⊆ Ω := fun _ hx => hx.1
  obtain ⟨η,hη,hηc,hηE,hpert,heq⟩ := exists_cap_perturbation hΩ hu hq hp hε hK hqtop hqp
  let v : Space n → ℝ := fun x => u x+η x
  have hv : ContDiffOn ℝ ∞ v Ω := hu.add hη.contDiffOn
  have hiu := integrableOn_affineArea_sublevel hΩ hu hp hK
  have hiv := integrableOn_affineArea_sublevel hΩ hv hpert hK
  have hmaxi := affineMaximal_local_area_maximization hΩ hu hp hmax η hη hηc
    (hηE.trans hEΩ) hpert
  have hrestrict : (∫ x in Ω, affineAreaDensity v x-affineAreaDensity u x) =
      ∫ x in E, affineAreaDensity v x-affineAreaDensity u x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hEΩ
    intro x hx
    have hn : x ∉ tsupport η := fun hh => hx.2 (hηE hh)
    have he : v =ᶠ[𝓝 x] u := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [v,hy,add_zero]
    unfold affineAreaDensity
    rw [hessian_eq_of_eventuallyEq he,sub_self]
  change (∫ x in Ω, affineAreaDensity v x-affineAreaDensity u x) ≤ 0 at hmaxi
  rw [hrestrict,integral_sub hiv hiu] at hmaxi
  have hev : (∫ x in B, affineAreaDensity q x) = ∫ x in B, affineAreaDensity v x := by
    apply setIntegral_congr_fun hB.measurableSet
    intro x hx
    have he : v =ᶠ[𝓝 x] q := by
      filter_upwards [hB.mem_nhds hx] with y hy
      exact heq y (hBE y hy).1 (hBE y hy).2.1 (hBE y hy).2.2
    unfold affineAreaDensity
    rw [hessian_eq_of_eventuallyEq he]
  rw [hev]
  refine le_trans (setIntegral_mono_set hiv ?_ ?_) (sub_nonpos.mp hmaxi)
  · filter_upwards [ae_restrict_mem hE.measurableSet] with x hx
    exact Real.rpow_nonneg (hpert x hx.1).det_pos.le _
  · exact Filter.Eventually.of_forall fun x hx => ⟨(hBE x hx).1,(hBE x hx).2.1⟩

/-- The graph-coordinate positive cap estimate, with a quantitative uniform
constant. The original PDE, not an area lower bound, is the hypothesis. -/
theorem affineMaximal_positive_cap_area {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmax : AffineMaximalOn Ω u)
    {b ε α r : ℝ} (hε : 0 < ε) (hα : 0 < α) (_hr : 0 < r)
    (c : Space n) (hK : IsCompact {x | x ∈ Ω ∧ u x ≤ b})
    (hball : ∀ x ∈ Metric.ball c r, x ∈ Ω ∧ u x ≤ b-6*ε)
    (hradius : ∀ x, x ∈ Ω → u x < b → α*‖x-c‖^2 ≤ 2*ε) :
    volume.real (Metric.ball (0 : Space n) r) * Real.rpow (2*α) ((n : ℝ)/((n : ℝ)+2)) ≤
      ∫ x in {x | x ∈ Ω ∧ u x < b}, affineAreaDensity u x := by
  have hcomp := affineMaximal_cap_area_comparison hΩ hu
    (capQuadratic_smooth c (b-4*ε) α).contDiffOn hp hmax hε hK
    (q := capQuadratic c (b-4*ε) α) (B := Metric.ball c r) ?_ ?_ Metric.isOpen_ball ?_
  · simpa only [affineAreaDensity_capQuadratic _ _ hα, integral_const,
      measureReal_restrict_apply_univ, smul_eq_mul, Measure.addHaar_real_ball_center] using hcomp
  · intro x hx hxb
    unfold capQuadratic
    linarith [hradius x hx hxb]
  · intro x hx hxb
    exact hessian_capQuadratic_posDef c (b-4*ε) hα x
  · intro x hx
    obtain ⟨hxΩ,hxu⟩ := hball x hx
    refine ⟨hxΩ,by linarith,?_⟩
    unfold capQuadratic
    nlinarith [sq_nonneg ‖x-c‖]

lemma cap_area_constant_pos (n : ℕ) {r α : ℝ} (hr : 0 < r) (hα : 0 < α) :
    0 < volume.real (Metric.ball (0 : Space n) r) *
      Real.rpow (2*α) ((n : ℝ)/((n : ℝ)+2)) := by
  apply mul_pos
  · exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume _ hr))
      (ne_of_lt (measure_ball_lt_top))
  · exact Real.rpow_pos_of_pos (by positivity) _

/-- Uniform nonvanishing in uniformly bounded graph caps, without assumptions
on boundary regularity or uniform Hessian bounds. -/
theorem exists_uniform_positive_graph_cap_area (n : ℕ) {ε r R : ℝ}
    (hε : 0 < ε) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Set (Space n)) (u : Space n → ℝ)
      (b : ℝ) (c : Space n), IsOpen Ω → ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
      IsCompact {x | x ∈ Ω ∧ u x ≤ b} →
      (∀ x ∈ Metric.ball c r, x ∈ Ω ∧ u x ≤ b-6*ε) →
      (∀ x, x ∈ Ω → u x < b → ‖x-c‖ ≤ R) →
      C ≤ ∫ x in {x | x ∈ Ω ∧ u x < b}, affineAreaDensity u x := by
  let α : ℝ := ε/(R^2+1)
  have hd : 0 < R^2+1 := by positivity
  have ha : 0 < α := div_pos hε hd
  refine ⟨_,cap_area_constant_pos n hr ha,?_⟩
  intro Ω u b c hΩ hu hp hmax hK hball hbound
  apply affineMaximal_positive_cap_area hΩ hu hp hmax hε ha hr c hK hball
  intro x hx hxb
  have hb := hbound x hx hxb
  have hsq : ‖x-c‖^2 ≤ R^2 := by nlinarith [norm_nonneg (x-c)]
  have he : α*(R^2+1) = ε := div_mul_cancel₀ ε (ne_of_gt hd)
  have hh := mul_le_mul_of_nonneg_left hsq ha.le
  nlinarith

end AffineBernstein
end

end OAI
