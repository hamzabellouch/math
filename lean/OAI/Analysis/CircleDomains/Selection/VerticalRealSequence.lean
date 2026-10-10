import OAI.Analysis.CircleDomains.Modulus.RealSequencePayment
import OAI.Analysis.CircleDomains.Modulus.VerticalLimitPayment

namespace OAI

/-! Vertical payment along cofinal subsequences of actual real models. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer
namespace RealModelExhaustion


variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem limiting_vertical_line_payment
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hε : Tendsto ε atTop (𝓝 0)) (r : ℕ → ℕ) (hr : Tendsto r atTop atTop) (l : ℕ)
    {L : ℝ} (hL : 3 * M.radius ≤ L)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (verticalLine y s : Sphere) ∈ (M.stages (r n)).domain ∧
      (verticalLine y t : Sphere) ∈ (M.stages (r n)).domain ∧
      verticalLine y s ∈ closedBall 0 L ∧
      verticalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))
        ((M.stages (r n)).inverse (verticalLine y s)) = 0 ∧
      sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))
        ((M.stages (r n)).inverse (verticalLine y t)) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
        (∫ x in realChartDomain G,
          gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * L * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  classical
  let _ : ∀ n, Fintype (M.stages (r n)).indices := fun n => (M.stages (r n)).finite_indices.fintype
  let T (n : ℕ) := (M.stages (r n)).terminals.H
  let f (n : ℕ) := (M.stages (r n)).forward
  let fi (n : ℕ) := (M.stages (r n)).inverse
  let V (n : ℕ) := (M.stages (r n)).domain
  let w (n : ℕ) := (M.stages (r n)).functions (prefixIndex l (r n))
  let E := ∫ x in realChartDomain G,
    gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x
  have hE : 0 ≤ E := integral_nonneg (fun x => by
    rw [gradientEnergy_spherical]
    positivity)
  have hbound (n : ℕ) : (V n)ᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall 0 L := by
    have h := (normalized_model_uniform_bound harea (M.stages (r n)).equivalence
      (M.stages (r n)).circle_domain.1 M.radius_pos
      ((M.exterior_core (r n)).trans (M.core_model (r n)))
      ((M.core_conformal (r n)).mono
        ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans (M.exterior_core (r n))))
      (M.stages (r n)).principal).1
    exact fun p hp => image_mono (closedBall_subset_closedBall hL) (h p hp)
  have ha (n : ℕ) : Nonempty (TerminalComponentAssignment (T n) (f n) (V n)) :=
    exists_terminal_component_assignment hsard hsch (T n)
      (M.stages (r n)).terminals.disjoint_closures (M.stages (r n)).equivalence
      (M.stages (r n)).circle_domain.1 (M.stages (r n)).principal.1
  let a (n : ℕ) := Classical.choice (ha n)
  apply limiting_vertical_terminal_line_payment T f fi V a
    (fun n => (M.stages (r n)).equivalence) (fun n => (M.stages (r n)).circle_domain)
    (fun n => (M.stages (r n)).source_infty) (fun n => (M.stages (r n)).principal.1)
    ((mul_nonneg (by norm_num) M.radius_pos.le).trans hL) hbound w
    (fun n => (M.stages (r n)).functions_smooth_source (prefixIndex l (r n)))
    (fun n => (M.stages (r n)).extension) (fun n => (M.stages (r n)).extension_open)
    (fun n => (M.stages (r n)).terminal_frontier_extension)
    (fun n => ((M.stages (r n)).functions_smooth (prefixIndex l (r n))).continuousOn)
    (fun n => (M.stages (r n)).metric) (fun n => (M.stages (r n)).metric_conformal)
    (fun n x _ => (M.stages (r n)).metric_pos x)
    (fun n => (M.stages (r n)).functions_integrable_source (prefixIndex l (r n)))
    (fun n s => d.upper l s - d.lower l s) (fun _ s => d.width_nonneg l s)
    (Real.sqrt_nonneg E) (fun n =>
      finite_label_band_norm_le (fun s : (M.stages (r n)).indices => (s : S))
        Subtype.val_injective (fun s => d.upper l s - d.lower l s) (d.width_summable l))
    (fun n => E + ε (r n)) (fun n => ε (r n)) ?_ (hε.comp hr) ?_ ?_ hJ hcross
  · simpa only [Real.sq_sqrt hE, add_zero, Function.comp_def] using
      tendsto_const_nhds.add (hε.comp hr)
  · filter_upwards [hr (prefixIndex_eq l)] with n hn
    change (prefixIndex l (r n)).val = l at hn
    have h := (M.stages (r n)).source_energy_lt (prefixIndex l (r n))
    simpa only [CountableRealCoordinates.Stage, hn] using h.le
  · filter_upwards [hr (prefixIndex_eq l)] with n hn
    change (prefixIndex l (r n)).val = l at hn
    have h := (M.stages (r n)).excess (prefixIndex l (r n))
    simpa only [terminalOscillation, hn, tsum_fintype] using h.le

end RealModelExhaustion

end CircleDomainRigidity.FiniteTransfer

end

end OAI
