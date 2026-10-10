import OAI.NumberTheory.DukePrimeDegree.Dynamics.UnitFlowSmoothing
import OAI.NumberTheory.DukePrimeDegree.Dynamics.InvariantMeanGenericSet
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-!
# Comparing the nonconstant means of nearby generic points

A single finite continuous average approximates the invariant mean on
the entire good set.  Nearby good points therefore have nearby means.
This supplies exactly the continuity comparison needed after bounded
simultaneous corrections; no continuity of the invariant mean is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace DukePrimeDegree

lemma continuous_fixed_flow_average
    {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    (f : Y →ᵇ ℝ) (T : ℝ) :
    Continuous (fun x => T⁻¹ * ∫ t in (0 : ℝ)..T, f (realActionTime t x)) := by
  apply Continuous.const_mul
  apply intervalIntegral.continuous_of_dominated_interval (bound := fun _ => ‖f‖)
  · intro x
    exact ((continuous_flow_observable f).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · intro x
    exact ae_of_all _ (fun t _ => f.norm_coe_le_norm (realActionTime t x))
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun t _ => (continuous_flow_observable f).comp
      (continuous_const.prodMk continuous_id))

lemma invariant_mean_pair_bound
    {Y : Type*} (q F : Y → ℝ) (G : Set Y) (ε η : ℝ)
    (happrox : ∀ x ∈ G, |q x - F x| ≤ ε)
    (x y : Y) (hx : x ∈ G) (hy : y ∈ G)
    (hclose : |F x - F y| ≤ η) :
    |q x - q y| ≤ 2 * ε + η := by
  have hdecomp : q x - q y = (q x - F x) + (F x - F y) + (F y - q y) := by ring
  rw [hdecomp]
  calc
    _ ≤ |q x - F x| + |F x - F y| + |F y - q y| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ε + η + ε := by
      exact add_le_add (add_le_add (happrox x hx) hclose)
        (by simpa only [abs_sub_comm] using happrox y hy)
    _ = _ := by ring

/-- Close pairs may vary inside one common generic set. A fixed
continuous finite approximation suffices to compare their invariant
means, even when those means are not constant. -/
theorem eventually_invariant_means_close
    {Y I : Type*} [TopologicalSpace Y] {l : Filter I}
    (q F : Y → ℝ) (G : Set Y) (ε η : ℝ) (hη : 0 < η)
    (happrox : ∀ x ∈ G, |q x - F x| ≤ ε)
    (a b : I → Y) (x : Y) (hF : ContinuousAt F x)
    (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 x))
    (hG : ∀ᶠ i in l, a i ∈ G ∧ b i ∈ G) :
    ∀ᶠ i in l, |q (a i) - q (b i)| ≤ 2 * ε + η := by
  have hlim : Tendsto (fun i => |F (a i) - F (b i)|) l (𝓝 0) := by
    simpa only [sub_self, abs_zero, Function.comp_def] using
      ((hF.tendsto.comp ha).sub (hF.tendsto.comp hb)).abs
  filter_upwards [hG, hlim.eventually (gt_mem_nhds hη)] with i hi hclose
  exact invariant_mean_pair_bound q F G ε η happrox (a i) (b i) hi.1 hi.2 hclose.le

/-- A common integer averaging time supplies the finite continuous
approximation used above for genuine flow windows. -/
theorem eventually_flow_invariant_means_close
    {Y I : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    {l : Filter I} (f : Y →ᵇ ℝ) (q : Y → ℝ) (G : Set Y)
    (ε η : ℝ) (hη : 0 < η) (N₀ : ℕ)
    (hgood : ∀ x ∈ G, ∀ N ≥ N₀,
      |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ), f (realActionTime t x)) - q x| ≤ ε)
    (a b : I → Y) (x : Y) (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 x))
    (hG : ∀ᶠ i in l, a i ∈ G ∧ b i ∈ G) :
    ∀ᶠ i in l, |q (a i) - q (b i)| ≤ 2 * ε + η := by
  let F := fun y => (N₀ : ℝ)⁻¹ * ∫ t in (0 : ℝ)..(N₀ : ℝ), f (realActionTime t y)
  exact eventually_invariant_means_close q F G ε η hη
    (fun y hy => by simpa only [abs_sub_comm] using hgood y hy N₀ le_rfl)
    a b x (continuous_fixed_flow_average f N₀).continuousAt ha hb hG

end DukePrimeDegree

end

end OAI
