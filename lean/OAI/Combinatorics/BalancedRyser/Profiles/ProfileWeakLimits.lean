import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Bounded.Normed

namespace OAI

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Balanced
open scoped _root_.Balanced

def bounded_profile_coordinate {ι : Type*} (S : Set (ι → ℝ))
    (hbound : ∀ x ∈ S, ∀ i, |x i| ≤ 1) (i : ι) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => x.1 i)
    ((continuous_apply i).comp continuous_subtype_val) 1
    (fun x => by simpa only [Real.norm_eq_abs] using hbound x.1 x.2 i)

theorem profile_incidence_weak_limit {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {νn : ℕ → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hν : Tendsto νn atTop (𝓝 ν)) (f : Ω →ᵇ ℝ)
    {pn : ℕ → ℝ} {p w : ℝ} (hp : Tendsto pn atTop (𝓝 p))
    (hinc : ∀ n, (∫ ω, f ω ∂(νn n : Measure Ω)) = w * pn n) :
    (∫ ω, f ω ∂(ν : Measure Ω)) = w * p := by
  have hleft := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν) f
  have hright : Tendsto (fun n => ∫ ω, f ω ∂(νn n : Measure Ω)) atTop
      (𝓝 (w * p)) := by
    simpa only [hinc] using (tendsto_const_nhds.mul hp :
      Tendsto (fun n => w * pn n) atTop (𝓝 (w * p)))
  exact tendsto_nhds_unique hleft hright

theorem profile_zero_integral_weak_limit {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {νn : ℕ → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hν : Tendsto νn atTop (𝓝 ν)) (f : Ω →ᵇ ℝ)
    (hzero : ∀ n, (∫ ω, f ω ∂(νn n : Measure Ω)) = 0) :
    (∫ ω, f ω ∂(ν : Measure Ω)) = 0 := by
  have h := profile_incidence_weak_limit hν f
    (pn := fun _ => 0) (p := 0) (w := 1) tendsto_const_nhds
    (fun n => by simpa using hzero n)
  simpa using h

theorem profile_zero_coordinate_weak_limit {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {νn : ℕ → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hν : Tendsto νn atTop (𝓝 ν)) (f : Ω →ᵇ ℝ)
    (hnonneg : ∀ ω, 0 ≤ f ω)
    (hzero : ∀ n, ∀ᵐ ω ∂(νn n : Measure Ω), f ω = 0) :
    ∀ᵐ ω ∂(ν : Measure Ω), f ω = 0 := by
  apply (integral_eq_zero_iff_of_nonneg hnonneg (f.integrable (ν : Measure Ω))).mp
  apply profile_zero_integral_weak_limit hν f
  intro n
  rw [integral_congr_ae (hzero n)]
  simp

theorem profile_zero_coordinates_weak_limit {ι Ω : Type*} [Countable ι]
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {νn : ℕ → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hν : Tendsto νn atTop (𝓝 ν)) (f : ι → Ω →ᵇ ℝ)
    (hnonneg : ∀ i ω, 0 ≤ f i ω)
    (hzero : ∀ n, ∀ᵐ ω ∂(νn n : Measure Ω), ∀ i, f i ω = 0) :
    ∀ᵐ ω ∂(ν : Measure Ω), ∀ i, f i ω = 0 := by
  rw [ae_all_iff]
  intro i
  apply profile_zero_coordinate_weak_limit hν (f i) (hnonneg i)
  intro n
  filter_upwards [hzero n] with ω hω
  exact hω i

theorem profile_mass_weak_limit {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {νn : ℕ → FiniteMeasure Ω} {ν : FiniteMeasure Ω} {m : ℝ}
    (hν : Tendsto νn atTop (𝓝 ν))
    (hm : Tendsto (fun n => (νn n : Measure Ω).real Set.univ) atTop (𝓝 m)) :
    (ν : Measure Ω).real Set.univ = m := by
  have h := profile_incidence_weak_limit hν
    (BoundedContinuousFunction.const Ω (1 : ℝ)) (w := 1) hm
    (fun n => by simp)
  simpa using h

end Balanced

end OAI
