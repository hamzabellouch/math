import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Fourier.FourierPolynomialSmoothing
import OAI.MeasureTheory.FalconerCompletion.Measures.Ambient2

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
namespace CurrentFalconer.AssemblyRetention
open Set MeasureTheory
open scoped ENNReal

theorem masked_pushforward_deficit {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (m : Measure X) (D : X → Y) (hD : Measurable D) (Γ bad : Set X)
    (_hΓ : MeasurableSet Γ) (hbad : MeasurableSet bad) (w θ : X → ℝ)
    (_hw : Measurable w) (_hθ : Measurable θ) (hw0 : ∀ z, 0≤w z)
    (hθ01 : ∀ z, 0≤θ z ∧ θ z≤1) (M : ℝ) (_hM : 0≤M)
    (hbound : ∀ z∈Γ, w z≤M) (hone : ∀ z∈Γ, z∉bad → θ z=1) :
    let α := (m.withDensity (fun z => ENNReal.ofReal (w z*Γ.indicator (fun _ => (1:ℝ)) z))).map D
    let τ := (m.withDensity (fun z => ENNReal.ofReal (w z*Γ.indicator θ z))).map D
    τ ≤ α ∧ (α-τ) univ ≤ ENNReal.ofReal M*m bad := by
  intro α τ
  have hfg : m.withDensity (fun z => ENNReal.ofReal (w z*Γ.indicator θ z)) ≤
      m.withDensity (fun z => ENNReal.ofReal (w z*Γ.indicator (fun _ => (1:ℝ)) z)) := by
    apply withDensity_mono
    filter_upwards with z
    apply ENNReal.ofReal_le_ofReal
    by_cases hz : z∈Γ
    · simp only [indicator_of_mem hz,mul_one]
      exact mul_le_of_le_one_right (hw0 z) (hθ01 z).2
    · simp only [indicator_of_notMem hz,mul_zero,le_refl]
  refine ⟨Measure.map_mono hfg hD,?_⟩
  let E : Measure X := (ENNReal.ofReal M) • m.restrict bad
  have hdom : m.withDensity (fun z => ENNReal.ofReal (w z*Γ.indicator (fun _ => (1:ℝ)) z)) ≤
      E + m.withDensity (fun z => ENNReal.ofReal (w z*Γ.indicator θ z)) := by
    have he : E = m.withDensity (bad.indicator (fun _ => ENNReal.ofReal M)) := by
      rw [withDensity_indicator hbad,withDensity_const]
    rw [he,←withDensity_add_left (measurable_const.indicator hbad)]
    apply withDensity_mono
    filter_upwards with z
    simp only [Pi.add_apply]
    by_cases hz : z∈Γ
    · simp only [indicator_of_mem hz,mul_one]
      by_cases hb : z∈bad
      · rw [indicator_of_mem hb]
        exact (ENNReal.ofReal_le_ofReal (hbound z hz)).trans le_self_add
      · rw [indicator_of_notMem hb,hone z hz hb,mul_one,zero_add]
    · simp only [indicator_of_notMem hz,mul_zero,ENNReal.ofReal_zero]
      exact zero_le
  have hsub : α-τ ≤ E.map D := Measure.sub_le_of_le_add (by
    simpa only [Measure.map_add _ _ hD] using Measure.map_mono hdom hD)
  calc
    _ ≤ E.map D univ := Measure.le_iff.mp hsub univ MeasurableSet.univ
    _ = ENNReal.ofReal M*m bad := by
      rw [Measure.map_apply hD MeasurableSet.univ,preimage_univ]
      simp [E,Measure.smul_apply,smul_eq_mul]
end CurrentFalconer.AssemblyRetention
end
end

section
section
namespace CurrentFalconer.AssemblyLimit
open MeasureTheory Set Filter
open scoped ENNReal Topology
abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)
def distanceSet {d : ℕ} (E : Set (Ambient d)) : Set ℝ :=
  {r | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}
noncomputable def pairDistance {d : ℕ} (z : Ambient d × Ambient d) : ℝ := dist z.1 z.2
noncomputable def pairWeight {d : ℕ} (z : Ambient d × Ambient d) : ℝ :=
  (pairDistance z)^(-((d:ℝ)-1)/2)

noncomputable def filteredDistanceMeasure {d : ℕ} (μ ν : Measure (Ambient d))
    (Γ : Set (Ambient d × Ambient d)) : Measure ℝ :=
  ((μ.prod ν).withDensity (fun z => ENNReal.ofReal
    (pairWeight z * Γ.indicator (fun _ => (1:ℝ)) z))).map pairDistance
end CurrentFalconer.AssemblyLimit
end
end

end OAI
