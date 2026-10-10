import OAI.Analysis.CircleDomains.Modulus.AverageOscillation
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Averaging an axis-by-axis pointwise bound over a product set. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma abs_sub_iterated_average_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NeZero μ] [NeZero ν] {f : X → Y → ℝ} {V : X → ℝ} {z H : ℝ}
    (hf : ∀ᵐ x ∂μ, Integrable (f x) ν)
    (hmean : Integrable (fun x => ⨍ y, f x y ∂ν) μ)
    (hV : Integrable V μ)
    (hb : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, |z-f x y| ≤ H+V x) :
    |z-(⨍ x, ⨍ y, f x y ∂ν ∂μ)| ≤ H+(⨍ x, V x ∂μ) := by
  have hpoint : ∀ᵐ x ∂μ, |z-(⨍ y, f x y ∂ν)| ≤ H+V x := by
    filter_upwards [hf, hb] with x hx hbx
    exact abs_sub_average_le_of_ae hx z (H+V x) hbx
  apply (abs_sub_average_le_average_abs_sub hmean z).trans
  have hh := average_mono_real ((integrable_const z).sub hmean).abs
    ((integrable_const H).add hV) hpoint
  have he : (⨍ x, H+V x ∂μ) = H+(⨍ x, V x ∂μ) := by
    simpa only [Pi.add_apply, average_const] using
      (average_add (integrable_const H : Integrable (fun _ : X => H) μ) hV)
  have hh' : (⨍ x, |z-(⨍ y, f x y ∂ν)| ∂μ) ≤ (⨍ x, H+V x ∂μ) := by
    simpa only [Pi.sub_apply, Pi.add_apply] using hh
  exact hh'.trans_eq he

end CircleDomainRigidity

end

end OAI
