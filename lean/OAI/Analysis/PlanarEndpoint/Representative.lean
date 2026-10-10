import OAI.Analysis.PlanarEndpoint.BanachHeat
import OAI.Analysis.PlanarEndpoint.Convolution
import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphTree
import OAI.Analysis.PlanarEndpoint.Heat

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal
namespace PlanarEndpoint

lemma heatPath_eq_abel {f : L2} {U : Plane → TimePath}
    (hU : LocallyIntegrable U volume) (A : ℝ≥0)
    (hball : ∀ x : Plane, ∫ y in ball x 1, ‖U y‖ ≤ A)
    (hid : ∀ t : Time, (fun y => U y t) =ᵐ[volume] (l2Evolution f (t : ℝ) : Plane → ℂ))
    {a : ℝ} (ha : 0 < a) (x : Plane) (t : Time) :
    (∫ z, heatKernel a z • U (x-z)) t = abel f a x (t : ℝ) := by
  rw [ContinuousMap.integral_apply (integrable_heat_smul hU A hball ha x), abel_eq_heat_convolution f ha]
  calc
    _ = ∫ y : Plane, (heatKernel a (x-y) : ℂ) * U y t := by
      simpa only [ContinuousMap.smul_apply, Complex.real_smul, smul_eq_mul, sub_sub_cancel]
        using integral_sub_left_eq_self
          (fun y : Plane => (heatKernel a (x-y) : ℂ) * U y t) volume x
    _ = _ := integral_congr_ae ((hid t).mono fun y hy => by exact congrArg (fun z : ℂ => (heatKernel a (x-y) : ℂ) * z) hy)

lemma mainConclusion_of_integrable_paths (f : L2) (U : Plane → TimePath)
    (hU : LocallyIntegrable U volume) (A : ℝ≥0)
    (hball : ∀ x : Plane, ∫ y in ball x 1, ‖U y‖ ≤ A)
    (hid : ∀ t : Time, (fun y => U y t) =ᵐ[volume] (l2Evolution f (t : ℝ) : Plane → ℂ)) :
    MainConclusion f := by
  let tzero : Time := ⟨0, by constructor <;> norm_num⟩
  have hzero : (fun y => U y tzero) =ᵐ[volume] (f : Plane → ℂ) := by
    simpa only [tzero, l2Evolution_zero] using hid tzero
  let E : Set Plane := {x |
    Tendsto (fun r : ℝ => (Real.pi*r^2)⁻¹ * ∫ y in ball x r, ‖U y-U x‖) (𝓝[>] 0) (𝓝 0) ∧
    IsLebesguePoint f x ∧
    Tendsto (diskAverage f x) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) ∧
    lebesgueRepresentative f x = f x ∧ U x tzero = f x}
  have hE : volume Eᶜ = 0 := by
    apply ae_iff.1
    filter_upwards [ae_banachLebesguePoint hU, ae_isLebesguePoint f,
      ae_diskAverage_tendsto f, lebesgueRepresentative_ae f, hzero] with x h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  refine ⟨E, hE, ?_⟩
  intro x hx
  obtain ⟨hLeb, hpoint, hdisk, hrep, hzero⟩ := hx
  let u : ℝ → ℂ := fun t => U x (projIcc 0 1 (by norm_num) t)
  have hc : Continuous u := (U x).continuous.comp continuous_projIcc
  have hu0 : u 0 = lebesgueRepresentative f x := by
    dsimp only [u]
    rw [projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ∈ Icc 0 1 by simp)]
    exact hzero.trans hrep.symm
  have ht := tendsto_heat_smul_of_lebesgue hU A hball x hLeb
  have htu := ContinuousMap.tendsto_iff_tendstoUniformly.1 ht
  have huni : TendstoUniformlyOn (fun a t => abel f a x t) u
      (𝓝[>] (0 : ℝ)) (Ioo (0 : ℝ) 1) := by
    apply Metric.tendstoUniformlyOn_iff.2
    intro ε hε
    have hh := (Metric.tendstoUniformly_iff.1 htu) ε hε
    filter_upwards [self_mem_nhdsWithin, hh] with a ha hae
    intro t ht
    let tt : Time := ⟨t, ht.1.le, ht.2.le⟩
    have he := hae tt
    rw [heatPath_eq_abel hU A hball hid ha x tt] at he
    simpa only [u, projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) (show t ∈ Icc 0 1 from ⟨ht.1.le, ht.2.le⟩)] using he
  refine ⟨hpoint, u, hc.continuousOn, hu0, ?_, ?_, ?_, huni⟩
  · simpa only [hu0, hrep] using hdisk
  · intro t ht
    exact huni.tendsto_at ht
  · rw [← hu0]
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

end PlanarEndpoint
end

end OAI
