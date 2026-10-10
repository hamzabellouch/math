import Mathlib
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.PositivePotentialLinearization
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.SmoothLocalPath
import OAI.Geometry.PrescribedPotential.SmoothPotentialDifference
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Smooth Path Openness. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical ComplexOrder
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma logRatio_deform_eq_logDensity (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) (x : X) :
    (g.logRatio (g.deform φ hp)).value x = Real.log ((g.potentialDensity φ).value x) := by
  obtain ⟨i,hi⟩ := A.covers x
  change g.logRatioValue (g.deform φ hp) x = _
  rw [g.logRatioValue_local _ i hi,g.potentialDensity_quotient φ i hi]
  exact (Real.log_div
    (ne_of_gt ((g.deform φ hp).volumeCoefficient_pos i ((A.chart i).mapsTo hi)))
    (ne_of_gt (g.volumeCoefficient_pos i ((A.chart i).mapsTo hi)))).symm

lemma positivePotential_add (g : KaehlerMetric A) (φ ψ : SmoothRealFunction A)
    (hφ : g.PositivePotential φ) (hψ : (g.deform φ hφ).PositivePotential ψ) :
    g.PositivePotential (φ.addFunction ψ) := by
  intro i z hz
  rw [SmoothRealFunction.hessian_addFunction φ ψ i hz,← add_assoc]
  exact hψ i z hz

lemma logRatio_deform_add (g : KaehlerMetric A) (φ ψ : SmoothRealFunction A)
    (hφ : g.PositivePotential φ) (hψ : (g.deform φ hφ).PositivePotential ψ) (x : X) :
    (g.logRatio (g.deform (φ.addFunction ψ) (g.positivePotential_add φ ψ hφ hψ))).value x =
      (g.logRatio (g.deform φ hφ)).value x +
      ((g.deform φ hφ).logRatio ((g.deform φ hφ).deform ψ hψ)).value x := by
  obtain ⟨i,hi⟩ := A.covers x
  change g.logRatioValue _ x = g.logRatioValue _ x + (g.deform φ hφ).logRatioValue _ x
  rw [g.logRatioValue_local _ i hi,g.logRatioValue_local _ i hi,
    (g.deform φ hφ).logRatioValue_local _ i hi]
  simp only [volumeCoefficient,deform,
    SmoothRealFunction.hessian_addFunction φ ψ i ((A.chart i).mapsTo hi),add_assoc]
  ring

end KaehlerMetric

 

theorem smooth_log_path_eventually_solvable [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (g : KaehlerMetric A) (F : SmoothRealFunction A) (x₀ : X) :
    ∀ᶠ t : ℝ in 𝓝 0, ∃ (φ : SmoothRealFunction A) (b : ℝ)
      (hp : g.PositivePotential φ), φ.value x₀ = 0 ∧
      ∀ x, (g.logRatio (g.deform φ hp)).value x = t * F.value x + b := by
  obtain ⟨S,⟨D⟩⟩ := GlobalElliptic.exists_gluingData g
  filter_upwards [D.smooth_path_eventually_solvable (GlobalElliptic.RealSmooth.ofReal F) x₀]
    with t ht
  obtain ⟨φ,b,hp,hn,he⟩ := ht
  refine ⟨φ,b,hp,hn,fun x => ?_⟩
  rw [g.logRatio_deform_eq_logDensity φ hp x,he x,Real.log_exp]
  rfl

 

def SmoothVolumePathTimes (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (x₀ : X) : Set ℝ :=
  {t | ∃ (φ : SmoothRealFunction A) (b : ℝ), φ.value x₀ = 0 ∧ SolvesVolumePath g h t φ b}

lemma smoothVolumePathTimes_zero (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (x₀ : X) : 0 ∈ SmoothVolumePathTimes g h x₀ :=
  ⟨SmoothRealFunction.constant 0,0,rfl,volumePath_zero g h⟩

lemma smoothVolumePathTimes_eventually [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) (x₀ : X)
    {t₀ : ℝ} (ht₀ : t₀ ∈ SmoothVolumePathTimes g h x₀) :
    ∀ᶠ t in 𝓝 t₀, t ∈ SmoothVolumePathTimes g h x₀ := by
  obtain ⟨φ₀,b₀,hn₀,hp₀,he₀⟩ := ht₀
  have hs : Tendsto (fun t : ℝ => t-t₀) (𝓝 t₀) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t-t₀) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto t₀
  filter_upwards [hs.eventually (smooth_log_path_eventually_solvable
    (g.deform φ₀ hp₀) (prescribedForcing g h) x₀)] with t ht
  obtain ⟨ψ,a,hψ,hnψ,heψ⟩ := ht
  refine ⟨φ₀.addFunction ψ,b₀+a,?_,g.positivePotential_add φ₀ ψ hp₀ hψ,?_⟩
  · change φ₀.value x₀ + ψ.value x₀ = 0
    rw [hn₀,hnψ,add_zero]
  · intro x
    rw [g.logRatio_deform_add φ₀ ψ hp₀ hψ,he₀ x,heψ x]
    ring

 

theorem smoothVolumePathTimes_isOpen [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) (x₀ : X) :
    IsOpen (SmoothVolumePathTimes g h x₀) :=
  isOpen_iff_mem_nhds.mpr (fun _ ht => smoothVolumePathTimes_eventually g h x₀ ht)

end Anticanonical.SourceSmooth

end
end

end OAI
