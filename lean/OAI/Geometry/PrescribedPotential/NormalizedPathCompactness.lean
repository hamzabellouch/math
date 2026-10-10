import Mathlib
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealSmoothCompactness
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.SmoothPathLimit
import OAI.Geometry.PrescribedPotential.VolumeNormalization

namespace OAI

/-! Normalized Path Compactness. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace RealSmooth

omit [T2Space X] [CompactSpace X] in
@[simp] lemma source_ofReal (φ : SmoothRealFunction A) : (ofReal φ).source = φ := by
  cases φ
  rfl

end RealSmooth
namespace Localizers
variable (D : Localizers A ι)

lemma real_source_value_tendsto (f : ℕ → RealSmooth A) (fLim : RealSmooth A)
    (hf : ∀ s : ℝ, Tendsto (fun n => D.embed s (f n).val) atTop
      (𝓝 (D.embed s fLim.val))) (x : X) :
    Tendsto (fun n => (f n).source.value x) atTop (𝓝 (fLim.source.value x)) := by
  let s : ℝ := (Module.finrank ℝ (EC d) : ℝ)+1
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s := by
    dsimp only [s]
    linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (EC d))]
  exact (Complex.continuous_re.tendsto (fLim.val x)).comp
    (D.smooth_value_tendsto s hs (fun n => (f n).val) fLim.val (hf s) x)

end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

 

theorem normalized_path_sequence_compact (h : SemipositiveAnticanonicalMetric A)
    (x₀ : X) (t b : ℕ → ℝ) (tLim : ℝ) (ht : Tendsto t atTop (𝓝 tLim))
    (hinterval : ∀ n, t n ∈ Icc 0 1) (f : ℕ → RealSmooth A)
    (hnorm : ∀ n, (f n).source.value x₀ = 0)
    (hsol : ∀ n, SolvesVolumePath g h (t n) (f n).source (b n))
    (hbound : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      ‖D.localizers.embed (((2*k : ℕ) : ℝ)+2) (f n).val‖ ≤ C) :
    ∃ (fLim : RealSmooth A) (bLim : ℝ) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (b ∘ r) atTop (𝓝 bLim) ∧
      (∀ s : ℝ, Tendsto (fun n => D.localizers.embed s (f (r n)).val) atTop
        (𝓝 (D.localizers.embed s fLim.val))) ∧
      fLim.source.value x₀ = 0 ∧ SolvesVolumePath g h tLim fLim.source bLim := by
  let : Nonempty X := ⟨x₀⟩
  let C : ℝ := ‖(⟨(prescribedForcing g h).value,
    (prescribedForcing g h).continuous⟩ : C(X,ℝ))‖
  have hb (n : ℕ) : b n ∈ Icc (-C) C :=
    abs_le.mp (volumePath_scalar_bound g h (hinterval n) (hsol n))
  obtain ⟨bLim,_,r₀,hr₀,hb₀⟩ := (isCompact_Icc : IsCompact (Icc (-C) C)).tendsto_subseq hb
  have hbound' : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      ‖D.localizers.embed (((2*k : ℕ) : ℝ)+2) (f (r₀ n)).val‖ ≤ C := by
    intro k
    obtain ⟨K,hK⟩ := hbound k
    exact ⟨K,fun n => hK (r₀ n)⟩
  obtain ⟨fLim,r₁,hr₁,hf⟩ := D.real_smooth_sequence_compact (fun n => f (r₀ n)) hbound'
  let r := r₀ ∘ r₁
  have hr : StrictMono r := hr₀.comp hr₁
  have hbLim : Tendsto (b ∘ r) atTop (𝓝 bLim) := hb₀.comp hr₁.tendsto_atTop
  have hnLim : fLim.source.value x₀ = 0 := by
    have hv := D.localizers.real_source_value_tendsto (fun n => f (r n)) fLim hf x₀
    have he : (fun n => (f (r n)).source.value x₀) = (fun _ : ℕ => (0 : ℝ)) :=
      funext (fun n => hnorm (r n))
    rw [he] at hv
    exact tendsto_nhds_unique hv tendsto_const_nhds
  refine ⟨fLim,bLim,r,hr,hbLim,hf,hnLim,?_⟩
  exact D.smooth_path_limit_solution h (t ∘ r) (b ∘ r) tLim bLim
    (ht.comp hr.tendsto_atTop) hbLim (fun n => f (r n)) fLim hf (fun n => hsol (r n))

end GluingData
end GlobalElliptic

end
end

end OAI
