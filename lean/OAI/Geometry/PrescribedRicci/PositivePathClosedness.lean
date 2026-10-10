import Mathlib
import OAI.Geometry.PrescribedRicci.PositivePathOpenness
import OAI.Geometry.PrescribedPotential.VolumeNormalization
import OAI.Geometry.PrescribedRicci.NormalizeVolumePath
import OAI.Geometry.PrescribedRicci.PositivePathLimit
import OAI.Geometry.PrescribedRicci.SmoothPathLimit

namespace OAI

/-! Positive Path Closedness. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace Anticanonical.SourceSmooth
open GlobalElliptic
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}

theorem volumePath_soluble_limit (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    (hd : 2 ≤ d) (t : ℕ → ℝ) (u : ℝ)
    (ht : ∀ n, t n ∈ Icc (0:ℝ) 1)
    (hsol : ∀ n, ∃ (φ : SmoothRealFunction A) (b : ℝ), SolvesVolumePath g line (t n) φ b)
    (hu : Tendsto t atTop (𝓝 u)) :
    ∃ (φ : SmoothRealFunction A) (b : ℝ), SolvesVolumePath g line u φ b := by
  choose φ b hφ using hsol
  choose z hz _ using fun n => g.normalizeVolumePath line (ht n) (hφ n)
  obtain ⟨S,⟨D⟩⟩ := exists_gluingData g
  obtain ⟨ψ,ν,hν,hψ⟩ := D.path_smooth_subsequence line hd z
  let M := ‖(⟨(prescribedForcing g line).value,(prescribedForcing g line).continuous⟩ : C(X,ℝ))‖
  have hb (n : ℕ) : (z (ν n)).constant ∈ Icc (-M) M := by
    exact abs_le.mp (volumePath_scalar_bound g line (z (ν n)).time_mem
      ⟨(z (ν n)).positive,(z (ν n)).equation⟩)
  obtain ⟨c,_,μ,hμ,hc⟩ := isCompact_Icc.tendsto_subseq hb
  refine ⟨ψ,c,D.path_limit_solves line (fun n => z (ν (μ n))) ψ u c
    (fun k => (hψ k).comp hμ.tendsto_atTop) ?_ hc⟩
  have he : (fun n => (z (ν (μ n))).time) = t ∘ ν ∘ μ := by
    funext n
    exact hz _
  rw [he]
  exact (hu.comp hν.tendsto_atTop).comp hμ.tendsto_atTop

theorem volumePath_soluble_isClosed (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    (hd : 2 ≤ d) :
    IsClosed {t : Icc (0:ℝ) 1 | ∃ (φ : SmoothRealFunction A) (b : ℝ),
      SolvesVolumePath g line t.val φ b} := by
  apply IsSeqClosed.isClosed
  intro t u ht hu
  exact volumePath_soluble_limit g line hd (fun n => (t n).val) u.val
    (fun n => (t n).property) ht (continuous_subtype_val.continuousAt.tendsto.comp hu)

theorem volumePath_one_exists (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    (hd : 2 ≤ d) :
    ∃ (φ : SmoothRealFunction A) (b : ℝ), SolvesVolumePath g line 1 φ b := by
  let S : Set (Icc (0:ℝ) 1) := {t | ∃ (φ : SmoothRealFunction A) (b : ℝ),
    SolvesVolumePath g line t.val φ b}
  have hS : IsClopen S := ⟨volumePath_soluble_isClosed g line hd,
    (volumePath_soluble_isOpen g line).preimage continuous_subtype_val⟩
  let : PreconnectedSpace (Icc (0:ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  have he : S = univ := hS.eq_univ ⟨⟨0,by norm_num⟩,SmoothRealFunction.constant 0,0,
    volumePath_zero g line⟩
  have h1 : (⟨1,by norm_num⟩ : Icc (0:ℝ) 1) ∈ S := by rw [he]; trivial
  exact h1
end Anticanonical.SourceSmooth

end
end

end OAI
