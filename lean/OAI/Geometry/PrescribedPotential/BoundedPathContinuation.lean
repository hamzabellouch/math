import Mathlib
import OAI.Geometry.PrescribedPotential.NormalizedPathCompactness
import OAI.Geometry.PrescribedPotential.SmoothPathOpenness

namespace OAI

/-! Bounded Path Continuation. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

 

def PathSobolevBounds (h : SemipositiveAnticanonicalMetric A) (x₀ : X) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ (t b : ℝ) (φ : SmoothRealFunction A),
    t ∈ Icc 0 1 → φ.value x₀ = 0 → SolvesVolumePath g h t φ b →
      ‖D.localizers.embed (((2*k : ℕ) : ℝ)+2) (Smooth.ofReal φ)‖ ≤ C

omit [ConnectedSpace X] in
lemma smoothVolumePathTimes_relatively_closed (h : SemipositiveAnticanonicalMetric A)
    (x₀ : X) (hbound : D.PathSobolevBounds h x₀) :
    IsClosed ((Subtype.val : Icc (0:ℝ) 1 → ℝ) ⁻¹' SmoothVolumePathTimes g h x₀) := by
  apply IsSeqClosed.isClosed
  intro t tLim ht htLim
  choose φ b hn hs using ht
  have hB : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      ‖D.localizers.embed (((2*k : ℕ) : ℝ)+2) (RealSmooth.ofReal (φ n)).val‖ ≤ C := by
    intro k
    obtain ⟨C,hC⟩ := hbound k
    exact ⟨C,fun n => hC (t n).val (b n) (φ n) (t n).property (hn n) (hs n)⟩
  have ht' : Tendsto (fun n => (t n).val) atTop (𝓝 tLim.val) :=
    (continuous_subtype_val.tendsto tLim).comp htLim
  obtain ⟨fLim,bLim,r,hr,hb,hf,hnLim,hsLim⟩ := D.normalized_path_sequence_compact h x₀
    (fun n => (t n).val) b tLim.val ht' (fun n => (t n).property)
    (fun n => RealSmooth.ofReal (φ n)) (by simpa only [RealSmooth.source_ofReal] using hn)
    (by simpa only [RealSmooth.source_ofReal] using hs) hB
  exact ⟨fLim.source,bLim,hnLim,hsLim⟩

 

theorem smoothVolumePathTimes_full_of_bounds (h : SemipositiveAnticanonicalMetric A)
    (x₀ : X) (hbound : D.PathSobolevBounds h x₀) :
    Icc 0 1 ⊆ SmoothVolumePathTimes g h x₀ := by
  let S : Set (Icc (0:ℝ) 1) := Subtype.val ⁻¹' SmoothVolumePathTimes g h x₀
  have hc : IsClopen S := ⟨D.smoothVolumePathTimes_relatively_closed h x₀ hbound,
    (smoothVolumePathTimes_isOpen g h x₀).preimage continuous_subtype_val⟩
  have hn : S.Nonempty := ⟨⟨0,by constructor <;> norm_num⟩,
    smoothVolumePathTimes_zero g h x₀⟩
  have he := hc.eq_univ hn
  intro t ht
  have hh : (⟨t,ht⟩ : Icc (0:ℝ) 1) ∈ S := by rw [he]; trivial
  exact hh

end GluingData
end GlobalElliptic

namespace Anticanonical.SourceSmooth
open GlobalElliptic
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

 

theorem prescribedPotential_of_path_bounds (P : A.ProjectiveEmbedding)
    (h : SemipositiveAnticanonicalMetric A) (D : GluingData (projectiveBackground P) ι)
    (x₀ : X) (hbound : D.PathSobolevBounds h x₀) : HasPrescribedVolumePotential P h := by
  obtain ⟨φ,b,_,hs⟩ := D.smoothVolumePathTimes_full_of_bounds h x₀ hbound
    (by constructor <;> norm_num : (1:ℝ) ∈ Icc 0 1)
  exact volumePath_one P h φ b hs

end Anticanonical.SourceSmooth

end
end

end OAI
