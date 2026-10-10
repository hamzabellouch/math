import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.TotalInjectivity

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def reverseRay (z : TangentBundle 𝓘(ℝ,Model n) M) := tangentScale (-1) (sprayFlow 1 z)

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma reverseRay_involutive : Function.Involutive (reverseRay (n := n) (M := M)) := by
  intro z
  dsimp only [reverseRay]
  rw [sprayFlow_reverse]
  rcases z with ⟨x,p⟩
  change (⟨x,(-1:ℝ) • ((-1:ℝ) • p)⟩ : TangentBundle 𝓘(ℝ,Model n) M)=⟨x,p⟩
  rw [neg_one_smul,neg_one_smul,neg_neg]

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma continuous_reverseRay : Continuous (reverseRay (n := n) (M := M)) := by
  exact contMDiff_tangentScale.continuous.comp
    (continuous_const.prodMk (contMDiff_sprayFlow.continuous.comp
      (continuous_const.prodMk continuous_id)))

lemma reverseRay_minimizing {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) :
    (reverseRay z).2∈minimizingVectors (reverseRay z).1 := by
  change dist (reverseRay z).1 (riemannianExp (reverseRay z).1 (reverseRay z).2)=‖(reverseRay z).2‖
  rw [riemannianExp_eq_sprayFlow]
  change dist (sprayFlow 1 z).1 (sprayFlow 1 (tangentScale (-1) (sprayFlow 1 z))).1=
    ‖(-1:ℝ) • (sprayFlow 1 z).2‖
  rw [sprayFlow_reverse,neg_one_smul,norm_neg,sprayFlow_speed]
  change dist (sprayFlow 1 z).1 z.1=‖z.2‖
  rw [dist_comm,←riemannianExp_eq_sprayFlow]
  exact hz

lemma reverseRay_regular {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈injectivityDomain z.1) :
    (reverseRay z).2∈injectivityDomain (reverseRay z).1 := by
  have hzi := interior_total_minimizingVectors z hz
  have H := continuous_reverseRay.continuousAt.eventually
    (show ∀ᶠ q in 𝓝 (reverseRay (reverseRay z)), q.2∈minimizingVectors q.1 from
      by rw [reverseRay_involutive z]; exact mem_interior_iff_mem_nhds.mp hzi)
  have HR : ∀ᶠ q in 𝓝 (reverseRay z), q.2∈minimizingVectors q.1 := by
    filter_upwards [H] with q hq
    exact (reverseRay_involutive q) ▸ (reverseRay_minimizing hq)
  have HI : reverseRay z∈interior {q : TangentBundle 𝓘(ℝ,Model n) M | q.2∈minimizingVectors q.1} :=
    mem_interior_iff_mem_nhds.mpr HR
  rwa [←total_injectivityDomain_eq_interior] at HI

end WeakMTWTransport

end

end OAI
