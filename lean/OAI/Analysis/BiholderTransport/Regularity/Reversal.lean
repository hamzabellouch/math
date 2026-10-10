import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ReverseRegular

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section Reversal
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma reverseRay_reverseRay (z : TangentBundle 𝓘(ℝ,Model n) M) :
    reverseRay (reverseRay z)=z := by
  unfold reverseRay
  rw [sprayFlow_reverse]
  rcases z with ⟨x,v⟩
  change (⟨x,(-1:ℝ) • ((-1:ℝ) • v)⟩ : TangentBundle 𝓘(ℝ,Model n) M)=⟨x,v⟩
  rw [neg_one_smul,neg_one_smul,neg_neg]

lemma reverseRay_injectivityDomain {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈injectivityDomain z.1) :
    (reverseRay z).2∈injectivityDomain (reverseRay z).1 := by
  have hi := interior_total_minimizingVectors z hz
  have H : ∀ᶠ w : TangentBundle 𝓘(ℝ,Model n) M in 𝓝 (reverseRay z),
      (reverseRay w).2∈minimizingVectors (reverseRay w).1 := by
    have hN := continuous_reverseRay.continuousAt.preimage_mem_nhds
      (show {q : TangentBundle 𝓘(ℝ,Model n) M | q.2∈minimizingVectors q.1} ∈
        𝓝 (reverseRay (reverseRay z)) from by
          rw [reverseRay_reverseRay]; exact mem_interior_iff_mem_nhds.mp hi)
    exact hN
  have hj : reverseRay z∈interior {q : TangentBundle 𝓘(ℝ,Model n) M |
      q.2∈minimizingVectors q.1} := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [H] with w hw
    have hh := reverseRay_minimizing hw
    change reverseRay (reverseRay w)∈{q : TangentBundle 𝓘(ℝ,Model n) M |
      q.2∈minimizingVectors q.1} at hh
    rwa [reverseRay_reverseRay] at hh
  rwa [←total_injectivityDomain_eq_interior] at hj

end Reversal
end WeakMTWTransport

end

end

end

end OAI
