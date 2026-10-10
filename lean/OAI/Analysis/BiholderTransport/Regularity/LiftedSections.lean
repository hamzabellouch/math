import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.DoubleMountain

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

def liftedGapSection (u v : M → ℝ) (x : M) (r : ℝ) :
    Set (TangentSpace 𝓘(ℝ,Model n) x) :=
  {p | p∈minimizingVectors x ∧ u x+‖p‖^2/2+v (riemannianExp x p)≤r}

lemma cost_minimizingVector {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) : cost x (riemannianExp x p)=‖p‖^2/2 := by
  unfold cost
  rw [show dist x (riemannianExp x p)=‖p‖ from hp]

lemma mem_liftedGapSection_iff {u v : M → ℝ} {x : M} {r : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} :
    p∈liftedGapSection u v x r ↔ p∈minimizingVectors x ∧ riemannianExp x p∈gapSection u v x r := by
  constructor
  · intro hp
    exact ⟨hp.1,by simpa only [gapSection,mem_ofPred_eq,contactGap,cost_minimizingVector hp.1] using hp.2⟩
  · intro hp
    exact ⟨hp.1,by simpa only [gapSection,mem_ofPred_eq,contactGap,cost_minimizingVector hp.1] using hp.2⟩

variable [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma liftedGapSection_image (u v : M → ℝ) (x : M) (r : ℝ) :
    riemannianExp x '' liftedGapSection (n := n) u v x r=gapSection u v x r := by
  apply Subset.antisymm
  · rintro y ⟨p,hp,rfl⟩
    exact (mem_liftedGapSection_iff.mp hp).2
  · intro y hy
    obtain ⟨p,hp,hpy⟩ := exists_minimizing_vector (n := n) x y
    exact ⟨p,mem_liftedGapSection_iff.mpr ⟨hp,by rwa [hpy]⟩,hpy⟩

variable [Nonempty M]

lemma WeakMTW.convex_liftedGapSection (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (huv : IsCostDualPair u v)
    (x : M) (r : ℝ) : Convex ℝ (liftedGapSection (n := n) u v x r) := by
  intro p hp q hq a b ha hb hab
  have hp' := mem_liftedGapSection_iff.mp hp
  have hq' := mem_liftedGapSection_iff.mp hq
  obtain ⟨hm,hcomp⟩ := hmtw.double_mountain hp.1 hq.1 ha hb hab
  rw [mem_liftedGapSection_iff]
  refine ⟨hm,?_⟩
  change u x+cost x (riemannianExp x (a • p+b • q))+v (riemannianExp x (a • p+b • q))≤r
  have HB : cTransform u (riemannianExp x (a • p+b • q))≤
      r-u x-cost x (riemannianExp x (a • p+b • q)) := by
    rw [cTransform_le_iff hu]
    intro z
    rw [cost_symm (riemannianExp x (a • p+b • q)) z]
    have hcp := dualPair_gap_nonneg hv huv z (riemannianExp x p)
    have hcq := dualPair_gap_nonneg hv huv z (riemannianExp x q)
    have hpS : u x+cost x (riemannianExp x p)+v (riemannianExp x p)≤r := hp'.2
    have hqS : u x+cost x (riemannianExp x q)+v (riemannianExp x q)≤r := hq'.2
    have hpB : cost x (riemannianExp x p)-cost z (riemannianExp x p)≤r-u x+u z := by
      dsimp [contactGap] at hcp
      linarith [hpS]
    have hqB : cost x (riemannianExp x q)-cost z (riemannianExp x q)≤r-u x+u z := by
      dsimp [contactGap] at hcq
      linarith [hqS]
    have hmax := (hcomp z).trans (max_le hpB hqB)
    linarith
  rw [huv.2]
  linarith

end WeakMTWTransport

end

end OAI
