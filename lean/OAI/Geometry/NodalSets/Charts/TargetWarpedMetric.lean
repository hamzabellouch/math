import OAI.Geometry.NodalSets.Charts.ImmersionMetric
import OAI.Geometry.NodalSets.Elliptic.TargetEmbedding
import OAI.Geometry.NodalSets.Elliptic.WarpedAmbientForm

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

variable (B : Base → AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ)
    (hB : ContMDiff (𝓡 4) 𝓘(ℝ,AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞ B)
    (hs : ∀ x v w, B x v w = B x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < B x v v)
    (q : Base → ℝ) (hq : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ q) (hpos : ∀ x, 0 < q x)

def ambientWeightedMetric : SmoothMetric :=
  immersionMetric targetEmbedding targetEmbedding_smooth targetEmbedding_immersion
    (fun x ↦ warpedAmbientForm (B x.1) (q x.1))
    (warpedAmbientForm_smooth _ _ (hB.comp contMDiff_fst) (hq.comp contMDiff_fst))
    (fun x ↦ warpedAmbientForm_symm _ _ (hs x.1))
    (fun x ↦ warpedAmbientForm_pos _ (hp x.1) (hpos x.1))

lemma ambientWeightedMetric_inner (x : Manifold5) (v w : TangentSpace modelWithCorners x) :
    (ambientWeightedMetric B hB hs hp q hq hpos).inner x v w =
      B x.1 (mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase) (Subtype.val : Base → AmbientBase) x.1 v.1)
        (mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase) (Subtype.val : Base → AmbientBase) x.1 w.1) +
      (q x.1)^2 * @inner ℝ ℂ _
        (mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 v.2 : ℂ)
        (mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 w.2 : ℂ) := by
  change warpedAmbientForm (B x.1) (q x.1)
    (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding x v)
    (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding x w) = _
  erw [targetEmbedding_derivative]
  rfl

lemma ambientWeightedMetric_metricMatrix (c : PartialEquiv Manifold5 Model) (y : Model)
    (i j : Index) :
    metricMatrix (ambientWeightedMetric B hB hs hp q hq hpos) c y i j =
      warpedAmbientForm (B (c.symm y).1) (q (c.symm y).1)
        (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding (c.symm y)
          (mfderiv 𝓘(ℝ,Model) modelWithCorners c.symm y (frame i)))
        (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding (c.symm y)
          (mfderiv 𝓘(ℝ,Model) modelWithCorners c.symm y (frame j))) := rfl

end
end Yau.Target

end OAI
