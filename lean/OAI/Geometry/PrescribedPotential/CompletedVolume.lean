import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalHessian
import OAI.Geometry.PrescribedPotential.GlobalMetricEntries
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.PotentialDensity
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.SobolevDeterminant

namespace OAI

/-! Completed Volume. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical BoundedContinuousFunction
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def completedVolume (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u : D.localizers.Sobolev ((k : ℝ)+2)) : D.localizers.Sobolev (k : ℝ) :=
  ∑ p, D.product k hk (D.localizers.embed (k : ℝ) (D.determinantWeight p))
    (D.determinant k hk d (fun i j => D.localizers.embed (k : ℝ) (D.metricEntry p i j) +
      D.completedHessian k p i j u))

lemma completedVolume_contDiff (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    ContDiff ℝ ∞ (D.completedVolume k hk) := by
  apply ContDiff.sum
  intro p _
  exact (D.product k hk (D.localizers.embed (k : ℝ) (D.determinantWeight p))).contDiff.comp
    (D.determinant_contDiff k hk d _ (fun i j => contDiff_const.add (D.completedHessian k p i j).contDiff))

lemma completedVolume_embed (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (φ : SmoothRealFunction A) :
    D.completedVolume k hk (D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ)) =
      D.localizers.embed (k : ℝ) (Smooth.ofReal (g.potentialDensity φ)) := by
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  apply D.localizers.strong_injective (k : ℝ) hs
  ext x
  simp only [completedVolume, map_sum, BoundedContinuousFunction.sum_apply]
  rw [D.localizers.strong_embed _ hs]
  have hterm (p : ι) : D.localizers.strong (k : ℝ)
      (D.product k hk (D.localizers.embed (k : ℝ) (D.determinantWeight p))
        (D.determinant k hk d (fun i j => D.localizers.embed (k : ℝ) (D.metricEntry p i j) +
          D.completedHessian k p i j (D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ))))) x =
      D.localizers.weight p x * ((g.potentialDensity φ).value x : ℂ) := by
    rw [D.product_strong, BoundedContinuousFunction.mul_apply, D.localizers.strong_embed _ hs]
    change D.determinantWeight p x * _ = _
    by_cases hz : D.localizers.weight p x = 0
    · rw [D.determinantWeight_zero p hz, hz, zero_mul, zero_mul]
    · have hx : x ∈ tsupport (D.localizers.weight p : X → ℂ) := subset_tsupport _ hz
      rw [D.determinantWeight_apply p hx]
      erw [D.determinant_strong]
      have hm : (fun i j => D.localizers.strong (k : ℝ)
          (D.localizers.embed (k : ℝ) (D.metricEntry p i j) +
            D.completedHessian k p i j (D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ))) x) =
          g.matrix (D.patch p).index (A.chart (D.patch p).index x) +
            φ.hessian (D.patch p).index (A.chart (D.patch p).index x) := by
        ext i j
        rw [D.completedHessian_embed, map_add, BoundedContinuousFunction.add_apply,
          D.localizers.strong_embed _ hs, D.localizers.strong_embed _ hs]
        change D.metricEntry p i j x + D.localizedHessian p i j (Smooth.ofReal φ) x = _
        rw [D.metricEntry_apply p i j hx, D.localizedHessian_source p i j φ hx]
        rfl
      rw [hm, g.potentialDensity_complex φ (D.patch p).index (by simpa using D.patch_source p hx)]
      unfold KaehlerMetric.volumePolynomial
      ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, D.localizers.sum_one, one_mul]
  rfl

lemma completedVolume_real (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    ∀ u ∈ D.localizers.realCompletion ((k : ℝ)+2),
      D.completedVolume k hk u ∈ D.localizers.realCompletion (k : ℝ) := by
  apply ClosedCore.maps_closure_range (D.localizers.realCoreMap ((k : ℝ)+2))
    (D.localizers.realCoreMap (k : ℝ)) (D.completedVolume k hk)
    (D.completedVolume_contDiff k hk).continuous
  intro f
  refine ⟨RealSmooth.ofReal (g.potentialDensity f.source), ?_⟩
  change D.completedVolume k hk (D.localizers.embed ((k : ℝ)+2) f.val) = _
  rw [← f.ofReal_source, D.completedVolume_embed]
  rfl

end GluingData
end GlobalElliptic

end
end

end OAI
