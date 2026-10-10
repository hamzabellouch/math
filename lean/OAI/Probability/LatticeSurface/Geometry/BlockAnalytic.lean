import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.FacetDeficitAnalytic
import OAI.Probability.LatticeSurface.Convexity.FacetQuantile
import OAI.Probability.LatticeSurface.Convexity.InteriorQuantile
import OAI.Probability.LatticeSurface.Convexity.QuantileCentroid
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.QuantitativeTransport
import OAI.Probability.LatticeSurface.Convexity.RadialExposure
import OAI.Probability.LatticeSurface.Convexity.SliceDensity
import OAI.Probability.LatticeSurface.Convexity.SliceGeometry
import OAI.Probability.LatticeSurface.Convexity.SliceMoments
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality
import OAI.Probability.LatticeSurface.Geometry.BlockEdgeGeometry
import OAI.Probability.LatticeSurface.Geometry.BlockFacetGeometry
import OAI.Probability.LatticeSurface.Geometry.BlockRadial
import OAI.Probability.LatticeSurface.Geometry.BlockVolume
import OAI.Probability.LatticeSurface.Geometry.EdgeCoordinates
import OAI.Probability.LatticeSurface.Geometry.FacetBody
import OAI.Probability.LatticeSurface.Geometry.FacetExposure
import OAI.Probability.LatticeSurface.Geometry.TriangularCover
import OAI.Probability.LatticeSurface.Geometry.TriangularGeometry
import OAI.Probability.LatticeSurface.Geometry.UniformFacet

namespace OAI

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

end TriangularLipschitz

namespace FacetExposure

end FacetExposure

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

open MeasureTheory Set

open scoped ENNReal

noncomputable section

namespace EdgeCoordinates

end EdgeCoordinates

namespace EdgeCoordinates

end EdgeCoordinates

namespace EdgeCoordinates

end EdgeCoordinates

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace SliceTransport

end SliceTransport

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace TriangularLipschitz

lemma filling_image_mix {L n : ℕ} (E : Filling L ≃ₗ[ℝ] (Fin n → ℝ))
    (s t : Vertex → ℝ) {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hsum : α+γ=1) :
    ∀ x ∈ E '' fillingPolytope L s, ∀ y ∈ E '' fillingPolytope L t,
      α • x+γ • y ∈ E '' fillingPolytope L (fun b => α*s b+γ*t b) := by
  rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
  exact ⟨α • a+γ • b,fillingPolytope_mix ha hb hα hγ hsum,by simp⟩

lemma positiveLogVolume_concave {L n : ℕ} (E : Filling L ≃ₗ[ℝ] (Fin n → ℝ))
    (hE : MeasurePreserving E) (s t : Vertex → ℝ) {α γ : ℝ}
    (hs : 0 < fillingVolume L s) (ht : 0 < fillingVolume L t)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hsum : α+γ=1) :
    α*positiveLogVolume L s+γ*positiveLogVolume L t ≤
      positiveLogVolume L (fun b => α*s b+γ*t b) := by
  have hs' : 0 < (fillingVolume L s).toReal := ENNReal.toReal_pos hs.ne' (fillingVolume_lt_top L s).ne
  have ht' : 0 < (fillingVolume L t).toReal := ENNReal.toReal_pos ht.ne' (fillingVolume_lt_top L t).ne
  have hbm := FacetVolume.compact_volume_brunn_minkowski
    (isCompact_filling_image E s) (isCompact_filling_image E t)
    (isCompact_filling_image E (fun b => α*s b+γ*t b))
    ((nonempty_of_measure_ne_zero hs.ne').image E) ((nonempty_of_measure_ne_zero ht.ne').image E)
    hα hγ hsum (filling_image_mix E s t hα hγ hsum)
  simp only [filling_volume_image E hE] at hbm
  have hlog := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hs' α) (Real.rpow_pos_of_pos ht' γ)) hbm
  rw [Real.log_mul (Real.rpow_pos_of_pos hs' α).ne' (Real.rpow_pos_of_pos ht' γ).ne',
    Real.log_rpow hs',Real.log_rpow ht'] at hlog
  exact hlog

lemma log_volume_ratio {L : ℕ} {s t h : Vertex → ℝ}
    (hs : 0 < fillingVolume L s) (ht : 0 < fillingVolume L t) (hh : 0 < fillingVolume L h) :
    Real.log ((fillingVolume L h).toReal/
      Real.sqrt ((fillingVolume L s).toReal*(fillingVolume L t).toReal)) =
      positiveLogVolume L h-(positiveLogVolume L s+positiveLogVolume L t)/2 := by
  have hs' : 0 < (fillingVolume L s).toReal := ENNReal.toReal_pos hs.ne' (fillingVolume_lt_top L s).ne
  have ht' : 0 < (fillingVolume L t).toReal := ENNReal.toReal_pos ht.ne' (fillingVolume_lt_top L t).ne
  have hh' : 0 < (fillingVolume L h).toReal := ENNReal.toReal_pos hh.ne' (fillingVolume_lt_top L h).ne
  rw [Real.log_div hh'.ne' (Real.sqrt_pos.2 (mul_pos hs' ht')).ne',
    Real.log_sqrt (mul_pos hs' ht').le,Real.log_mul hs'.ne' ht'.ne']
  rfl

lemma exists_filling_facet_constant (L n : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (s t h : Vertex → ℝ) (x y : Vertex) (τ : ℝ)
      (E : Filling L ≃ₗ[ℝ] (Fin (n+1) → ℝ)),
      MeasurePreserving E → |τ|=1 → x ∈ box L → y ∈ box L → Adj x y →
      (∀ s a, E a 0 = τ*(filledHeight L s a y-filledHeight L s a x)+edgeOffset L τ s x) →
      0 < fillingVolume L s → 0 < fillingVolume L t → 0 < fillingVolume L h →
      (∃ q₀ : Fin n → ℝ, ∀ q ∈ Metric.ball q₀ (β/16),
        Fin.cons (1+edgeOffset L τ s x) q ∈ E '' fillingPolytope L s) →
      (∃ q₀ : Fin n → ℝ, ∀ q ∈ Metric.ball q₀ (β/16),
        Fin.cons (1+edgeOffset L τ t x) q ∈ E '' fillingPolytope L t) →
      (∀ b, (s b+t b)/2=h b) →
      κ*((meanHeight L s y-meanHeight L s x)-(meanHeight L t y-meanHeight L t x))^2 ≤
        positiveLogVolume L h-(positiveLogVolume L s+positiveLogVolume L t)/2 := by
  obtain ⟨κ,hκ,hfacet⟩ := FacetVolume.exists_uniform_facet_constant n (β/16)
    (volume (Metric.closedBall (0 : Filling L) (2*L))).toReal (by linarith)
  refine ⟨κ,hκ,?_⟩
  intro s t h x y τ E hE hτ hx hy hxy hE0 hs ht hh hballS hballT hmid
  obtain ⟨qS,hqS⟩ := hballS
  obtain ⟨qT,hqT⟩ := hballT
  have hresult := hfacet (E '' fillingPolytope L s) (E '' fillingPolytope L t)
    (E '' fillingPolytope L h) (1+edgeOffset L τ s x) (1+edgeOffset L τ t x) qS qT
    (isCompact_filling_image E s) (isCompact_filling_image E t) (isCompact_filling_image E h)
    (convex_filling_image E s) (convex_filling_image E t) (convex_filling_image E h)
    (by rwa [filling_volume_image E hE]) (by rwa [filling_volume_image E hE])
    (filling_projection_width s hτ hx hy hxy E hE0) (filling_projection_width t hτ hx hy hxy E hE0)
    hqS hqT (filling_image_volume_bound E hE s) (filling_image_volume_bound E hE t) ?_
  · rw [coordinate_meanHeight E hE hE0 s hs,coordinate_meanHeight E hE hE0 t ht] at hresult
    simp only [filling_volume_image E hE] at hresult
    rw [log_volume_ratio hs ht hh] at hresult
    have hτsq : τ^2=1 := by nlinarith [sq_abs τ]
    have heq : ((1+edgeOffset L τ s x-(τ*(meanHeight L s y-meanHeight L s x)+edgeOffset L τ s x))-
        (1+edgeOffset L τ t x-(τ*(meanHeight L t y-meanHeight L t x)+edgeOffset L τ t x)))^2 =
        ((meanHeight L s y-meanHeight L s x)-(meanHeight L t y-meanHeight L t x))^2 := by
      calc
        _ = τ^2*((meanHeight L s y-meanHeight L s x)-(meanHeight L t y-meanHeight L t x))^2 := by ring
        _ = _ := by rw [hτsq,one_mul]
    rwa [heq] at hresult
  · have heq : (fun b => (1/2:ℝ)*s b+(1/2:ℝ)*t b)=h := by
      funext b; linarith [hmid b]
    simpa only [heq] using filling_image_mix E s t (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)

end TriangularLipschitz

end
end
end
end

end OAI
