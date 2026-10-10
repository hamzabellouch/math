import OAI.Geometry.ProjectionVolume.OuterApproximation
import OAI.Geometry.ProjectionVolume.Translation
import OAI.Geometry.ProjectionVolume.PolytopeCauchy

namespace OAI

open Set Filter
open scoped Pointwise Topology RealInnerProductSpace

namespace Paper092

theorem projectionBody_support_centered_of_polytope_support {n : ℕ}
    (hpoly : ∀ {ι : Type} [Fintype ι] (P : HPolytope n ι) (u : Euclidean n),
      SupportGeometry.support (projectionBody P.body) (innerSL ℝ u) = brightness P.body u)
    (K : Set (Euclidean n)) (hc : IsCompact K) (hv : Convex ℝ K)
    (h0 : (0 : Euclidean n) ∈ interior K) (u : Euclidean n) :
    SupportGeometry.support (projectionBody K) (innerSL ℝ u) = brightness K u := by
  apply le_antisymm (projectionBody_support_le K u)
  have hbound : ∀ r : ℝ, 1 < r → brightness K u ≤
      r ^ (n - 1) * SupportGeometry.support (projectionBody K) (innerSL ℝ u) := by
    intro r hr
    obtain ⟨F, P, hKP, hPr⟩ := exists_outer_hpolytope_sandwich hc hv h0 hr
    calc
      brightness K u ≤ brightness P.body u := brightness_mono hKP P.compact u
      _ = SupportGeometry.support (projectionBody P.body) (innerSL ℝ u) := (hpoly P u).symm
      _ ≤ SupportGeometry.support (projectionBody (r • K)) (innerSL ℝ u) :=
        support_mono ⟨0, zero_mem_projectionBody P.body⟩ (projectionBody_isCompact _)
          (projectionBody_mono hPr (hc.smul r)) u
      _ = r ^ (n - 1) * SupportGeometry.support (projectionBody K) (innerSL ℝ u) := by
        rw [projectionBody_body_smul K r (by linarith),
          SupportGeometry.support_smul _ _ (by positivity), abs_of_pos (by linarith)]
  have ht : Tendsto (fun r : ℝ =>
      r ^ (n - 1) * SupportGeometry.support (projectionBody K) (innerSL ℝ u))
      (𝓝[>] 1) (𝓝 (SupportGeometry.support (projectionBody K) (innerSL ℝ u))) := by
    have hcont : Continuous (fun r : ℝ =>
        r ^ (n - 1) * SupportGeometry.support (projectionBody K) (innerSL ℝ u)) := by
      fun_prop
    simpa only [one_pow, one_mul] using (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hbound r hr

theorem projectionBody_support_of_polytope_support {n : ℕ}
    (hpoly : ∀ {ι : Type} [Fintype ι] (P : HPolytope n ι) (u : Euclidean n),
      SupportGeometry.support (projectionBody P.body) (innerSL ℝ u) = brightness P.body u)
    (K : Set (Euclidean n)) (hc : IsCompact K) (hv : Convex ℝ K)
    (hint : (interior K).Nonempty) (u : Euclidean n) :
    SupportGeometry.support (projectionBody K) (innerSL ℝ u) = brightness K u := by
  obtain ⟨x, hx⟩ := hint
  let K0 := -x +ᵥ K
  have h0 : (0 : Euclidean n) ∈ interior K0 := by
    simpa [K0, interior_vadd, mem_vadd_set_iff_neg_vadd_mem] using hx
  have hs := projectionBody_support_centered_of_polytope_support hpoly K0
    (hc.vadd (-x)) (hv.vadd (-x)) h0 u
  simpa only [K0, projectionBody_vadd, brightness_vadd] using hs

theorem projectionBody_support {d : ℕ} (_hd : 2 ≤ d) (K : Set (Euclidean d))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hint : (interior K).Nonempty)
    (u : Euclidean d) :
    SupportGeometry.support (projectionBody K) (innerSL ℝ u) = brightness K u :=
  projectionBody_support_of_polytope_support
    (fun P v => P.projectionBody_support v) K hK hconv hint u

end Paper092

end OAI
