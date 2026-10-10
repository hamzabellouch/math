import Mathlib
import OAI.Analysis.AffineBernstein.CompletePositiveCapFurther
import OAI.Analysis.AffineBernstein.AffineStripArea
import OAI.Analysis.AffineBernstein.OrthantHeight

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

open Filter Metric
open scoped Topology

lemma exists_pos_mul_rpow_lt {p c : ℝ} (hp : 0 < p) (hc : 0 < c) (d : ℝ) :
    ∃ ε > 0, d * ε^p < c := by
  have hf : ContinuousAt (fun t : ℝ => d*t^p) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 p (Or.inr hp.le))
  have hh : ∀ᶠ t in 𝓝 (0 : ℝ), d*t^p < c :=
    hf.eventually_lt_const (by simpa only [Real.zero_rpow hp.ne',mul_zero] using hc)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨r/2,half_pos hr,hball ?_⟩
  simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hr)] using
    (show r/2 < r by linarith)

/- A finite union of actual affine-image thin strips obeys the sum of the
source strip-area bounds, without a disjointness or integrability premise. -/
theorem affine_image_finite_strip_area {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hxR : ∀ x ∈ K, ∀ i, |(L (x,u x)+v).1 i| ≤ R)
    (htR : ∀ x ∈ K, |(L (x,u x)+v).2| ≤ R)
    (hcover : ∀ x ∈ K, ∃ i : Fin n ⊕ Unit,
      |ambientCoordinates n (L (x,u x)+v) i| ≤ ε) :
    Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
      (∫ x in K, affineAreaDensity u x) ≤
      ((n:ℝ)+1) * (graphAreaBoxBound n (2*max R 1)).toReal * ε^((n:ℝ)/((n:ℝ)+2)) := by
  classical
  let S (i : Fin n ⊕ Unit) := K ∩ {x | |ambientCoordinates n (L (x,u x)+v) i| ≤ ε}
  have hc (i : Fin n ⊕ Unit) :
      ContinuousOn (fun x => |ambientCoordinates n (L (x,u x)+v) i|) K := by
    exact (continuous_ambientCoordinate i).abs.comp_continuousOn
      (((L.continuous.comp_continuousOn (continuousOn_id.prodMk (hu.continuousOn.mono hKΩ))).add continuousOn_const))
  have hm (i : Fin n ⊕ Unit) : MeasurableSet (S i) :=
    measurableSet_inter_preimage_continuousOn hK (hc i) measurableSet_Iic
  have hcov : K ⊆ ⋃ i, S i := by
    intro x hx
    obtain ⟨i,hi⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨i,hx,hi⟩
  have hsum := integral_le_sum_cover (μ := volume) (f := affineAreaDensity u) hK hm (fun i => inter_subset_left) hcov
    (fun x hx => Real.rpow_nonneg (hp x (hKΩ hx)).det_pos.le (1/((n:ℝ)+2)))
  calc
    _ ≤ Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
        ∑ i, ∫ x in S i, affineAreaDensity u x :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (abs_nonneg _) _)
    _ = ∑ i, Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
        ∫ x in S i, affineAreaDensity u x := Finset.mul_sum _ _ _
    _ ≤ ∑ _i : Fin n ⊕ Unit, (graphAreaBoxBound n (2*max R 1)).toReal * ε^((n:ℝ)/((n:ℝ)+2)) := by
      apply Finset.sum_le_sum
      intro i _
      exact affine_image_strip_area hΩ hcv (hm i) (fun x hx => hKΩ hx.1) hu hp L v i hR hε
        (fun x hx => hxR x hx.1) (fun x hx => htR x hx.1) (fun x hx => hx.2)
    _ = _ := by simp; ring

/- The m=0 case of bounds.tex is impossible for actual affine images of the
complete affine-maximal graph. In particular the limit cannot be an orthant. -/
theorem complete_affineMaximal_no_orthant_limit {n : ℕ} (hn : 0 < n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u)
    (L : ℕ → (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : ℕ → Space n × ℝ) :
    ¬ LocalDistanceConverges (fun j => (fun z => L j z+v j) '' sourceEpigraph Ω u)
      (ambientOrthant n) := by
  intro hlim
  let Cj := fun j => (fun z => L j z+v j) '' sourceEpigraph Ω u
  let b : ℝ := n+2
  have hb : 0 < b := by dsimp [b]; positivity
  have hclj j : IsClosed (Cj j) := affineSourceEpigraph_closed hΩ hne hcv hu hp hc _ _
  have hcvj j : Convex ℝ (Cj j) := affineSourceEpigraph_convex hΩ hcv hu hp _ _
  have hnej j : (Cj j).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨L j (x,u x)+v j,mem_image_of_mem _ ⟨hx,le_rfl⟩⟩
  have hob : orthantHeight n (orthantCenter n) < b := by rw [orthantCenter_height]; dsimp [b]; linarith
  obtain ⟨c,hcpos,harea⟩ := complete_affineMaximal_positive_cap_area hΩ hne hcv hu hp hm hc L v
    (isClosed_ambientOrthant n) hlim (orthantHeight n) (orthantHeight_ne_zero n)
    (orthant_cap_bounded n hb.le) (orthantCenter_interior n) hob
  obtain ⟨R,hR,hcaps⟩ := hlim.eventually_bounded_caps (isClosed_ambientOrthant n) hclj hcvj hnej
    (orthantHeight n) b (orthant_cap_bounded n hb.le) (interior_subset (orthantCenter_interior n)) hob
  have hpwr : 0 < (n:ℝ)/((n:ℝ)+2) := div_pos (Nat.cast_pos.mpr hn) (by positivity)
  obtain ⟨ε,hε,heps⟩ := exists_pos_mul_rpow_lt hpwr hcpos
    (((n:ℝ)+1)*(graphAreaBoxBound n (2*max R 1)).toReal)
  have hstrip := orthant_limit_boundary_strips hlim hclj hcvj hnej (R := R) hε
  obtain ⟨j,hja,hjc,hjs⟩ := (harea.and (hcaps.and hstrip)).exists
  let K : Set (Space n) := {x | x ∈ Ω ∧ orthantHeight n (L j (x,u x)+v j) < b}
  have hG : ContinuousOn (fun x => L j (x,u x)+v j) Ω :=
    ((L j).continuous.comp_continuousOn (continuousOn_id.prodMk hu.continuousOn)).add continuousOn_const
  have hKm : MeasurableSet K := measurableSet_inter_preimage_continuousOn hΩ.measurableSet
    ((orthantHeight n).continuous.comp_continuousOn hG) measurableSet_Iio
  have hKr (x : Space n) (hx : x ∈ K) : ‖L j (x,u x)+v j‖ ≤ R := by
    have hh := hjc ⟨mem_image_of_mem _ ⟨hx.1,le_rfl⟩,hx.2.le⟩
    exact (show ‖L j (x,u x)+v j‖ < R by simpa using hh).le
  have hupper := affine_image_finite_strip_area hΩ hcv hKm (fun x hx => hx.1) hu hp (L j) (v j)
    hR.le hε (fun x hx i => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · exact (not_lt_of_ge (hja.trans hupper)) heps
  · exact (show |(L j (x,u x)+v j).1 i| ≤ ‖(L j (x,u x)+v j).1‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (L j (x,u x)+v j).1 i).trans
      ((le_max_left _ _).trans (hKr x hx))
  · exact (show |(L j (x,u x)+v j).2| ≤ ‖L j (x,u x)+v j‖ by
        simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_right ‖(L j (x,u x)+v j).1‖ ‖(L j (x,u x)+v j).2‖).trans
      (hKr x hx)
  · exact hjs _ (mem_image_of_mem _ ⟨hx.1,le_rfl⟩)
      (affineGraph_not_mem_interior_epigraph Ω u (L j) (v j) x) (hKr x hx)

end AffineBernstein

end

end OAI
