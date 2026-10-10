import Mathlib
import OAI.Analysis.AffineBernstein.NoOrthant
import OAI.Analysis.AffineBernstein.PositiveFaceMass

namespace OAI

noncomputable section

namespace AffineBernstein

section PositiveFaceDependencies
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

section PositiveFaceLimit
open Filter Metric
open scoped Topology

lemma LocalDistanceConverges.eventually_support_coordinate_lower {n k : ℕ}
    {Cj : ℕ → Set (Space n × ℝ)} {C : Set (Space n × ℝ)}
    (h : LocalDistanceConverges Cj C) (hcl : IsClosed C) (hne : C.Nonempty)
    (s : Fin k → Fin n ⊕ Unit)
    (hs : ∀ z ∈ C, ∀ i, 0 ≤ ambientCoordinates n z (s i)) {R ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ z ∈ Cj j, ‖z‖ ≤ R → ∀ i, -ε ≤ ambientCoordinates n z (s i) := by
  have he (i : Fin k) : ∀ᶠ j in atTop,
      Disjoint (Cj j) (Metric.closedBall (0 : Space n × ℝ) R ∩
        {z | ambientCoordinates n z (s i) ≤ -ε}) := by
    apply h.eventually_disjoint_compact hcl hne
      ((isCompact_closedBall _ _).inter_right
        (isClosed_le (continuous_ambientCoordinate (s i)) continuous_const))
    rw [disjoint_left]
    intro z hz hz'
    have hh := hs z hz i
    have hn : ambientCoordinates n z (s i) ≤ -ε := hz'.2
    linarith
  filter_upwards [Filter.eventually_all.mpr he] with j hj
  intro z hz hzR i
  by_contra hh
  have hzB : z ∈ Metric.closedBall (0 : Space n × ℝ) R := by simpa using hzR
  exact Set.disjoint_left.mp (hj i) hz ⟨hzB,(lt_of_not_ge hh).le⟩

/- The exact positive boundary mass left after removing all finitely many
face strips, uniformly along affine local limits. This is before tube charts;
the integral remains the literal original-graph affine area. -/
theorem complete_affineMaximal_positive_face_mass {n k : ℕ} (hn : 0 < n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u)
    (L : ℕ → (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : ℕ → Space n × ℝ)
    {C : Set (Space n × ℝ)} (hC : IsClosed C)
    (hlim : LocalDistanceConverges (fun j => (fun p => L j p+v j) '' sourceEpigraph Ω u) C)
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hell : ell ≠ 0)
    {b : ℝ} (hcapC : Bornology.IsBounded (C ∩ {z | ell z ≤ b}))
    {o : Space n × ℝ} (ho : o ∈ interior C) (hob : ell o < b)
    (s : Fin k → Fin n ⊕ Unit) (hs : ∀ z ∈ C, ∀ i, 0 ≤ ambientCoordinates n z (s i)) :
    ∃ R > 0, ∃ ε > 0, ∃ a > 0, ∀ᶠ j in atTop,
      (∀ x ∈ Ω, ell (L j (x,u x)+v j) < b → ‖L j (x,u x)+v j‖ ≤ R) ∧
      a ≤ Real.rpow |(L j).toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
        ∫ x in {x | x ∈ Ω ∧ ell (L j (x,u x)+v j) < b} ∩
          {x | ∀ i, ε < ambientCoordinates n (L j (x,u x)+v j) (s i)}, affineAreaDensity u x := by
  let Cj := fun j => (fun z => L j z+v j) '' sourceEpigraph Ω u
  have hclj j : IsClosed (Cj j) := affineSourceEpigraph_closed hΩ hne hcv hu hp hc _ _
  have hcvj j : Convex ℝ (Cj j) := affineSourceEpigraph_convex hΩ hcv hu hp _ _
  have hnej j : (Cj j).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨L j (x,u x)+v j,mem_image_of_mem _ ⟨hx,le_rfl⟩⟩
  obtain ⟨c,hcpos,harea⟩ := complete_affineMaximal_positive_cap_area hΩ hne hcv hu hp hm hc L v
    hC hlim ell hell hcapC ho hob
  obtain ⟨R,hR,hcaps⟩ := hlim.eventually_bounded_caps hC hclj hcvj hnej ell b hcapC (interior_subset ho) hob
  have hpwr : 0 < (n:ℝ)/((n:ℝ)+2) := div_pos (Nat.cast_pos.mpr hn) (by positivity)
  obtain ⟨ε,hε,heps⟩ := exists_pos_mul_rpow_lt hpwr (half_pos hcpos)
    ((k:ℝ)*(graphAreaBoxBound n (2*max R 1)).toReal)
  have hlow := hlim.eventually_support_coordinate_lower hC ⟨o,interior_subset ho⟩ s hs (R := R) hε
  refine ⟨R,hR,ε,hε,c/2,half_pos hcpos,?_⟩
  filter_upwards [harea,hcaps,hlow] with j hja hjc hjl
  let K : Set (Space n) := {x | x ∈ Ω ∧ ell (L j (x,u x)+v j) < b}
  have hG : ContinuousOn (fun x => L j (x,u x)+v j) Ω :=
    ((L j).continuous.comp_continuousOn (continuousOn_id.prodMk hu.continuousOn)).add continuousOn_const
  have hKm : MeasurableSet K := measurableSet_inter_preimage_continuousOn hΩ.measurableSet
    (ell.continuous.comp_continuousOn hG) measurableSet_Iio
  have hKr (x : Space n) (hx : x ∈ K) : ‖L j (x,u x)+v j‖ ≤ R := by
    have hh := hjc ⟨mem_image_of_mem _ ⟨hx.1,le_rfl⟩,hx.2.le⟩
    exact (show ‖L j (x,u x)+v j‖ < R by simpa using hh).le
  refine ⟨fun x hx hb => hKr x ⟨hx,hb⟩,?_⟩
  apply affine_image_good_area_lower hΩ hcv hKm (fun x hx => hx.1) hu hp (L j) (v j) s hR.le hε
  · intro x hx i
    exact (show |(L j (x,u x)+v j).1 i| ≤ ‖(L j (x,u x)+v j).1‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (L j (x,u x)+v j).1 i).trans
      ((le_max_left _ _).trans (hKr x hx))
  · intro x hx
    exact (show |(L j (x,u x)+v j).2| ≤ ‖L j (x,u x)+v j‖ by
        simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_right ‖(L j (x,u x)+v j).1‖ ‖(L j (x,u x)+v j).2‖).trans
      (hKr x hx)
  · intro x hx i
    exact hjl _ (mem_image_of_mem _ ⟨hx.1,le_rfl⟩) (hKr x hx) i
  · exact hja
  · exact heps.le
end PositiveFaceLimit

-- END

end PositiveFaceDependencies

end AffineBernstein

end

end OAI
