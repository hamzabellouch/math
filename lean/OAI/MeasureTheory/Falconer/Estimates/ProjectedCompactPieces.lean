import OAI.MeasureTheory.Falconer.Measures.ProjectedSupportPoints
import OAI.MeasureTheory.Falconer.Geometry.ProjectedSeparation

namespace OAI

/-! # Positive compact pieces separated in the original and projected spaces -/
namespace Falconer
open Set Metric MeasureTheory Filter NormedSpace
open scoped ENNReal Topology
variable {d m : ℕ}

theorem continuousAt_radialDirection_pair {x y : Space d} (hne : y ≠ x) :
    ContinuousAt (fun z : Space d × Space d => radialDirection z.1 z.2) (x,y) := by
  have hd : ContinuousAt (fun z : Space d × Space d => z.2-z.1) (x,y) :=
    (continuous_snd.sub continuous_fst).continuousAt
  exact (hd.norm.inv₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))).smul hd

theorem projected_compact_pieces (μ : ProbabilityMeasure (Space d))
    (hK : IsCompact (μ : Measure (Space d)).support)
    (P : Space d →L[ℝ] Space m)
    [NullSingletonClass ((μ : Measure (Space d)).map P)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A B : Set (Space d), IsCompact A ∧ IsCompact B ∧
      A ⊆ (μ : Measure (Space d)).support ∧ B ⊆ (μ : Measure (Space d)).support ∧
      0 < (μ : Measure (Space d)) A ∧ 0 < (μ : Measure (Space d)) B ∧
      ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ∃ w : Space d, ‖w‖ = 1 ∧
        ∀ a ∈ A, ∀ b ∈ B, r/2 ≤ dist a b ∧ dist a b ≤ 2*r ∧
          c ≤ ‖P (radialDirection a b)‖ ∧ c ≤ ‖P (radialDirection b a)‖ ∧
          dist (radialDirection a b) w < ε := by
  obtain ⟨x,hx,y,hy,hxyP⟩ := distinct_projected_support_points μ P
  have hxy : x ≠ y := fun h => hxyP (congrArg P h)
  let r := dist x y
  let a := dist (P x) (P y)
  have hr : 0 < r := dist_pos.mpr hxy
  have ha : 0 < a := dist_pos.mpr hxyP
  have hlo : ∀ᶠ z : Space d × Space d in 𝓝 (x,y), r/2 < dist z.1 z.2 :=
    (isOpen_lt continuous_const (continuous_fst.dist continuous_snd)).mem_nhds (by
      change r/2 < r
      linarith)
  have hup : ∀ᶠ z : Space d × Space d in 𝓝 (x,y), dist z.1 z.2 < 2*r :=
    (isOpen_lt (continuous_fst.dist continuous_snd) continuous_const).mem_nhds (by
      change r < 2*r
      linarith)
  have hp : ∀ᶠ z : Space d × Space d in 𝓝 (x,y), a/2 < dist (P z.1) (P z.2) :=
    (isOpen_lt continuous_const
      ((P.continuous.comp continuous_fst).dist (P.continuous.comp continuous_snd))).mem_nhds (by
        change a/2 < a
        linarith)
  have hw : ∀ᶠ z : Space d × Space d in 𝓝 (x,y),
      dist (radialDirection z.1 z.2) (radialDirection x y) < ε :=
    (continuousAt_radialDirection_pair (Ne.symm hxy)).tendsto (ball_mem_nhds _ hε)
  have hall : ∀ᶠ z : Space d × Space d in 𝓝 (x,y),
      r/2 < dist z.1 z.2 ∧ dist z.1 z.2 < 2*r ∧
        a/2 < dist (P z.1) (P z.2) ∧
          dist (radialDirection z.1 z.2) (radialDirection x y) < ε := by
    filter_upwards [hlo,hup,hp,hw] with z hz1 hz2 hz3 hz4
    exact ⟨hz1,hz2,hz3,hz4⟩
  obtain ⟨δ,hδ,hδgood⟩ := Metric.eventually_nhds_iff_ball.mp hall
  let A := (μ : Measure (Space d)).support ∩ closedBall x (δ/2)
  let B := (μ : Measure (Space d)).support ∩ closedBall y (δ/2)
  obtain ⟨hAc,hAm⟩ := positive_compact_support_ball μ hK hx (by positivity : 0 < δ/2)
  obtain ⟨hBc,hBm⟩ := positive_compact_support_ball μ hK hy (by positivity : 0 < δ/2)
  refine ⟨A,B,hAc,hBc,inter_subset_left,inter_subset_left,hAm,hBm,
    r,(a/2)/(2*r),hr,by positivity,radialDirection x y,?_,?_⟩
  · exact norm_normalize (sub_ne_zero.mpr (Ne.symm hxy))
  · intro x' hx' y' hy'
    have hd : dist (x',y') (x,y) < δ := by
      rw [Prod.dist_eq]
      exact max_lt (lt_of_le_of_lt hx'.2 (by linarith)) (lt_of_le_of_lt hy'.2 (by linarith))
    obtain ⟨h1,h2,h3,h4⟩ := hδgood _ (mem_ball.mpr hd)
    refine ⟨h1.le,h2.le,projected_direction_lower_of_dist P x' y' (by positivity) h3.le h2.le,?_,h4⟩
    apply projected_direction_lower_of_dist P y' x' (by positivity)
    · simpa only [dist_comm] using h3.le
    · simpa only [dist_comm] using h2.le

end Falconer

end OAI
