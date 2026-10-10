import Mathlib
import OAI.Analysis.AffineBernstein.NormedInteriorLimits
import OAI.Analysis.AffineBernstein.AffineCapArea

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section PositiveLimitCap
open Filter Metric

/- Positive cap area for a local limit of genuine affine images. This is
bounds.tex, Lemma positive-cap-area, with a strict height cutoff (hence it also
bounds the closed cap whenever that area is expressed as a measure). -/
theorem positive_cap_area_of_affine_local_limit {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (L : ℕ → (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : ℕ → Space n × ℝ)
    (hclj : ∀ j, IsClosed ((fun p => L j p+v j) '' sourceEpigraph Ω u))
    (hcvj : ∀ j, Convex ℝ ((fun p => L j p+v j) '' sourceEpigraph Ω u))
    (hnej : ∀ j, ((fun p => L j p+v j) '' sourceEpigraph Ω u).Nonempty)
    {C : Set (Space n × ℝ)} (hC : IsClosed C)
    (hlim : LocalDistanceConverges (fun j => (fun p => L j p+v j) '' sourceEpigraph Ω u) C)
    {b : ℝ} (hcapC : Bornology.IsBounded (C ∩ {z | z.2 ≤ b}))
    {o : Space n × ℝ} (ho : o ∈ interior C) (hob : o.2 < b) :
    ∃ c > 0, ∀ᶠ j in atTop, c ≤ affineImageCapArea Ω u (L j) (v j) b := by
  let D := fun j => (fun p => L j p+v j) '' sourceEpigraph Ω u
  obtain ⟨R,hR,hcaps⟩ := hlim.eventually_bounded_caps hC hclj hcvj hnej
    (ContinuousLinearMap.snd ℝ (Space n) ℝ) b hcapC (interior_subset ho) hob
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp isOpen_interior o ho
  have hclosedball : Metric.closedBall o (r/2) ⊆ C :=
    (Metric.closedBall_subset_ball (by linarith)).trans (hball.trans interior_subset)
  have hballs := hlim.eventually_normed_ball_subset hclj hcvj hnej (half_pos hr) hclosedball
  let ε := (b-o.2)/6
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : o.2 ≤ b-6*ε := by dsimp [ε]; linarith
  obtain ⟨c,hc,huniform⟩ := exists_uniform_positive_affine_cap_area n (r := (r/2)/4)
    (R := R) hε (by positivity) hR.le
  refine ⟨c,hc,?_⟩
  filter_upwards [hcaps,hballs] with j hj hjball
  have hK : IsCompact {z | z ∈ D j ∧ z.2 ≤ b} := by
    exact (isCompact_iff_isClosed_bounded).mpr
      ⟨(hclj j).inter (isClosed_le continuous_snd continuous_const),
        (isBounded_ball (x := (0 : Space n × ℝ)) (r := R)).subset hj⟩
  apply huniform Ω u (L j) (v j) o b hΩ hu hp hm hK _ hjball hgap
  intro z hz hzb
  exact (show ‖z‖ < R by simpa only [Metric.mem_ball,dist_zero_right] using hj ⟨hz,hzb⟩).le

end PositiveLimitCap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/- A nonzero real functional has full range. -/
/- A nonzero support is strictly positive at every interior point. -/
/- The literal split along a normalized support vector. The second component
is the kernel of the support; no quotient or degenerate coordinate is used. -/

end AffineBernstein
end

end OAI
