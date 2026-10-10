import Mathlib
import OAI.Analysis.AffineBernstein.UniformSphericalCap
import OAI.Analysis.AffineBernstein.ModelCentering

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

section ModelCentering
open Filter Metric
open scoped Topology Pointwise

variable {k m d : ℕ}

/- Transverse coordinate changes preserve the literal model conditions. -/
/- The actual support-coordinate change gives precisely the split model to
which the thin-slice construction applies. -/
/- The rescaling is genuinely an invertible linear image, not an abstract
limit operation. -/
/- Reindexing the limiting (s,r) orthant gives the manuscript's exact
(k+1)-model, including the case of no remaining transverse coordinates. -/
/- A supported thin-slice model produces an actual model with one additional
nonnegative direction in the original affine local-limit family. All normalizers,
subsequences and limiting sets are constructed here. -/
/- Boundary zero in the fiber is incompatible with maximality of the number
of model directions: the missing new model is actually produced, not assumed. -/
/- Dilation of a convex body containing zero is monotone for nonnegative
radii. This includes a zero inner radius. -/
/- Centering is unaffected by any invertible linear transverse change. -/
/- Uniform centering for every distinguished fiber in a maximal model
family. The single maximality hypothesis rules out actual (k+1)-models;
it carries no centering estimate and is discharged by choosing maximal k. -/
/- The positive diagonal base change sending s to the all-ones base point. -/
/- Positive diagonal choices of the distinguished directions preserve all
model properties, in particular compactness of caps. -/
/- Geometry.tex Proposition 2.7: the centering constant is uniform over all
models, positive fibers, and admissible distinguished coordinates of a maximal
family. Zero-dimensional transverse fibers are included. -/
end ModelCentering

/- Every admissible graph path has at least the Euclidean length of its
base displacement. This uses the literal C¹-path definition of completeness. -/
/- A straight base segment has constant velocity, including its endpoints
for the closed-interval derivative used in the metric. -/
/- Length estimate on a segment on which the graph height is nondecreasing. -/
/- Expansion in the frozen Euclidean coordinate vectors. -/
/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/
/- The straight-segment estimate in its geometric form. Both possible
orientations of a monotone height are included. -/
open Filter
open scoped Topology

/- Intrinsic convergence always entails convergence of base points. -/
/- Completeness prevents a finite base endpoint from being lost when graph
paths make a sequence intrinsically Cauchy. -/
/- A chord bound along a family of segments turns ordinary Cauchy control of
base and height into control for the actual graph metric. -/
/- Restricting a monotone-height ray to any oriented subsegment gives the
uniform chord bound used to exhibit an intrinsic Cauchy tail. -/
/- A bounded ray with monotone graph height cannot end at a missing finite
base point of a complete graph. This proves the metric step rather than
assuming properness of the embedding. -/
/- A differentiable convex function on a finite half-open interval has a
monotone tail (in one of the two orientations). -/
/- The tangent line at the initial point bounds a convex ray from below,
so an upper bound on a finite ray implies a two-sided bound. -/
/- Completeness forbids any bounded convex ray from reaching a missing finite
endpoint. Convexity and two-sided variation, not a growth hypothesis, produce
the required metric Cauchy sequence. -/
/- The metric obstruction applied to an arbitrary bounded-height sequence,
not merely points already lying on a fixed ray. This is the core boundary
properness argument in geometry.tex:36–55. -/
/- Actual height sublevels are closed in the ambient base space. No convex
extension of u to missing boundary points is used. -/
/- Finite boundary blow-up, derived from the manuscript's literal Euclidean
intrinsic completeness assumption. -/
/- The epigraph is genuinely closed in Rⁿ × R. Completeness was not
silently replaced by properness of the graph embedding. -/
/- Strict version of the second-derivative test, with specified derivatives. -/
theorem strictConvexOn_of_hasDerivWithinAt2_pos {D : Set ℝ} (hD : Convex ℝ D)
    {f f' f'' : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : ∀ x ∈ interior D, 0 < f'' x) : StrictConvexOn ℝ D f := by
  have he : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine strictConvexOn_of_deriv2_pos hD hf fun x hx => ?_
  convert hf''₀ x hx using 1
  dsimp
  rw [deriv_eqOn isOpen_interior (fun y hy => ?_) hx]
  exact (hf'' _ hy).congr he (by rw [he hy])

/- The standing Hessian hypothesis gives strict convexity on every nonconstant
base segment, with the literal coordinate Hessian, not an abstract Hessian. -/
theorem strictConvexOn_segment {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {x y : Space n} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : y ≠ x) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => u (x + t • (y - x))) := by
  let γ : ℝ → Space n := fun t => x + t • (y - x)
  let d : ℝ → ℝ := fun t => fderiv ℝ u (γ t) (y - x)
  let dd : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ u) (γ t) (y - x) (y - x)
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Ω :=
    hcv.add_smul_mem hx (by simpa using hy) ht
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγd (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hf : ContinuousOn (u ∘ γ) (Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hγ.continuous.continuousOn hseg
  have hdf (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt (u ∘ γ) (d t) (interior (Icc (0 : ℝ) 1)) t :=
    (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hγd t)).hasDerivWithinAt
  have hdd (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt d (dd t) (interior (Icc (0 : ℝ) 1)) t := by
    have hd := (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
    have he := hd.clm_apply (hasFDerivAt_const (y - x) (γ t))
    have hc := he.comp_hasDerivAt t (hγd t)
    simpa only [d, dd, Function.comp_def, ContinuousLinearMap.comp_zero,
      zero_add, ContinuousLinearMap.flip_apply] using
      hc.hasDerivWithinAt (s := interior (Icc (0 : ℝ) 1))
  exact strictConvexOn_of_hasDerivWithinAt2_pos (convex_Icc _ _) hf hdf hdd
    (fun t ht => second_fderiv_pos
      (hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht))))
      (hp _ (hseg t (interior_subset ht))) (sub_ne_zero.mpr hxy))

/- The tangent-plane height used in all source sections. -/
def tangentHeight {n : ℕ} (u : Space n → ℝ) (a x : Space n) : ℝ :=
  u x - u a - fderiv ℝ u a (x - a)

@[simp] theorem tangentHeight_self {n : ℕ} (u : Space n → ℝ) (a : Space n) :
    tangentHeight u a a = 0 := by simp [tangentHeight]

theorem tangentHeight_pos {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) (hxa : x ≠ a) :
    0 < tangentHeight u a x := by
  have hc := strictConvexOn_segment hΩ hcv hu hp ha hx hxa
  have hd : HasDerivAt (fun t : ℝ => u (a + t • (x - a)))
      (fderiv ℝ u a (x - a)) 0 := by
    have hγ : HasDerivAt (fun t : ℝ => a + t • (x - a)) (x - a) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (x - a)).const_add a
    have hdu : HasFDerivAt u (fderiv ℝ u a) (a + (0 : ℝ) • (x - a)) := by
      simpa using ((hu.contDiffAt (hΩ.mem_nhds ha)).differentiableAt (by simp)).hasFDerivAt
    exact hdu.comp_hasDerivAt 0 hγ
  have hs := hc.lt_slope_of_hasDerivAt (x := 0) (y := 1)
    (by norm_num) (by norm_num) (by norm_num) hd
  simp only [slope_def_field, sub_zero, div_one, zero_smul, add_zero, one_smul,
    add_sub_cancel] at hs
  exact sub_pos.mpr hs

theorem convexOn_tangentHeight {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hcv : ConvexOn ℝ Ω u) (a : Space n) :
    ConvexOn ℝ Ω (tangentHeight u a) := by
  refine ⟨hcv.1, ?_⟩
  intro x hx y hy s t hs ht hst
  have he := hcv.2 hx hy hs ht hst
  have hv : s • x + t • y - a = s • (x - a) + t • (y - a) := by
    rw [smul_sub, smul_sub]
    have heq : s • a + t • a = a := by rw [← add_smul, hst, one_smul]
    calc
      _ = s • x + t • y - (s • a + t • a) := by rw [heq]
      _ = _ := by module
  simp only [tangentHeight, hv, map_add, map_smul, smul_eq_mul]
  simp only [smul_eq_mul] at he
  have heq : s * u a + t * u a = u a := by rw [← add_mul, hst, one_mul]
  nlinarith

theorem continuousOn_tangentHeight {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : ContinuousOn u Ω) (a : Space n) :
    ContinuousOn (tangentHeight u a) Ω := by
  exact (hu.sub continuousOn_const).sub
    ((fderiv ℝ u a).continuous.comp (continuous_id.sub continuous_const)).continuousOn

/- Tangent-plane sublevels are closed, by closedness of the actual epigraph.
No implicit completeness-invariance under a shear is needed. -/
theorem isClosed_tangent_sublevel {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hcv : ConvexOn ℝ Ω u)
    (hc : EuclideanGraphComplete Ω u) (a : Space n) (t : ℝ) :
    IsClosed {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  have he := isClosed_epigraph_of_complete hΩ hne hu hcv hc
  have hf : Continuous (fun x : Space n => (x, u a + fderiv ℝ u a (x - a) + t)) :=
    continuous_id.prodMk ((continuous_const.add
      ((fderiv ℝ u a).continuous.comp (continuous_id.sub continuous_const))).add continuous_const)
  convert he.preimage hf using 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage, tangentHeight]
  constructor <;> rintro ⟨hx, hh⟩ <;> exact ⟨hx, by linarith⟩

/- A finite-radius positive support gap yields a linear coercivity bound.
This replaces only the choice of constants in geometry.tex:56–67, not any
standing hypothesis or conclusion. -/
theorem tangentHeight_coercive {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {a : Space n} (ha : a ∈ Ω) :
    ∃ r > 0, ∃ m > 0, ∀ x ∈ Ω, r ≤ ‖x - a‖ →
      m * ‖x - a‖ ≤ r * tangentHeight u a x := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds ha)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hrΩ : Metric.closedBall a r ⊆ Ω :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hRΩ
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hcg := convexOn_tangentHeight hcu a
  have hct := continuousOn_tangentHeight hu.continuousOn a
  have hsΩ : Metric.sphere a r ⊆ Ω := Metric.sphere_subset_closedBall.trans hrΩ
  obtain ⟨m, hm, hmlow⟩ : ∃ m : ℝ, 0 < m ∧
      ∀ x ∈ Metric.sphere a r, m ≤ tangentHeight u a x := by
    by_cases hne : (Metric.sphere a r).Nonempty
    · obtain ⟨y, hy, hmin⟩ := (isCompact_sphere a r).exists_isMinOn hne (hct.mono hsΩ)
      refine ⟨tangentHeight u a y, tangentHeight_pos hΩ hcv hu hp ha (hsΩ hy) ?_, hmin⟩
      intro he
      subst y
      have hh : (0 : ℝ) = r := by simpa [Metric.mem_sphere] using hy
      linarith
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  refine ⟨r, hr, m, hm, ?_⟩
  intro x hx hxr
  have hn : 0 < ‖x - a‖ := hr.trans_le hxr
  let q := r / ‖x - a‖
  have hq : 0 < q := div_pos hr hn
  have hq1 : q ≤ 1 := (div_le_one hn).mpr hxr
  let y := a + q • (x - a)
  have hyn : ‖y - a‖ = r := by
    simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    exact div_mul_cancel₀ r hn.ne'
  have hys : y ∈ Metric.sphere a r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hyn
  have hv : (1 - q) • a + q • x = y := by dsimp [y]; module
  have hineq := hcg.2 ha hx (sub_nonneg.mpr hq1) hq.le (show (1 - q) + q = 1 by ring)
  rw [hv, tangentHeight_self] at hineq
  simp only [smul_eq_mul, mul_zero, zero_add] at hineq
  have hmm : m ≤ r / ‖x - a‖ * tangentHeight u a x := (hmlow y hys).trans hineq
  have heq : r / ‖x - a‖ * tangentHeight u a x =
      (r * tangentHeight u a x) / ‖x - a‖ := by ring
  rw [heq] at hmm
  exact (le_div_iff₀ hn).mp hmm

/- The compact tangent sections required throughout the manuscript, proved
from PD Hessian, convexity of the open base, and intrinsic graph completeness. -/
theorem isCompact_tangent_sublevel {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω) (t : ℝ) :
    IsCompact {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hclosed := isClosed_tangent_sublevel hΩ ⟨a, ha⟩ hu hcu hc a t
  obtain ⟨r, hr, m, hm, hbound⟩ := tangentHeight_coercive hΩ hcv hu hp ha
  apply (isCompact_closedBall a (max r (r * t / m))).of_isClosed_subset hclosed
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_cases hxr : r ≤ ‖x - a‖
  · apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hm).mpr
    have hb := (hbound x hx.1 hxr).trans (mul_le_mul_of_nonneg_left hx.2 hr.le)
    simpa [mul_comm] using hb
  · exact (le_of_not_ge hxr).trans (le_max_left _ _)

theorem tangentHeight_nonneg {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) :
    0 ≤ tangentHeight u a x := by
  by_cases hxa : x = a
  · simp [hxa]
  · exact (tangentHeight_pos hΩ hcv hu hp ha hx hxa).le

/- Interior of the epigraph, including the correct restriction to the open
base domain. This is a local continuity fact and needs no completeness. -/
theorem interior_epigraph {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContinuousOn u Ω) :
    interior {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2} =
      {p | p.1 ∈ Ω ∧ u p.1 < p.2} := by
  have hopen : IsOpen {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 < p.2} := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have h1 : ∀ᶠ q : Space n × ℝ in 𝓝 p, q.1 ∈ Ω :=
      (continuous_fst.tendsto p) (hΩ.mem_nhds hp.1)
    have hdiff : ContinuousAt (fun q : Space n × ℝ => u q.1 - q.2) p :=
      ((hu.continuousAt (hΩ.mem_nhds hp.1)).comp continuous_fst.continuousAt).sub
        continuous_snd.continuousAt
    filter_upwards [h1, hdiff.tendsto (Iio_mem_nhds (sub_neg.mpr hp.2))] with q hq hqu
    exact ⟨hq, sub_neg.mp hqu⟩
  apply le_antisymm
  · intro p hp
    have hpD := interior_subset hp
    refine ⟨hpD.1, ?_⟩
    have hv : Continuous (fun z : ℝ => (p.1, z)) := continuous_const.prodMk continuous_id
    have hn : Ici (u p.1) ∈ 𝓝 p.2 := by
      have hpre := (hv.tendsto p.2) (mem_interior_iff_mem_nhds.mp hp)
      exact mem_of_superset hpre (fun z hz => hz.2)
    have hh := mem_interior_iff_mem_nhds.mpr hn
    simpa only [interior_Ici, mem_Ioi] using hh
  · exact interior_maximal (fun p hp => ⟨hp.1, hp.2.le⟩) hopen

theorem frontier_epigraph_of_complete {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hcv : ConvexOn ℝ Ω u)
    (hc : EuclideanGraphComplete Ω u) :
    frontier {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2} = graph Ω u := by
  rw [frontier, (isClosed_epigraph_of_complete hΩ hne hu hcv hc).closure_eq,
    interior_epigraph hΩ hu.continuousOn]
  ext p
  simp only [Set.mem_sdiff, mem_ofPred_eq, graph]
  constructor
  · rintro ⟨⟨hp, hle⟩, hn⟩
    exact ⟨hp, le_antisymm (not_lt.mp (fun h => hn ⟨hp, h⟩)) hle⟩
  · rintro ⟨hp, he⟩
    refine ⟨⟨hp, he.ge⟩, ?_⟩
    rintro ⟨_, hlt⟩
    exact (ne_of_lt hlt) he.symm

theorem epigraph_interior_nonempty {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {u : Space n → ℝ} (hu : ContinuousOn u Ω) :
    (interior {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2}).Nonempty := by
  rw [interior_epigraph hΩ hu]
  obtain ⟨a, ha⟩ := hne
  exact ⟨(a, u a + 1), ha, by simp⟩

/- Compactness of the entire tangent cap, not just its projection. -/
theorem isCompact_tangent_cap {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω) (t : ℝ) :
    IsCompact {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2 ∧
      p.2 - u a - fderiv ℝ u a (p.1 - a) ≤ t} := by
  let K := {x | x ∈ Ω ∧ tangentHeight u a x ≤ t}
  have hK : IsCompact K := isCompact_tangent_sublevel hΩ hcv hu hp hc ha t
  let Φ : Space n × ℝ → Space n × ℝ :=
    fun q => (q.1, u a + fderiv ℝ u a (q.1 - a) + q.2)
  have hΦ : Continuous Φ := continuous_fst.prodMk
    ((continuous_const.add ((fderiv ℝ u a).continuous.comp
      (continuous_fst.sub continuous_const))).add continuous_snd)
  have hcpt : IsCompact (Φ '' (K ×ˢ Icc (0 : ℝ) t)) :=
    (hK.prod isCompact_Icc).image hΦ
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hclosed : IsClosed {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2 ∧
      p.2 - u a - fderiv ℝ u a (p.1 - a) ≤ t} := by
    have he := isClosed_epigraph_of_complete hΩ ⟨a, ha⟩ hu hcu hc
    have hf : Continuous (fun p : Space n × ℝ => p.2 - u a - fderiv ℝ u a (p.1 - a)) :=
      (continuous_snd.sub continuous_const).sub
        ((fderiv ℝ u a).continuous.comp (continuous_fst.sub continuous_const))
    convert he.inter (isClosed_le hf continuous_const) using 1
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  apply hcpt.of_isClosed_subset hclosed
  intro p hp'
  have hga := tangentHeight_nonneg hΩ hcv hu hp ha hp'.1
  dsimp [tangentHeight] at hga
  refine ⟨(p.1, p.2 - u a - fderiv ℝ u a (p.1 - a)), ?_, ?_⟩
  · refine ⟨⟨hp'.1, ?_⟩, ?_, hp'.2.2⟩
    · dsimp [tangentHeight]
      linarith [hp'.2.1, hp'.2.2]
    · linarith [hp'.2.1]
  · dsimp [Φ]
    congr 1
    ring

/- The manuscript's open tangent section. -/
def tangentSection {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n) (t : ℝ) : Set (Space n) :=
  {x | x ∈ Ω ∧ tangentHeight u a x < t}

/- For positive height the closed sublevel is precisely the closure of the
open tangent section. Completeness supplies closedness; convexity supplies
approximation from the section interior. -/
theorem closure_tangentSection {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω)
    {t : ℝ} (ht : 0 < t) :
    closure (tangentSection Ω u a t) = {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hcg := convexOn_tangentHeight hcu a
  apply le_antisymm
  · refine closure_minimal ?_ (isClosed_tangent_sublevel hΩ ⟨a, ha⟩ hu hcu hc a t)
    intro x hx
    exact ⟨hx.1, hx.2.le⟩
  · intro x hx
    obtain ⟨q, hqm, hqmem, hqlim⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ) < 1 by norm_num)
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun i => a + q i • (x - a), ?_, ?_⟩
    · intro i
      have hqi : q i ∈ Ioo (0 : ℝ) 1 := hqmem i
      refine ⟨hcv.add_smul_mem ha (by simpa using hx.1) ⟨hqi.1.le, hqi.2.le⟩, ?_⟩
      have hv : (1 - q i) • a + q i • x = a + q i • (x - a) := by module
      have he := hcg.2 ha hx.1 (sub_nonneg.mpr hqi.2.le) hqi.1.le
        (show (1 - q i) + q i = 1 by ring)
      rw [hv, tangentHeight_self] at he
      simp only [smul_eq_mul, mul_zero, zero_add] at he
      exact lt_of_le_of_lt (he.trans (mul_le_mul_of_nonneg_left hx.2 hqi.1.le))
        (by nlinarith [ht, hqi.2])
    · have hh := (tendsto_const_nhds (x := a)).add (hqlim.smul_const (x - a))
      simpa using hh

/- Source equation uniform-section-balance, in unshifted coordinates;
equivalently, -ρ(closure S-a) ⊆ closure S-a. -/
def SectionBalance {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) (ρ : ℝ) : Prop :=
  ∀ a ∈ Ω, ∀ t : ℝ, 0 < t → ∀ x ∈ closure (tangentSection Ω u a t),
    a - ρ • (x - a) ∈ closure (tangentSection Ω u a t)

/- A direct form of the closed-section reflection, with arbitrary finite
height (zero included). No balance conclusion is assumed about the domain. -/
theorem sectionBalance_reflection {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {ρ : ℝ} (hbal : SectionBalance Ω u ρ)
    {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) :
    a - ρ • (x - a) ∈ Ω ∧
    tangentHeight u a (a - ρ • (x - a)) ≤ tangentHeight u a x := by
  by_cases hxa : x = a
  · simp only [hxa, sub_self, smul_zero, sub_zero, le_refl, and_true]
    exact ha
  · have ht := tangentHeight_pos hΩ hcv hu hp ha hx hxa
    have he := hbal a ha _ ht x (by
      rw [closure_tangentSection hΩ hcv hu hp hc ha ht]
      exact ⟨hx, le_rfl⟩)
    rwa [closure_tangentSection hΩ hcv hu hp hc ha ht] at he

/- An open set containing a point and invariant under one dilation about it
of factor greater than one is the whole vector space. -/
theorem eq_univ_of_dilation {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {a : Space n} (ha : a ∈ Ω) {c : ℝ} (hc : 1 < c)
    (hexpand : ∀ x ∈ Ω, a + c • (x - a) ∈ Ω) : Ω = univ := by
  have hp (k : ℕ) (x : Space n) (hx : x ∈ Ω) : a + c ^ k • (x - a) ∈ Ω := by
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have he := hexpand _ ih
      simpa [pow_succ, smul_smul, mul_comm] using he
  apply eq_univ_iff_forall.mpr
  intro b
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hq : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
  have hqlt : c⁻¹ < 1 := (inv_lt_one₀ hc0).mpr hc
  have hlim : Tendsto (fun k : ℕ => a + (c⁻¹) ^ k • (b - a)) atTop (𝓝 a) := by
    have he := (tendsto_const_nhds (x := a)).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hqlt).smul_const (b - a))
    simpa using he
  obtain ⟨k, hk⟩ := (hlim.eventually_mem (hΩ.mem_nhds ha)).exists
  have he := hp k _ hk
  simpa [smul_smul, ← mul_pow, hc0.ne'] using he

/- The domain-extension conclusion of rigidity.tex:38–87. Uniform reflection
of actual tangent sections, once proved by the model argument, forces all
rays to continue. This lemma does not assume whole-domain solvability. -/
theorem eq_univ_of_sectionBalance {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {ρ : ℝ} (hρ : 0 < ρ)
    (hbal : SectionBalance Ω u ρ) : Ω = univ := by
  obtain ⟨a, ha⟩ := hne
  apply eq_univ_of_dilation hΩ ha (c := 1 + ρ) (by linarith)
  intro x hx
  have he := (sectionBalance_reflection hΩ hcv hu hp hc hbal hx ha).1
  have hv : x - ρ • (a - x) = a + (1 + ρ) • (x - a) := by module
  rwa [hv] at he

/- The exact gap-doubling constants from rigidity.tex, proved before assuming
that the base is all of Rⁿ. Thus the same calculation supplies ray extension. -/
theorem gap_doubling_of_sectionBalance {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {ρ : ℝ} (hρ : 0 < ρ)
    (hbal : SectionBalance Ω u ρ) {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) :
    a + (1 + ρ / 2) • (x - a) ∈ Ω ∧
    tangentHeight u a (a + (1 + ρ / 2) • (x - a)) ≤
      ((2 + ρ) * (1 + ρ) / ρ) * tangentHeight u a x := by
  let θ : ℝ := (2 + ρ) / (2 * (1 + ρ))
  let β : ℝ := 1 + ρ / 2
  let A : ℝ := (2 + ρ) * (1 + ρ) / ρ
  have hden : 0 < 2 * (1 + ρ) := by positivity
  have hθ : 0 < θ := div_pos (by linarith) hden
  have hθ1 : θ < 1 := (div_lt_one hden).mpr (by linarith)
  have hβ : β = (1 + ρ) * θ := by dsimp [β, θ]; field_simp
  have hA : A * (1 - θ) = β := by
    dsimp [A, θ, β]
    field_simp
    ring
  have hA0 : 0 < A := by dsimp [A]; positivity
  let v := x - a
  let y := a + θ • v
  let z := a + β • v
  have hy : y ∈ Ω := hcv.add_smul_mem ha (by simpa [v] using hx) ⟨hθ.le, hθ1.le⟩
  have hz : y - ρ • (a - y) = z := by
    dsimp [y, z]
    rw [hβ]
    module
  have hrfl := sectionBalance_reflection hΩ hcv hu hp hc hbal hy ha
  rw [hz] at hrfl
  refine ⟨hrfl.1, ?_⟩
  have hzy : z - y = (β - θ) • v := by dsimp [z, y]; module
  have hay : a - y = (-θ) • v := by dsimp [y]; module
  have hxy : x - y = (1 - θ) • v := by dsimp [y, v]; module
  have hza : z - a = β • v := by simp [z]
  have hya : y - a = θ • v := by simp [y]
  have hrefl := hrfl.2
  simp only [tangentHeight, hzy, hay, map_smul, smul_eq_mul] at hrefl
  have hsupport := tangentHeight_nonneg hΩ hcv hu hp hy hx
  simp only [tangentHeight, hxy, map_smul, smul_eq_mul] at hsupport
  have hbase := tangentHeight_nonneg hΩ hcv hu hp ha hy
  simp only [tangentHeight, hya, map_smul, smul_eq_mul] at hbase
  have hbound : (1 - θ) * (fderiv ℝ u y v - fderiv ℝ u a v) ≤ tangentHeight u a x := by
    dsimp [tangentHeight, v] at *
    nlinarith
  have hzbound : tangentHeight u a z ≤ β * (fderiv ℝ u y v - fderiv ℝ u a v) := by
    simp only [tangentHeight, hza, map_smul, smul_eq_mul]
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbound hA0.le
  rw [← mul_assoc, hA] at hmul
  exact hzbound.trans hmul

/- Convexity of the actual support gap gives its monotonicity on every ray. -/
theorem tangentHeight_ray_mono {n : ℕ} {u : Space n → ℝ}
    (hu : ConvexOn ℝ univ u) (hmin : ∀ a x, 0 ≤ tangentHeight u a x)
    (a e : Space n) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    tangentHeight u a (a + r • e) ≤ tangentHeight u a (a + s • e) := by
  by_cases hs : s = 0
  · have : r = 0 := le_antisymm (by simpa [hs] using hrs) hr
    simp [this, hs]
  have hs0 : 0 < s := lt_of_le_of_ne (hr.trans hrs) (Ne.symm hs)
  have hq : 0 ≤ r / s := div_nonneg hr hs0.le
  have hq1 : r / s ≤ 1 := (div_le_one hs0).mpr hrs
  have he := (convexOn_tangentHeight hu a).2 (mem_univ a) (mem_univ (a + s • e))
    (sub_nonneg.mpr hq1) hq (show (1 - r / s) + r / s = 1 by ring)
  have hv : (1 - r / s) • a + (r / s) • (a + s • e) = a + r • e := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ hs]
    module
  rw [hv, tangentHeight_self] at he
  simp only [smul_eq_mul, mul_zero, zero_add] at he
  exact he.trans (mul_le_of_le_one_left (hmin _ _) hq1)

/- The normalization B₁⊆{v<1}, at a zero tangent, gives v≤1/4 on B₁/₄. -/
theorem normalized_value_le_quarter {n : ℕ} {v : Space n → ℝ}
    (hv : ConvexOn ℝ univ v) (hzero : v 0 = 0) (hdzero : fderiv ℝ v 0 = 0)
    (hinner : Metric.ball 0 1 ⊆ tangentSection univ v 0 1)
    {x : Space n} (hx : ‖x‖ < 1 / 4) : v x ≤ 1 / 4 := by
  have hmem : (4 : ℝ) • x ∈ Metric.ball 0 1 := by
    rw [mem_ball_zero_iff, norm_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    linarith
  have hsmall := (hinner hmem).2
  simp only [tangentHeight, hzero, hdzero, sub_zero, zero_apply] at hsmall
  have he := hv.2 (mem_univ (0 : Space n)) (mem_univ ((4 : ℝ) • x))
    (show (0 : ℝ) ≤ 3 / 4 by norm_num) (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num)
  norm_num [smul_smul, hzero] at he
  linarith

/- Source fixed-radius-gap. The proof uses reflected closed sections directly,
rather than choosing the intersection with their radial boundary. -/
theorem fixed_radius_gap_of_sectionBalance {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hp : ∀ x, (hessian v x).PosDef)
    (hc : EuclideanGraphComplete univ v)
    (hzero : v 0 = 0) (hdzero : fderiv ℝ v 0 = 0)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R)
    (hbal : SectionBalance univ v ρ)
    (hinner : Metric.ball 0 1 ⊆ tangentSection univ v 0 1)
    (houter : tangentSection univ v 0 1 ⊆ Metric.ball 0 R)
    {x e : Space n} (hx : ‖x‖ < 1 / 4) (he : ‖e‖ = 1) :
    (1 / 4 : ℝ) ≤ tangentHeight v x (x + (2 * R / ρ) • e) := by
  have hcv := convexOn_of_hessian_posSemidef isOpen_univ (convex_univ : Convex ℝ (univ : Set (Space n)))
    hv.contDiffOn (fun z _ => (hp z).posSemidef)
  have hvx := normalized_value_le_quarter hcv hzero hdzero hinner hx
  have hout (z : Space n) (hz : R ≤ ‖z‖) : 1 ≤ v z := by
    by_contra hh
    have hmem : z ∈ tangentSection univ v 0 1 := by
      refine ⟨mem_univ _, ?_⟩
      simpa [tangentHeight, hzero, hdzero] using lt_of_not_ge hh
    have hnorm := mem_ball_zero_iff.mp (houter hmem)
    linarith
  have hb : 0 < 2 * R / ρ := by positivity
  have hbet : 2 * R ≤ 2 * R / ρ := (le_div_iff₀ hρ).mpr (by nlinarith)
  have hfar {s : ℝ} (hs : 2 * R ≤ |s|) : R ≤ ‖x + s • e‖ := by
    have hnorm := norm_add_le (x + s • e) (-x)
    have heq : x + s • e + -x = s • e := by abel
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, he, mul_one] at hnorm
    linarith
  by_cases hsgn : fderiv ℝ v x e ≤ 0
  · have hvz := hout _ (hfar (s := 2 * R / ρ) (by rwa [abs_of_pos hb]))
    simp only [tangentHeight, add_sub_cancel_left, map_smul, smul_eq_mul]
    have hneg := mul_nonpos_of_nonneg_of_nonpos hb.le hsgn
    linarith
  · have hvz := hout (x - (2 * R) • e) (by
      simpa only [neg_smul, sub_eq_add_neg] using
        hfar (s := -(2 * R)) (by rw [abs_neg, abs_of_pos (by positivity)]))
    have href := (sectionBalance_reflection isOpen_univ (convex_univ : Convex ℝ (univ : Set (Space n)))
      hv.contDiffOn (fun z _ => hp z) hc hbal (mem_univ x)
      (mem_univ (x + (2 * R / ρ) • e))).2
    have hreflect : x - ρ • (x + (2 * R / ρ) • e - x) = x - (2 * R) • e := by
      rw [add_sub_cancel_left, smul_smul, mul_div_cancel₀ _ hρ.ne']
    rw [hreflect] at href
    have hdisp : x - (2 * R) • e - x = -(2 * R) • e := by module
    simp only [tangentHeight, hdisp, map_smul, smul_eq_mul] at href
    have hprod : 0 ≤ (2 * R) * fderiv ℝ v x e := mul_nonneg (by positivity) (le_of_not_ge hsgn)
    unfold tangentHeight
    linarith

/- Exact integer in rigidity.tex: N(r)=max(0,ceil(log_beta(R*/r))).
The natural-number ceiling incorporates max with zero. -/
def modulusIterates (ρ R r : ℝ) : ℕ :=
  ⌈Real.logb (1 + ρ / 2) ((2 * R / ρ) / r)⌉₊

/- Exact lower modulus b(r)=1/(8 A^N(r)) from the manuscript. -/
def normalizedModulus (ρ R r : ℝ) : ℝ :=
  1 / (8 * (((2 + ρ) * (1 + ρ) / ρ) ^ modulusIterates ρ R r))

theorem normalizedModulus_pos {ρ R r : ℝ} (hρ : 0 < ρ) :
    0 < normalizedModulus ρ R r := by
  unfold normalizedModulus
  positivity

theorem modulusIterates_spec {ρ R r : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hr : 0 < r) :
    2 * R / ρ ≤ (1 + ρ / 2) ^ modulusIterates ρ R r * r := by
  have hb : 1 < 1 + ρ / 2 := by linarith
  have hb0 : 0 < 1 + ρ / 2 := zero_lt_one.trans hb
  have ht : 0 < (2 * R / ρ) / r := by positivity
  have he := Real.rpow_le_rpow_of_exponent_le hb.le
    (Nat.le_ceil (Real.logb (1 + ρ / 2) ((2 * R / ρ) / r)))
  rw [Real.rpow_logb hb0 (ne_of_gt hb) ht, Real.rpow_natCast] at he
  exact (div_le_iff₀ hr).mp he

/- Iterate the source's doubling inequality for the actual gap at a point. -/
theorem gap_doubling_iterate {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete univ u) {ρ : ℝ} (hρ : 0 < ρ)
    (hbal : SectionBalance univ u ρ) (a x : Space n) (k : ℕ) :
    tangentHeight u a (a + (1 + ρ / 2) ^ k • (x - a)) ≤
      ((2 + ρ) * (1 + ρ) / ρ) ^ k * tangentHeight u a x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he := (gap_doubling_of_sectionBalance isOpen_univ
      (convex_univ : Convex ℝ (univ : Set (Space n))) hu.contDiffOn
      (fun z _ => hp z) hc hρ hbal (mem_univ a)
      (mem_univ (a + (1 + ρ / 2) ^ k • (x - a)))).2
    simp only [add_sub_cancel_left, smul_smul] at he
    have hA : 0 ≤ (2 + ρ) * (1 + ρ) / ρ := by positivity
    calc
      _ ≤ ((2 + ρ) * (1 + ρ) / ρ) *
          tangentHeight u a (a + (1 + ρ / 2) ^ k • (x - a)) := by
        simpa only [pow_succ, mul_comm] using he
      _ ≤ ((2 + ρ) * (1 + ρ) / ρ) *
          (((2 + ρ) * (1 + ρ) / ρ) ^ k * tangentHeight u a x) :=
        mul_le_mul_of_nonneg_left ih hA
      _ = _ := by rw [pow_succ]; ring

/- Uniform normalized modulus, rigidity.tex:118–175. Every quantifier is
uniform in the normalized function, point and direction; only rho and R occur
in the explicit modulus. The section balance producer remains separate. -/
theorem normalized_modulus_of_sectionBalance {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hp : ∀ x, (hessian v x).PosDef)
    (hc : EuclideanGraphComplete univ v)
    (hzero : v 0 = 0) (hdzero : fderiv ℝ v 0 = 0)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R)
    (hbal : SectionBalance univ v ρ)
    (hinner : Metric.ball 0 1 ⊆ tangentSection univ v 0 1)
    (houter : tangentSection univ v 0 1 ⊆ Metric.ball 0 R)
    {x : Space n} (hx : x ∈ Metric.ball 0 (1 / 4)) {r : ℝ} (hr : 0 < r) :
    tangentSection univ v x (normalizedModulus ρ R r) ⊆ Metric.ball x r := by
  have hcv := convexOn_of_hessian_posSemidef isOpen_univ
    (convex_univ : Convex ℝ (univ : Set (Space n))) hv.contDiffOn (fun z _ => (hp z).posSemidef)
  have hmin (a z : Space n) : 0 ≤ tangentHeight v a z := tangentHeight_nonneg
    isOpen_univ (convex_univ : Convex ℝ (univ : Set (Space n))) hv.contDiffOn
    (fun z _ => hp z) (mem_univ _) (mem_univ _)
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm]
  by_contra hh
  have hdist : r ≤ ‖z - x‖ := le_of_not_gt hh
  have hd : 0 < ‖z - x‖ := hr.trans_le hdist
  let e : Space n := ‖z - x‖⁻¹ • (z - x)
  have he : ‖e‖ = 1 := by simp [e, norm_smul, hd.ne']
  have hzrep : x + ‖z - x‖ • e = z := by simp [e, smul_smul, hd.ne']
  let N := modulusIterates ρ R r
  let β : ℝ := 1 + ρ / 2
  let A : ℝ := (2 + ρ) * (1 + ρ) / ρ
  have hA : 0 < A := by dsimp [A]; positivity
  have hrad := modulusIterates_spec hρ (zero_lt_one.trans_le hR) hr
  have hfixed := fixed_radius_gap_of_sectionBalance hv hp hc hzero hdzero hρ hρ1 hR
    hbal hinner houter (mem_ball_zero_iff.mp hx) he
  have hmono := tangentHeight_ray_mono hcv hmin x e (by positivity : 0 ≤ 2 * R / ρ) hrad
  have hdouble := gap_doubling_iterate hv hp hc hρ hbal x (x + r • e) N
  simp only [add_sub_cancel_left, smul_smul] at hdouble
  have hsmall : tangentHeight v x (x + r • e) ≤ tangentHeight v x z := by
    have heq := tangentHeight_ray_mono hcv hmin x e hr.le hdist
    rwa [hzrep] at heq
  have hbound : (1 / 4 : ℝ) ≤ A ^ N * tangentHeight v x z :=
    (hfixed.trans hmono).trans (hdouble.trans (mul_le_mul_of_nonneg_left hsmall (pow_nonneg hA.le _)))
  have hscale : 0 < 8 * A ^ N := by positivity
  have hgap := hz.2
  change tangentHeight v x z < 1 / (8 * A ^ N) at hgap
  have hgap' := (lt_div_iff₀ hscale).mp hgap
  nlinarith

/- The manuscript's epigraph; the domain is not silently replaced by all of space. -/
/- Literal tangent affine coordinates, ordered as one base direction and n
transverse directions. -/
def tangentModelEquiv {n : ℕ} (u : Space n → ℝ) (a : Space n) :
    (Space n × ℝ) ≃ᴬ[ℝ] (Space 1 × Space n) := by
  letI : ContinuousSMul ℝ (Space 1 × Space n) := Prod.continuousSMul
  let L : (Space n × ℝ) ≃L[ℝ] (Space 1 × Space n) := LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => (WithLp.toLp 2 (fun _ => p.2 - fderiv ℝ u a p.1), p.1)
      invFun := fun q => (q.2, q.1 0 + fderiv ℝ u a q.2)
      left_inv := by intro p; dsimp; ext <;> simp
      right_inv := by
        intro q
        apply Prod.ext
        · ext i
          simp [Subsingleton.elim i (0 : Fin 1)]
        · rfl
      map_add' := by
        intro p q
        ext i <;> simp [map_add]
        ring
      map_smul' := by intro r p; ext i <;> simp [map_smul, mul_sub] }
  exact (ContinuousAffineEquiv.constVAdd ℝ (Space n × ℝ) (-(a,u a))).trans L.toContinuousAffineEquiv

@[simp] theorem tangentModelEquiv_apply {n : ℕ} (u : Space n → ℝ) (a x : Space n) (z : ℝ) :
    tangentModelEquiv u a (x,z) =
      (WithLp.toLp 2 (fun _ : Fin 1 => z-u a-fderiv ℝ u a (x-a)), x-a) := by
  change (WithLp.toLp 2 (fun _ : Fin 1 => (-u a+z)-fderiv ℝ u a (-a+x)), -a+x) = _
  simp only [neg_add_eq_sub]

@[simp] theorem tangentModelEquiv_fst {n : ℕ} (u : Space n → ℝ) (a : Space n)
    (p : Space n × ℝ) (i : Fin 1) :
    (tangentModelEquiv u a p).1 i = p.2-u a-fderiv ℝ u a (p.1-a) := by
  cases p
  simp only [tangentModelEquiv_apply]

@[simp] theorem tangentModelEquiv_snd {n : ℕ} (u : Space n → ℝ) (a : Space n)
    (p : Space n × ℝ) : (tangentModelEquiv u a p).2 = p.1-a := by
  cases p
  simp only [tangentModelEquiv_apply]

/- Completeness supplies an actual one-direction model in the affine family. -/
theorem tangent_epigraph_isModelShape {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω) :
    IsModelShape (tangentModelEquiv u a '' sourceEpigraph Ω u) := by
  have hv := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hcl := isClosed_epigraph_of_complete hΩ ⟨a,ha⟩ hu hv hc
  have hi := epigraph_interior_nonempty hΩ ⟨a,ha⟩ hu.continuousOn
  let A := tangentModelEquiv u a
  refine ⟨A.toHomeomorph.isClosedMap _ hcl, hv.convex_epigraph.affine_image A.toAffineEquiv.toAffineMap,
    ?_, ?_, ?_, ?_⟩
  · change (interior (A.toHomeomorph '' sourceEpigraph Ω u)).Nonempty
    rw [← A.toHomeomorph.image_interior]
    exact hi.image A.toHomeomorph
  · intro s hs
    refine ⟨(a,u a+s 0),⟨ha,by linarith [hs 0]⟩,?_⟩
    apply Prod.ext
    · ext i
      simp [tangentModelEquiv_apply,Subsingleton.elim i (0 : Fin 1)]
    · simp [tangentModelEquiv_apply]
  · rintro p ⟨⟨x,z⟩,⟨hx,hz⟩,rfl⟩ i
    rw [tangentModelEquiv_fst]
    have hh := tangentHeight_nonneg hΩ hcv hu hp ha hx
    dsimp [tangentHeight] at hh
    linarith
  · intro T hT
    convert (isCompact_tangent_cap hΩ hcv hu hp hc ha T).image A.continuous using 1
    ext p
    constructor
    · rintro ⟨⟨q,hq,rfl⟩,hTq⟩
      refine ⟨q,⟨hq.1,hq.2,?_⟩,rfl⟩
      simpa [A,tangentModelEquiv_apply] using hTq
    · rintro ⟨q,⟨hq,hz,hTq⟩,rfl⟩
      exact ⟨⟨q,⟨hq,hz⟩,rfl⟩,by simpa [A,tangentModelEquiv_apply] using hTq⟩

theorem tangent_epigraph_in_family {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω) :
    InAffineLimitFamily (sourceEpigraph Ω u) (tangentModelEquiv u a '' sourceEpigraph Ω u) := by
  have hv := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  exact InAffineLimitFamily.of_affine_image
    (isClosed_epigraph_of_complete hΩ ⟨a,ha⟩ hu hv hc) hv.convex_epigraph
    (epigraph_interior_nonempty hΩ ⟨a,ha⟩ hu.continuousOn) (tangentModelEquiv u a)

@[simp] theorem tangent_model_fiber {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n) (t : ℝ) :
    modelFiber (tangentModelEquiv u a '' sourceEpigraph Ω u)
      (WithLp.toLp 2 (fun _ : Fin 1 => t)) =
      (fun x => x-a) '' {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  ext y
  constructor
  · rintro ⟨⟨x,z⟩,⟨hx,hz⟩,he⟩
    have he1 := congrArg (fun q : Space 1 × Space n => q.1 0) he
    have he2 := congrArg Prod.snd he
    simp only [tangentModelEquiv_fst] at he1
    simp only [tangentModelEquiv_snd] at he2
    refine ⟨x,⟨hx,?_⟩,he2⟩
    change z-u a-fderiv ℝ u a (x-a) = t at he1
    dsimp [tangentHeight]
    linarith
  · rintro ⟨x,⟨hx,hxt⟩,rfl⟩
    refine ⟨(x,t+u a+fderiv ℝ u a (x-a)),⟨hx,?_⟩,?_⟩
    · dsimp [tangentHeight] at hxt
      linarith
    · ext i <;> simp [tangentModelEquiv_apply]
      ring

/- A model's direction number is bounded by the actual ambient dimension,
using an invertible affine map from its approximating sequence. -/
theorem model_dimension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {D : Set E} {k m : ℕ} {C : Set (Space k × Space m)}
    (hf : InAffineLimitFamily D C) : k+m = Module.finrank ℝ E := by
  obtain ⟨A,hA⟩ := hf.approximation
  have hh := (A 0).toAffineEquiv.linear.finrank_eq
  simpa [Module.finrank_prod,finrank_euclideanSpace] using hh.symm

/- A maximal direction number exists; this is genuine finite-dimensional
maximality rather than a postulated geometric estimate. -/
theorem exists_maximal_model {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {D : Set E}
    (h1 : ∃ m, ∃ C : Set (Space 1 × Space m), IsModelShape C ∧ InAffineLimitFamily D C) :
    ∃ (k m : ℕ) (C : Set (Space k × Space m)), 1 ≤ k ∧ IsModelShape C ∧
      InAffineLimitFamily D C ∧ ∀ (r d : ℕ) (C' : Set (Space r × Space d)),
      IsModelShape C' → InAffineLimitFamily D C' → r ≤ k := by
  classical
  let S : Set ℕ := {r | ∃ m, ∃ C : Set (Space r × Space m), IsModelShape C ∧ InAffineLimitFamily D C}
  have hbd : BddAbove S := ⟨Module.finrank ℝ E, by
    rintro r ⟨m,C,hC,hf⟩
    have hh := model_dimension hf
    omega⟩
  have hne : S.Nonempty := ⟨1,h1⟩
  let k := sSup S
  have hs : S.Finite := (Set.finite_Iic hbd.choose).subset hbd.choose_spec
  have hk : k ∈ S := hne.csSup_mem hs
  have hmax : ∀ {r}, r ∈ S → r ≤ k := fun hr => le_csSup hbd hr
  obtain ⟨m,C,hC,hf⟩ := hk
  exact ⟨k,m,C,hmax h1,hC,hf,fun r d C' hC' hf' => hmax ⟨d,C',hC',hf'⟩⟩

/- Once the geometric/analytic exclusion of two-direction models is proved,
all tangent sections (all centers and heights) inherit one common balance.
This is a faithful integration lemma, not the main theorem. -/
theorem sectionBalance_of_no_two_model {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u)
    (hno : ∀ (d : ℕ), n = d+1 → ∀ C : Set (Space 2 × Space d),
      IsModelShape C → InAffineLimitFamily (sourceEpigraph Ω u) C → False) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ SectionBalance Ω u ρ := by
  have hv := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hcl := isClosed_epigraph_of_complete hΩ hne hu hv hc
  have hneD : (sourceEpigraph Ω u).Nonempty := by obtain ⟨a,ha⟩ := hne; exact ⟨(a,u a),ha,le_rfl⟩
  obtain ⟨a,ha,hcenter⟩ := uniform_centering hcl hneD hno
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  refine ⟨a⁻¹,inv_pos.mpr hapos,(inv_le_one₀ hapos).mpr ha,?_⟩
  intro x hx t ht y hy
  rw [closure_tangentSection hΩ hcv hu hp hc hx ht] at hy ⊢
  have hmod := tangent_epigraph_isModelShape hΩ hcv hu hp hc hx
  have hf := tangent_epigraph_in_family hΩ hcv hu hp hc hx
  have hh := hcenter _ hmod hf (WithLp.toLp 2 (fun _ : Fin 1 => t)) (by simpa using ht)
  rw [tangent_model_fiber] at hh
  have hm : -(y-x) ∈ -((fun z => z-x) '' {z | z ∈ Ω ∧ tangentHeight u x z ≤ t}) := by
    exact neg_mem_neg.mpr ⟨y,hy,rfl⟩
  obtain ⟨z,⟨w,hw,rfl⟩,hz⟩ := mem_smul_set.mp (hh hm)
  have he : x-a⁻¹ • (y-x) = w := by
    have hz' := congrArg (fun v : Space n => a⁻¹ • v) hz
    simp only [smul_smul, inv_mul_cancel₀ hapos.ne', one_smul, smul_neg] at hz'
    rw [sub_eq_iff_eq_add] at hz'
    simpa only [sub_eq_add_neg, add_comm] using hz'.symm
  simpa only [he] using hw

-- END

end AffineBernstein

end

end OAI
