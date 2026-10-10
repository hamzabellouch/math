import OAI.Analysis.SphereIsometry.SimplexFixedPoint
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Finite-net approximate fixed points on a compact convex set

The coefficient map is the explicit normalization of the weights
`max (δ - dist (P i) y) 0`.  The simplex fixed point is applied to this
actual map composed with the actual barycenter and the given self-map.
-/

noncomputable section

namespace Tingley

open Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def compactNetWeight (P : ι → E) (δ : ℝ) (y : E) (i : ι) : ℝ :=
  max (δ - dist (P i) y) 0

def compactNetTotal (P : ι → E) (δ : ℝ) (y : E) : ℝ :=
  ∑ i, compactNetWeight P δ y i

def compactNetCoefficients (P : ι → E) (δ : ℝ) (y : E) (i : ι) : ℝ :=
  compactNetWeight P δ y i / compactNetTotal P δ y

omit [NormedSpace ℝ E] [Fintype ι] in
theorem compactNetWeight_nonneg (P : ι → E) (δ : ℝ) (y : E) (i : ι) :
    0 ≤ compactNetWeight P δ y i := le_max_right _ _

omit [NormedSpace ℝ E] [Fintype ι] in
theorem compactNetWeight_pos {P : ι → E} {δ : ℝ} {y : E} {i : ι}
    (hi : dist (P i) y < δ) : 0 < compactNetWeight P δ y i :=
  (sub_pos.mpr hi).trans_le (le_max_left _ _)

omit [NormedSpace ℝ E] in
theorem compactNetTotal_pos {P : ι → E} {δ : ℝ} {y : E}
    (hnet : ∃ i, dist (P i) y < δ) : 0 < compactNetTotal P δ y := by
  obtain ⟨i, hi⟩ := hnet
  apply Finset.sum_pos'
  · intro j _hj
    exact compactNetWeight_nonneg P δ y j
  · exact ⟨i, Finset.mem_univ i, compactNetWeight_pos hi⟩

omit [NormedSpace ℝ E] in
theorem compactNetCoefficients_nonneg {P : ι → E} {δ : ℝ} {y : E}
    (hnet : ∃ i, dist (P i) y < δ) (i : ι) :
    0 ≤ compactNetCoefficients P δ y i :=
  div_nonneg (compactNetWeight_nonneg P δ y i) (compactNetTotal_pos hnet).le

omit [NormedSpace ℝ E] in
theorem compactNetCoefficients_sum {P : ι → E} {δ : ℝ} {y : E}
    (hnet : ∃ i, dist (P i) y < δ) :
    ∑ i, compactNetCoefficients P δ y i = 1 := by
  unfold compactNetCoefficients
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (compactNetTotal_pos hnet).ne'

omit [NormedSpace ℝ E] in
theorem compactNetCoefficients_pos {P : ι → E} {δ : ℝ} {y : E} {i : ι}
    (hnet : ∃ j, dist (P j) y < δ) (hi : dist (P i) y < δ) :
    0 < compactNetCoefficients P δ y i :=
  div_pos (compactNetWeight_pos hi) (compactNetTotal_pos hnet)

omit [NormedSpace ℝ E] in
theorem compactNetCoefficients_active {P : ι → E} {δ : ℝ} {y : E} {i : ι}
    (hi : 0 < compactNetCoefficients P δ y i) : dist (P i) y < δ := by
  by_contra h
  have hw : compactNetWeight P δ y i = 0 :=
    max_eq_right (sub_nonpos.mpr (le_of_not_gt h))
  simp only [compactNetCoefficients, hw, zero_div] at hi
  exact (lt_irrefl 0) hi

def compactNetCoefficientMap (P : ι → E) (δ : ℝ) {K : Set E}
    (hnet : ∀ y ∈ K, ∃ i, dist (P i) y < δ) : K → ProbabilitySimplex ι :=
  fun y => ⟨compactNetCoefficients P δ (y : E),
    compactNetCoefficients_nonneg (hnet y y.property),
    compactNetCoefficients_sum (hnet y y.property)⟩

omit [NormedSpace ℝ E] in
theorem continuous_compactNetCoefficientMap (P : ι → E) (δ : ℝ) {K : Set E}
    (hnet : ∀ y ∈ K, ∃ i, dist (P i) y < δ) :
    Continuous (compactNetCoefficientMap P δ hnet) := by
  have hw (i : ι) : Continuous (fun y : K => compactNetWeight P δ (y : E) i) :=
    (continuous_const.sub (continuous_const.dist continuous_subtype_val)).max continuous_const
  have hD : Continuous (fun y : K => compactNetTotal P δ (y : E)) :=
    continuous_finsetSum Finset.univ (fun i _hi => hw i)
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (hw i).div₀ hD (fun y => (compactNetTotal_pos (hnet y y.property)).ne')

def compactNetBarycenter (P : ι → E) (a : ProbabilitySimplex ι) : E :=
  ∑ i, (a : ι → ℝ) i • P i

theorem compactNetBarycenter_mem {K : Set E} (hconv : Convex ℝ K)
    {P : ι → E} (hP : ∀ i, P i ∈ K) (a : ProbabilitySimplex ι) :
    compactNetBarycenter P a ∈ K :=
  hconv.sum_mem (fun i _hi => a.property.1 i) a.property.2 (fun i _hi => hP i)

theorem continuous_compactNetBarycenter (P : ι → E) :
    Continuous (compactNetBarycenter P) := by
  apply continuous_finsetSum Finset.univ
  intro i _hi
  exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const

/-- The normalized finite-net average is strictly less than the net radius
away from its argument. Zero weights are allowed. -/
theorem compactNet_sum_sub_lt {P : ι → E} {δ : ℝ} {y : E}
    (hnet : ∃ i, dist (P i) y < δ) :
    ‖(∑ i, compactNetCoefficients P δ y i • P i) - y‖ < δ := by
  have hs := compactNetCoefficients_sum hnet
  have hn := compactNetCoefficients_nonneg hnet
  have heq : (∑ i, compactNetCoefficients P δ y i • P i) - y =
      ∑ i, compactNetCoefficients P δ y i • (P i - y) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs, one_smul]
  have hle (i : ι) : compactNetCoefficients P δ y i * dist (P i) y ≤
      compactNetCoefficients P δ y i * δ := by
    by_cases hi : compactNetCoefficients P δ y i = 0
    · simp only [hi, zero_mul, le_refl]
    · have hip : 0 < compactNetCoefficients P δ y i :=
        lt_of_le_of_ne (hn i) (Ne.symm hi)
      exact (mul_lt_mul_of_pos_left (compactNetCoefficients_active hip) hip).le
  obtain ⟨i, hi⟩ := hnet
  have his : compactNetCoefficients P δ y i * dist (P i) y <
      compactNetCoefficients P δ y i * δ :=
    mul_lt_mul_of_pos_left hi (compactNetCoefficients_pos ⟨i, hi⟩ hi)
  calc
    ‖(∑ j, compactNetCoefficients P δ y j • P j) - y‖ =
        ‖∑ j, compactNetCoefficients P δ y j • (P j - y)‖ := congrArg norm heq
    _ ≤ ∑ j, ‖compactNetCoefficients P δ y j • (P j - y)‖ := norm_sum_le _ _
    _ = ∑ j, compactNetCoefficients P δ y j * dist (P j) y := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hn j), dist_eq_norm]
    _ < ∑ j, compactNetCoefficients P δ y j * δ :=
      Finset.sum_lt_sum (fun j _hj => hle j) ⟨i, Finset.mem_univ i, his⟩
    _ = δ := by rw [← Finset.sum_mul, hs, one_mul]

/-- The simplex theorem, applied to the actual normalized net weights,
produces approximate fixed points for any compact convex self-map. -/
theorem exists_approximate_fixedPoint_of_isCompact_convex
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    {g : E → E} (hg : ContinuousOn g K) (hmap : MapsTo g K K)
    {δ : ℝ} (hδ : 0 < δ) : ∃ x ∈ K, ‖x - g x‖ < δ := by
  classical
  obtain ⟨S, hSK, hSfinite, hcover⟩ := hK.finite_cover_balls hδ
  let : Fintype S := hSfinite.fintype
  let P : S → E := Subtype.val
  have hnet : ∀ y ∈ K, ∃ i : S, dist (P i) y < δ := by
    intro y hy
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hcover hy)
    obtain ⟨hpS, hpy⟩ := Set.mem_iUnion.mp hp
    exact ⟨⟨p, hpS⟩, Metric.mem_ball'.mp hpy⟩
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨i₀, _hi₀⟩ := hnet y₀ hy₀
  let : Nonempty S := ⟨i₀⟩
  have hP : ∀ i, P i ∈ K := fun i => hSK i.property
  let bary : ProbabilitySimplex S → K :=
    fun a => ⟨compactNetBarycenter P a, compactNetBarycenter_mem hconv hP a⟩
  have hbary : Continuous bary := (continuous_compactNetBarycenter P).subtype_mk _
  let gK : K → K := hmap.restrict g K K
  have hgK : Continuous gK := hg.mapsToRestrict hmap
  let Q : ProbabilitySimplex S → ProbabilitySimplex S :=
    compactNetCoefficientMap P δ hnet ∘ gK ∘ bary
  have hQ : Continuous Q :=
    (continuous_compactNetCoefficientMap P δ hnet).comp (hgK.comp hbary)
  obtain ⟨a, ha⟩ := continuous_probabilitySimplex_fixedPoint Q hQ
  have hcoeff : (a : S → ℝ) = compactNetCoefficients P δ (g (bary a : E)) := by
    have hh := congrArg (fun z : ProbabilitySimplex S => (z : S → ℝ)) ha
    change compactNetCoefficients P δ (g (bary a : E)) = (a : S → ℝ) at hh
    exact hh.symm
  refine ⟨(bary a : E), (bary a).property, ?_⟩
  have happ := compactNet_sum_sub_lt (hnet (g (bary a : E)) (hmap (bary a).property))
  rw [← hcoeff] at happ
  exact happ

end Tingley

end

end OAI
