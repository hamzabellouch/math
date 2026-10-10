import OAI.Analysis.Brenier.Basic

namespace OAI

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace Problem358

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The convex conjugate with the source variable restricted to `K`. -/
def restrictedConjugate (K : Set V) (u : V → ℝ) (y : V) : ℝ :=
  sSup ((fun x => inner ℝ x y - u x) '' K)

lemma restrictedConjugate_eq_of_isMaxOn
    {K : Set V} {u : V → ℝ} {x y : V} (hx : x ∈ K)
    (hmax : IsMaxOn (fun z => inner ℝ z y - u z) K x) :
    restrictedConjugate K u y = inner ℝ x y - u x := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, hx, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hmax hz

lemma restrictedConjugate_attained
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (hu : ContinuousOn u K) (y : V) :
    ∃ x ∈ K, restrictedConjugate K u y = inner ℝ x y - u x := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne
    ((continuous_id.inner continuous_const).continuousOn.sub hu :
      ContinuousOn (fun x => inner ℝ x y - u x) K)
  exact ⟨x, hx, restrictedConjugate_eq_of_isMaxOn hx hmax⟩

lemma restrictedConjugate_fenchel
    {K : Set V} {u : V → ℝ} (hK : IsCompact K)
    (hu : ContinuousOn u K) {x : V} (hx : x ∈ K) (y : V) :
    inner ℝ x y ≤ u x + restrictedConjugate K u y := by
  have hbound := hK.bddAbove_image
    ((continuous_id.inner continuous_const).continuousOn.sub hu :
      ContinuousOn (fun x => inner ℝ x y - u x) K)
  have hle : inner ℝ x y - u x ≤ restrictedConjugate K u y :=
    le_csSup hbound ⟨x, hx, rfl⟩
  linarith

/-- Fenchel equality is exactly the supporting-slope inequality on the source set. -/
lemma restrictedConjugate_eq_iff_support
    {K : Set V} {u : V → ℝ} (hK : IsCompact K)
    (hu : ContinuousOn u K) {x y : V} (hx : x ∈ K) :
    inner ℝ x y = u x + restrictedConjugate K u y ↔
      ∀ z ∈ K, u x + inner ℝ (z - x) y ≤ u z := by
  constructor
  · intro heq z hz
    have hle := restrictedConjugate_fenchel hK hu hz y
    rw [inner_sub_left] at *
    linarith
  · intro hs
    have hmax : IsMaxOn (fun z => inner ℝ z y - u z) K x := by
      intro z hz
      change inner ℝ z y - u z ≤ inner ℝ x y - u x
      have h := hs z hz
      rw [inner_sub_left] at h
      linarith
    rw [restrictedConjugate_eq_of_isMaxOn hx hmax]
    ring

lemma restrictedConjugate_sub_le
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (hu : ContinuousOn u K) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (y z : V) :
    restrictedConjugate K u y - restrictedConjugate K u z ≤ R * ‖y - z‖ := by
  obtain ⟨x, hx, heq⟩ := restrictedConjugate_attained hK hne hu y
  have hfen := restrictedConjugate_fenchel hK hu hx z
  have hinner := real_inner_le_norm x (y - z)
  have hmul := mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg (y - z))
  rw [inner_sub_right] at hinner
  rw [heq]
  linarith

lemma restrictedConjugate_lipschitz
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (hu : ContinuousOn u K) {R : ℝ≥0} (hR : ∀ x ∈ K, ‖x‖ ≤ R) :
    LipschitzWith R (restrictedConjugate K u) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := restrictedConjugate_sub_le hK hne hu hR z y
    rw [norm_sub_rev] at h
    linarith
  · exact restrictedConjugate_sub_le hK hne hu hR y z

lemma restrictedConjugate_continuous
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (hu : ContinuousOn u K) : Continuous (restrictedConjugate K u) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨x, hx⟩ := hne
  have hR0 : 0 ≤ R := (norm_nonneg x).trans (hR x hx)
  exact (restrictedConjugate_lipschitz hK ⟨x, hx⟩ hu (R := ⟨R, hR0⟩) hR).continuous

/-- Restricting the source variable does not prevent convexity in the dual variable. -/
lemma restrictedConjugate_convex
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (hu : ContinuousOn u K) : ConvexOn ℝ Set.univ (restrictedConjugate K u) := by
  refine ⟨convex_univ, ?_⟩
  intro y _ z _ a b ha hb hab
  obtain ⟨x, hx, heq⟩ := restrictedConjugate_attained hK hne hu (a • y + b • z)
  have hy := restrictedConjugate_fenchel hK hu hx y
  have hz := restrictedConjugate_fenchel hK hu hx z
  have hy' : inner ℝ x y - u x ≤ restrictedConjugate K u y := by linarith
  have hz' : inner ℝ x z - u x ≤ restrictedConjugate K u z := by linarith
  have hm := add_le_add (mul_le_mul_of_nonneg_left hy' ha)
    (mul_le_mul_of_nonneg_left hz' hb)
  rw [heq, inner_add_right, inner_smul_right, inner_smul_right]
  simp only [smul_eq_mul]
  have habu : (a + b) * u x = u x := by rw [hab, one_mul]
  nlinarith

/-- A supporting slope at an interior differentiability point is the derivative. -/
lemma restrictedConjugate_supporting_slope_eq_fderiv
    {K : Set V} {u : V → ℝ} {x y : V} {u' : V →L[ℝ] ℝ}
    (hx : x ∈ interior K) (hu : HasFDerivAt u u' x)
    (hs : ∀ z ∈ K, u x + inner ℝ (z - x) y ≤ u z) :
    u' = innerSL ℝ y := by
  have hmin : IsMinOn (fun z => u z - inner ℝ y z) K x := by
    intro z hz
    change u x - inner ℝ y x ≤ u z - inner ℝ y z
    have h := hs z hz
    rw [inner_sub_left] at h
    have hxy := real_inner_comm x y
    have hzy := real_inner_comm z y
    linarith
  have hzero := (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hx)).hasFDerivAt_eq_zero
    (hu.sub (innerSL ℝ y).hasFDerivAt)
  exact sub_eq_zero.mp hzero

lemma restrictedConjugate_supporting_slope_unique
    {K : Set V} {u : V → ℝ} {x y z : V}
    (hx : x ∈ interior K) (hu : DifferentiableAt ℝ u x)
    (hy : ∀ w ∈ K, u x + inner ℝ (w - x) y ≤ u w)
    (hz : ∀ w ∈ K, u x + inner ℝ (w - x) z ≤ u w) : y = z := by
  apply (innerSL_inj (𝕜 := ℝ)).mp
  exact (restrictedConjugate_supporting_slope_eq_fderiv hx hu.hasFDerivAt hy).symm.trans
    (restrictedConjugate_supporting_slope_eq_fderiv hx hu.hasFDerivAt hz)

/-- Supporting inequalities survive simultaneous pointwise potential and slope limits. -/
lemma supporting_slope_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {K : Set V} {u : V → ℝ} {un : ι → V → ℝ} {pn : ι → V} {x p : V}
    (hux : Tendsto (fun n => un n x) l (𝓝 (u x)))
    (hu : ∀ z ∈ K, Tendsto (fun n => un n z) l (𝓝 (u z)))
    (hp : Tendsto pn l (𝓝 p))
    (hs : ∀ᶠ n in l, ∀ z ∈ K, un n x + inner ℝ (z - x) (pn n) ≤ un n z) :
    ∀ z ∈ K, u x + inner ℝ (z - x) p ≤ u z := by
  intro z hz
  exact le_of_tendsto_of_tendsto (hux.add (tendsto_const_nhds.inner hp)) (hu z hz)
    (hs.mono fun n hn => hn z hz)

/-- Continuous quadratic-cost dual potentials obtained from the restricted conjugate. -/
lemma restrictedConjugate_quadratic_dual_le
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hu : ContinuousOn u K)
    {x : V} (hx : x ∈ K) (y : V) :
    (‖x‖ ^ 2 - 2 * u x) + (‖y‖ ^ 2 - 2 * restrictedConjugate K u y) ≤
      ‖x - y‖ ^ 2 := by
  rw [norm_sub_sq_real]
  have h := restrictedConjugate_fenchel hK hu hx y
  linarith

lemma restrictedConjugate_quadratic_dual_eq_iff
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hu : ContinuousOn u K)
    {x y : V} (hx : x ∈ K) :
    (‖x‖ ^ 2 - 2 * u x) + (‖y‖ ^ 2 - 2 * restrictedConjugate K u y) =
      ‖x - y‖ ^ 2 ↔ ∀ z ∈ K, u x + inner ℝ (z - x) y ≤ u z := by
  rw [← restrictedConjugate_eq_iff_support hK hu hx, norm_sub_sq_real]
  constructor <;> intro h <;> linarith

end Problem358

end

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Problem358

/-- A convex source gives full measure to its interior. -/
theorem ae_mem_interior_uniformMeasure {d : ℕ} {K : Set (E d)}
    (hK : Convex ℝ K) (hKm : MeasurableSet K) :
    ∀ᵐ x ∂uniformMeasure K, x ∈ interior K := by
  apply Measure.ae_smul_measure
  have hEq : interior K =ᵐ[volume] K :=
    interior_ae_eq_of_null_frontier (hK.addHaar_frontier volume)
  filter_upwards [ae_restrict_of_ae hEq, ae_restrict_mem hKm] with x hx hmem
  exact hx.mpr hmem

/-- Rademacher's theorem on a convex source, upgraded from within-derivatives
using the nullity of the boundary of a convex set. No regular boundary is needed. -/
theorem ae_differentiableAt_uniformMeasure {d : ℕ} {K : Set (E d)}
    {u : E d → ℝ} {L : ℝ≥0}
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hu : LipschitzOnWith L u K) :
    ∀ᵐ x ∂uniformMeasure K, x ∈ interior K ∧ DifferentiableAt ℝ u x := by
  have hd : ∀ᵐ x ∂volume.restrict K, DifferentiableWithinAt ℝ u K x :=
    hu.ae_differentiableWithinAt hKm
  have hd' : ∀ᵐ x ∂uniformMeasure K, DifferentiableWithinAt ℝ u K x :=
    Measure.ae_smul_measure hd _
  filter_upwards [ae_mem_interior_uniformMeasure hK hKm, hd'] with x hx hdx
  exact ⟨hx, hdx.differentiableAt (mem_interior_iff_mem_nhds.mp hx)⟩

end Problem358

end

/-! # Supporting slopes at differentiability points

The elementary local step used to identify the equality locus of a
Fenchel certificate.  No convexity assumption is needed once a supporting
inequality is supplied.
-/

noncomputable section

open Set Filter
open scoped Topology RealInnerProductSpace

namespace Problem358

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A supporting slope on a neighborhood is the derivative. -/
theorem hasFDerivAt_eq_innerSL_of_supporting
    {u : H → ℝ} {D : H →L[ℝ] ℝ} {K : Set H} {x p : H}
    (hu : HasFDerivAt u D x) (hx : x ∈ interior K)
    (hp : ∀ z ∈ K, u x + ⟪p, z - x⟫ ≤ u z) :
    D = innerSL ℝ p := by
  have hmin : IsLocalMin (fun z => u z - ⟪p, z⟫) x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with z hz
    have h := hp z hz
    simp only [inner_sub_right] at h
    linarith
  have hderiv : HasFDerivAt (fun z => u z - ⟪p, z⟫)
      (D - innerSL ℝ p) x := hu.sub (innerSL ℝ p).hasFDerivAt
  exact sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero hderiv)

/-- Evaluated form of the supporting-slope identification. -/
theorem hasFDerivAt_apply_eq_inner_of_supporting
    {u : H → ℝ} {D : H →L[ℝ] ℝ} {K : Set H} {x p : H}
    (hu : HasFDerivAt u D x) (hx : x ∈ interior K)
    (hp : ∀ z ∈ K, u x + ⟪p, z - x⟫ ≤ u z) (v : H) :
    D v = ⟪p, v⟫ := by
  rw [hasFDerivAt_eq_innerSL_of_supporting hu hx hp]
  rfl

/-- Supporting slopes are unique at an interior differentiability point. -/
theorem supporting_slope_unique
    {u : H → ℝ} {K : Set H} {x p q : H}
    (hu : DifferentiableAt ℝ u x) (hx : x ∈ interior K)
    (hp : ∀ z ∈ K, u x + ⟪p, z - x⟫ ≤ u z)
    (hq : ∀ z ∈ K, u x + ⟪q, z - x⟫ ≤ u z) : p = q := by
  apply ext_inner_right ℝ
  intro v
  exact (hasFDerivAt_apply_eq_inner_of_supporting hu.hasFDerivAt hx hp v).symm.trans
    (hasFDerivAt_apply_eq_inner_of_supporting hu.hasFDerivAt hx hq v)

/-- Equality in a Fenchel inequality produces a supporting slope. -/
theorem supporting_of_fenchel_eq
    {u : H → ℝ} {v : H → ℝ} {K : Set H} {x y : H}
    (hdual : ∀ z ∈ K, ⟪z, y⟫ ≤ u z + v y)
    (heq : ⟪x, y⟫ = u x + v y) :
    ∀ z ∈ K, u x + ⟪y, z - x⟫ ≤ u z := by
  intro z hz
  have h := hdual z hz
  rw [inner_sub_right, real_inner_comm z y, real_inner_comm x y]
  linarith

/-- At an interior differentiability point, equality in a Fenchel
certificate forces the target coordinate to equal any known supporting slope. -/
theorem eq_supporting_slope_of_fenchel_eq
    {u : H → ℝ} {v : H → ℝ} {K : Set H} {x p y : H}
    (hu : DifferentiableAt ℝ u x) (hx : x ∈ interior K)
    (hp : ∀ z ∈ K, u x + ⟪p, z - x⟫ ≤ u z)
    (hdual : ∀ z ∈ K, ⟪z, y⟫ ≤ u z + v y)
    (heq : ⟪x, y⟫ = u x + v y) : y = p :=
  supporting_slope_unique hu hx (supporting_of_fenchel_eq hdual heq) hp

end Problem358

end

/-! # Almost-everywhere uniqueness of supporting slopes

Rademacher's theorem and the null boundary of a convex set provide the
regularity needed by the local supporting-slope lemmas.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal

namespace Problem358

/-- Source-a.e. supporting-slope uniqueness for the exact uniform normalization. -/
theorem uniform_ae_supporting_slope_unique
    {d : ℕ} {K : Set (E d)} {u : E d → ℝ} {L : ℝ≥0}
    (hK : Convex ℝ K) (hKm : MeasurableSet K) (hu : LipschitzOnWith L u K) :
    ∀ᵐ x ∂uniformMeasure K, ∀ p q : E d,
      (∀ z ∈ K, u x + ⟪p, z - x⟫ ≤ u z) →
      (∀ z ∈ K, u x + ⟪q, z - x⟫ ≤ u z) → p = q := by
  filter_upwards [ae_differentiableAt_uniformMeasure hK hKm hu] with x hx
  intro p q hp hq
  exact supporting_slope_unique hx.2 hx.1 hp hq

/-- A Fenchel equality locus is the graph of a known supporting map,
source-almost everywhere.  This is the pointwise input for uniqueness of plans. -/
theorem uniform_ae_eq_supporting_map_of_fenchel_eq
    {d : ℕ} {K Y : Set (E d)} {u v : E d → ℝ} {T : E d → E d} {L : ℝ≥0}
    (hK : Convex ℝ K) (hKm : MeasurableSet K) (hu : LipschitzOnWith L u K)
    (hT : ∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K, u x + ⟪T x, z - x⟫ ≤ u z)
    (hdual : ∀ y ∈ Y, ∀ z ∈ K, ⟪z, y⟫ ≤ u z + v y) :
    ∀ᵐ x ∂uniformMeasure K, ∀ y ∈ Y,
      ⟪x, y⟫ = u x + v y → y = T x := by
  filter_upwards [ae_differentiableAt_uniformMeasure hK hKm hu, hT]
    with x hx hsupport
  intro y hy heq
  exact eq_supporting_slope_of_fenchel_eq hx.2 hx.1 hsupport (hdual y hy) heq

end Problem358

end

end OAI
