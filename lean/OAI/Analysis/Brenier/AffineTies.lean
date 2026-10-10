import OAI.Analysis.Brenier.Basic

namespace OAI

noncomputable section

section

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace

namespace Problem358

/-- A level set of a nonzero linear functional given by an inner product is null. -/
theorem haar_inner_level_null {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsAddHaarMeasure μ] {v : V} (hv : v ≠ 0) (c : ℝ) :
    μ {x : V | ⟪v, x⟫_ℝ = c} = 0 := by
  let S : AffineSubspace ℝ V :=
    (affineSpan ℝ ({c} : Set ℝ)).comap (innerₗ V v).toAffineMap
  have hS : (S : Set V) = {x : V | ⟪v, x⟫_ℝ = c} := by
    ext x
    simp [S]
  rw [← hS]
  apply addHaar_affineSubspace μ S
  intro htop
  have h0 : (0 : V) ∈ S := htop ▸ AffineSubspace.mem_top ℝ V 0
  have hv' : v ∈ S := htop ▸ AffineSubspace.mem_top ℝ V v
  rw [← SetLike.mem_coe, hS] at h0 hv'
  simp only [Set.mem_ofPred_eq, inner_zero_right] at h0 hv'
  exact hv (inner_self_eq_zero.mp (hv'.trans h0.symm))

/-- Distinct affine slopes can agree only on a Haar-null hyperplane. -/
theorem haar_affine_tie_null {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsAddHaarMeasure μ] {v w : V} (hvw : v ≠ w)
    (a b : ℝ) : μ {x : V | ⟪x, v⟫_ℝ + a = ⟪x, w⟫_ℝ + b} = 0 := by
  convert haar_inner_level_null μ (sub_ne_zero.mpr hvw) (b - a) using 1
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, inner_sub_left]
  rw [real_inner_comm v x, real_inner_comm w x]
  constructor <;> intro h <;> linarith

/-- In a countable affine family, equality of values almost everywhere forces equality of slopes. -/
theorem ae_affine_tie_implies_slopes_eq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsAddHaarMeasure μ] {ι : Type*} [Countable ι]
    (y : ι → V) (c : ι → ℝ) :
    ∀ᵐ x ∂μ, ∀ i j, ⟪x, y i⟫_ℝ + c i = ⟪x, y j⟫_ℝ + c j → y i = y j := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases h : y i = y j
  · exact Filter.Eventually.of_forall (fun _ _ => h)
  · have hne : ∀ᵐ x ∂μ, ⟪x, y i⟫_ℝ + c i ≠ ⟪x, y j⟫_ℝ + c j := by
      rw [ae_iff]
      simpa only [not_not] using haar_affine_tie_null μ h (c i) (c j)
    exact hne.mono (fun _ hx heq => (hx heq).elim)

/-- The finite-affine maximum has a unique maximizing slope off a null set, even if
    the presentation has repeated slopes. -/
theorem ae_unique_maximizing_slope {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsAddHaarMeasure μ] {ι : Type*} [Fintype ι] [Nonempty ι]
    (y : ι → V) (c : ι → ℝ) :
    ∀ᵐ x ∂μ, ∃ i, (∀ j, ⟪x, y j⟫_ℝ + c j ≤ ⟪x, y i⟫_ℝ + c i) ∧
      ∀ j, ⟪x, y i⟫_ℝ + c i ≤ ⟪x, y j⟫_ℝ + c j → y j = y i := by
  classical
  filter_upwards [ae_affine_tie_implies_slopes_eq μ y c] with x hx
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j => ⟪x, y j⟫_ℝ + c j) Finset.univ_nonempty
  refine ⟨i, fun j => hi j (Finset.mem_univ j), ?_⟩
  intro j hj
  exact hx j i (le_antisymm (hi j (Finset.mem_univ j)) hj)

/-- Uniform restrictions preserve the nullity of affine ties; no volume assumptions
    on the source set are needed for this fact. -/
theorem uniform_ae_affine_tie_implies_slopes_eq {d : ℕ} (K : Set (E d))
    {ι : Type*} [Countable ι] (y : ι → E d) (c : ι → ℝ) :
    ∀ᵐ x ∂uniformMeasure K, ∀ i j,
      ⟪x, y i⟫_ℝ + c i = ⟪x, y j⟫_ℝ + c j → y i = y j := by
  have hac : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  exact hac.ae_le (ae_affine_tie_implies_slopes_eq volume y c)

/-- A finite affine maximum has an almost-everywhere unique slope under the source measure. -/
theorem uniform_ae_unique_maximizing_slope {d : ℕ} (K : Set (E d))
    {ι : Type*} [Fintype ι] [Nonempty ι] (y : ι → E d) (c : ι → ℝ) :
    ∀ᵐ x ∂uniformMeasure K, ∃ i,
      (∀ j, ⟪x, y j⟫_ℝ + c j ≤ ⟪x, y i⟫_ℝ + c i) ∧
      ∀ j, ⟪x, y i⟫_ℝ + c i ≤ ⟪x, y j⟫_ℝ + c j → y j = y i := by
  have hac : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  exact hac.ae_le (ae_unique_maximizing_slope volume y c)

end Problem358

end

/-!+# Generic lines avoid affine subspaces of codimension at least two

This is the general-position step used in the cell-connectivity argument.
It does not assert that a nonempty cell intersection has positive surface measure.
-/

section

open MeasureTheory MeasureTheory.Measure Set

namespace Problem358.GenericSegmentAvoidance

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Adjoining one point to a subspace of codimension at least two leaves a proper
affine subspace. -/
theorem affineSpan_insert_ne_top (S : AffineSubspace ℝ E) (p : E)
    (hcodim : Module.finrank ℝ S.direction + 1 < Module.finrank ℝ E) :
    affineSpan ℝ (insert p (S : Set E)) ≠ ⊤ := by
  intro h
  have hd := finrank_vectorSpan_insert_le S p
  rw [← direction_affineSpan, h, AffineSubspace.direction_top, finrank_top] at hd
  omega

/-- A point outside the affine span of `p` and `S` determines a line through `p`
which misses `S`, provided `p` itself is outside `S`. -/
theorem lineMap_not_mem_of_not_mem_affineSpan_insert
    (S : AffineSubspace ℝ E) {p q : E} (hp : p ∉ S)
    (hq : q ∉ affineSpan ℝ (insert p (S : Set E))) (t : ℝ) :
    AffineMap.lineMap p q t ∉ S := by
  intro ht
  by_cases ht0 : t = 0
  · apply hp
    simpa [ht0] using ht
  have hp' : p ∈ affineSpan ℝ (insert p (S : Set E)) :=
    mem_affineSpan ℝ (mem_insert p _)
  have ht' : AffineMap.lineMap p q t ∈ affineSpan ℝ (insert p (S : Set E)) :=
    mem_affineSpan ℝ (mem_insert_of_mem p ht)
  have hq' := AffineMap.lineMap_mem t⁻¹ hp' ht'
  apply hq
  simpa [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ ht0] using hq'

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Affine subspaces of codimension at least two can be avoided by a generic line
through a fixed point. The second endpoint can be chosen in any prescribed
nonempty open set and outside any countable collection of proper affine subspaces. -/
theorem exists_line_avoiding
    {ι κ : Type*} [Countable ι] [Countable κ]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (S : ι → AffineSubspace ℝ E) (H : κ → AffineSubspace ℝ E)
    (hS : ∀ i, Module.finrank ℝ (S i).direction + 1 < Module.finrank ℝ E)
    (hH : ∀ j, H j ≠ ⊤) {p : E} (hp : ∀ i, p ∉ S i)
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ q ∈ U, (∀ j, q ∉ H j) ∧
      ∀ i (t : ℝ), AffineMap.lineMap p q t ∉ S i := by
  have hspan : ∀ᵐ q ∂μ, ∀ i, q ∉ affineSpan ℝ (insert p (S i : Set E)) := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    simpa using addHaar_affineSubspace μ _ (affineSpan_insert_ne_top (S i) p (hS i))
  have hplanes : ∀ᵐ q ∂μ, ∀ j, q ∉ H j := by
    rw [ae_all_iff]
    intro j
    rw [ae_iff]
    simpa using addHaar_affineSubspace μ (H j) (hH j)
  obtain ⟨q, hqU, hqH, hqS⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hU.measure_ne_zero μ hne) (ae_restrict_of_ae (hplanes.and hspan))
  refine ⟨q, hqU, hqH, fun i t => ?_⟩
  exact lineMap_not_mem_of_not_mem_affineSpan_insert (S i) (hp i) (hqS i) t

/-- Segment formulation of the general-position lemma. -/
theorem exists_segment_avoiding
    {ι κ : Type*} [Countable ι] [Countable κ]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (S : ι → AffineSubspace ℝ E) (H : κ → AffineSubspace ℝ E)
    (hS : ∀ i, Module.finrank ℝ (S i).direction + 1 < Module.finrank ℝ E)
    (hH : ∀ j, H j ≠ ⊤) {p : E} (hp : ∀ i, p ∉ S i)
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ q ∈ U, (∀ j, q ∉ H j) ∧
      ∀ i, Disjoint (segment ℝ p q) (S i : Set E) := by
  obtain ⟨q, hqU, hqH, hqS⟩ := exists_line_avoiding μ S H hS hH hp hU hne
  refine ⟨q, hqU, hqH, fun i => ?_⟩
  rw [Set.disjoint_left]
  intro x hx hxS
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, _, rfl⟩ := hx
  exact hqS i t hxS

end

open scoped RealInnerProductSpace

/-- Independent affine equations give the expected lower bound on codimension,
including when the common level set is empty. -/
theorem finrank_direction_add_card_le_of_inner_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]
    (S : AffineSubspace ℝ V) (v : ι → V) (a : ι → ℝ)
    (hv : LinearIndependent ℝ v)
    (hS : ∀ x ∈ S, ∀ i, ⟪x, v i⟫ = a i) :
    Module.finrank ℝ S.direction + Fintype.card ι ≤ Module.finrank ℝ V := by
  let W : Submodule ℝ V := Submodule.span ℝ (Set.range v)
  have hdir : S.direction ≤ Wᗮ := by
    rw [S.direction_eq_vectorSpan, vectorSpan_def]
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_vsub.mp hz
    apply (Submodule.mem_orthogonal' W (x -ᵥ y)).mpr
    intro w hw
    change w ∈ Submodule.span ℝ (Set.range v) at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        simp only [vsub_eq_sub, inner_sub_left, hS x hx i, hS y hy i, sub_self]
    | zero => simp
    | add u w hu hw ihu ihw => rw [inner_add_right, ihu, ihw, add_zero]
    | smul c w hw ihw => rw [inner_smul_right, ihw, mul_zero]
  have hd := Submodule.finrank_mono hdir
  have hdim := W.finrank_add_finrank_orthogonal
  have hW : Module.finrank ℝ W = Fintype.card ι := finrank_span_eq_card hv
  omega

end Problem358.GenericSegmentAvoidance

end

section

open scoped RealInnerProductSpace

namespace Problem358.TripleCell

/-- Three functions, each strictly largest somewhere, cannot have proportional differences. -/
theorem no_proportional_differences {X : Type*} {f g h : X → ℝ}
    (hf : ∃ x, g x < f x ∧ h x < f x)
    (hg : ∃ x, f x < g x ∧ h x < g x)
    (hh : ∃ x, f x < h x ∧ g x < h x) :
    ¬ ∃ r : ℝ, ∀ x, f x - h x = r * (f x - g x) := by
  rintro ⟨r, hr⟩
  obtain ⟨x0, h0g, h0h⟩ := hf
  obtain ⟨x1, h1f, h1h⟩ := hg
  obtain ⟨x2, h2f, h2g⟩ := hh
  have hpos : 0 < r := by
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (le_of_lt (sub_pos.mpr h0g))
    nlinarith [hr x0]
  have hlt : r < 1 := by
    by_contra hn
    have hm := mul_le_mul_of_nonpos_right (le_of_not_gt hn) (le_of_lt (sub_neg.mpr h1f))
    nlinarith [hr x1]
  have hneg : f x2 - g x2 < 0 := by
    by_contra hn
    have hm := mul_nonneg hpos.le (le_of_not_gt hn)
    nlinarith [hr x2]
  have hm := mul_lt_mul_of_neg_right hlt hneg
  nlinarith [hr x2]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The affine score whose slope is `y` and whose intercept is `c`. -/
def score (y : V) (c : ℝ) (x : V) : ℝ := ⟪x, y⟫ + c

/-- At a common tie point, strict activity of all three branches excludes
proportional slope differences. -/
theorem no_proportional_slopes_of_tie {y0 y1 y2 z : V} {c0 c1 c2 : ℝ}
    (hf : ∃ x, score y1 c1 x < score y0 c0 x ∧ score y2 c2 x < score y0 c0 x)
    (hg : ∃ x, score y0 c0 x < score y1 c1 x ∧ score y2 c2 x < score y1 c1 x)
    (hh : ∃ x, score y0 c0 x < score y2 c2 x ∧ score y1 c1 x < score y2 c2 x)
    (h01 : score y0 c0 z = score y1 c1 z)
    (h02 : score y0 c0 z = score y2 c2 z) :
    ∀ r : ℝ, r • (y0 - y1) ≠ y0 - y2 := by
  intro r hr
  apply no_proportional_differences hf hg hh
  refine ⟨r, ?_⟩
  have hv (x : V) : ⟪x, y0⟫ - ⟪x, y2⟫ =
      r * (⟪x, y0⟫ - ⟪x, y1⟫) := by
    have he := congrArg (fun v : V => ⟪x, v⟫) hr
    simpa only [inner_smul_right, inner_sub_right] using he.symm
  have hc : c0 - c2 = r * (c0 - c1) := by
    unfold score at h01 h02
    have hm := congrArg (fun a : ℝ => r * a) h01
    nlinarith [hv z]
  intro x
  unfold score
  nlinarith [hv x]

/-- The two tie-plane normals at a triple tie are linearly independent whenever
all three affine branches are strictly active somewhere. -/
theorem linearIndependent_slopes_of_tie {y0 y1 y2 z : V} {c0 c1 c2 : ℝ}
    (hf : ∃ x, score y1 c1 x < score y0 c0 x ∧ score y2 c2 x < score y0 c0 x)
    (hg : ∃ x, score y0 c0 x < score y1 c1 x ∧ score y2 c2 x < score y1 c1 x)
    (hh : ∃ x, score y0 c0 x < score y2 c2 x ∧ score y1 c1 x < score y2 c2 x)
    (h01 : score y0 c0 z = score y1 c1 z)
    (h02 : score y0 c0 z = score y2 c2 z) :
    LinearIndependent ℝ ![y0 - y1, y0 - y2] := by
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro hzero
    have hy : y0 = y2 := sub_eq_zero.mp hzero
    obtain ⟨x, _, hstrict⟩ := hf
    unfold score at h02 hstrict
    rw [hy] at h02 hstrict
    linarith
  · apply no_proportional_slopes_of_tie
      (hf.imp fun x hx => hx.symm) hh hg h02 h01

/-- A vector outside a line is detected by some vector tangent to its orthogonal plane. -/
theorem exists_tangent_inner_ne_zero {u v : V}
    (h : ∀ r : ℝ, r • u ≠ v) :
    ∃ w : (ℝ ∙ u)ᗮ, ⟪(w : V), v⟫ ≠ 0 := by
  by_contra! hn
  have hv : v ∈ ((ℝ ∙ u)ᗮ)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro w hw
    exact hn ⟨w, hw⟩
  rw [Submodule.orthogonal_orthogonal] at hv
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hv
  exact h r hr

/-- The second independent tie normal cuts out a null set for Haar measure on
 the first tie plane's tangent vector space. -/
theorem tangent_inner_zero_null [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {u v : V}
    (h : ∀ r : ℝ, r • u ≠ v)
    (μ : MeasureTheory.Measure ((ℝ ∙ u)ᗮ)) [μ.IsAddHaarMeasure] :
    μ {w : (ℝ ∙ u)ᗮ | ⟪(w : V), v⟫ = 0} = 0 := by
  let L : ((ℝ ∙ u)ᗮ) →ₗ[ℝ] ℝ := (innerₗ V v).comp ((ℝ ∙ u)ᗮ).subtype
  have hker : L.ker ≠ ⊤ := by
    obtain ⟨w, hw⟩ := exists_tangent_inner_ne_zero h
    intro heq
    have hm : w ∈ L.ker := by rw [heq]; trivial
    apply hw
    simpa [L, real_inner_comm] using hm
  have heq : {w : (ℝ ∙ u)ᗮ | ⟪(w : V), v⟫ = 0} = (L.ker : Set ((ℝ ∙ u)ᗮ)) := by
    ext w
    simp [L, real_inner_comm]
  rw [heq]
  exact MeasureTheory.Measure.addHaar_submodule μ L.ker hker

/-- Every affine level of the second independent normal is surface-null. -/
theorem tangent_inner_level_null [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {u v : V}
    (h : ∀ r : ℝ, r • u ≠ v)
    (μ : MeasureTheory.Measure ((ℝ ∙ u)ᗮ)) [μ.IsAddHaarMeasure] (t : ℝ) :
    μ {w : (ℝ ∙ u)ᗮ | ⟪(w : V), v⟫ = t} = 0 := by
  let S : Set ((ℝ ∙ u)ᗮ) := {w | ⟪(w : V), v⟫ = t}
  change μ S = 0
  by_cases hs : S.Nonempty
  · obtain ⟨w0, hw0⟩ := hs
    have heq : (fun w => w0 + w) ⁻¹' S =
        {w : (ℝ ∙ u)ᗮ | ⟪(w : V), v⟫ = 0} := by
      ext w
      change ⟪((w0 + w : (ℝ ∙ u)ᗮ) : V), v⟫ = t ↔ ⟪(w : V), v⟫ = 0
      change ⟪(w0 : V) + (w : V), v⟫ = t ↔ ⟪(w : V), v⟫ = 0
      rw [inner_add_left, show ⟪(w0 : V), v⟫ = t from hw0]
      simp
    rw [← MeasureTheory.measure_preimage_add μ w0 S, heq]
    exact tangent_inner_zero_null h μ
  · rw [Set.not_nonempty_iff_eq_empty.mp hs]
    exact MeasureTheory.measure_empty

/-- The common tie locus of three active cells is surface-null in a tie plane,
parametrized at any common tie point. -/
theorem triple_tie_surface_null [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {y0 y1 y2 z : V} {c0 c1 c2 : ℝ}
    (hf : ∃ x, score y1 c1 x < score y0 c0 x ∧ score y2 c2 x < score y0 c0 x)
    (hg : ∃ x, score y0 c0 x < score y1 c1 x ∧ score y2 c2 x < score y1 c1 x)
    (hh : ∃ x, score y0 c0 x < score y2 c2 x ∧ score y1 c1 x < score y2 c2 x)
    (h01 : score y0 c0 z = score y1 c1 z)
    (h02 : score y0 c0 z = score y2 c2 z)
    (μ : MeasureTheory.Measure ((ℝ ∙ (y0 - y1))ᗮ)) [μ.IsAddHaarMeasure] :
    μ {w : (ℝ ∙ (y0 - y1))ᗮ |
      score y0 c0 (z + (w : V)) = score y2 c2 (z + (w : V))} = 0 := by
  have heq : {w : (ℝ ∙ (y0 - y1))ᗮ |
      score y0 c0 (z + (w : V)) = score y2 c2 (z + (w : V))} =
      {w : (ℝ ∙ (y0 - y1))ᗮ | ⟪(w : V), y0 - y2⟫ = 0} := by
    ext w
    simp only [Set.mem_ofPred_eq, score, inner_add_left, inner_sub_right]
    unfold score at h02
    constructor <;> intro hw <;> linarith
  rw [heq]
  exact tangent_inner_zero_null (no_proportional_slopes_of_tie hf hg hh h01 h02) μ

/-- The triple tie locus is surface-null when the first tie hyperplane is
parametrized at any of its points; no triple tie need be specified in advance. -/
theorem triple_tie_surface_null_of_first_tie [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {y0 y1 y2 z : V} {c0 c1 c2 : ℝ}
    (hf : ∃ x, score y1 c1 x < score y0 c0 x ∧ score y2 c2 x < score y0 c0 x)
    (hg : ∃ x, score y0 c0 x < score y1 c1 x ∧ score y2 c2 x < score y1 c1 x)
    (hh : ∃ x, score y0 c0 x < score y2 c2 x ∧ score y1 c1 x < score y2 c2 x)
    (h01 : score y0 c0 z = score y1 c1 z)
    (μ : MeasureTheory.Measure ((ℝ ∙ (y0 - y1))ᗮ)) [μ.IsAddHaarMeasure] :
    μ {w : (ℝ ∙ (y0 - y1))ᗮ |
      score y0 c0 (z + (w : V)) = score y2 c2 (z + (w : V))} = 0 := by
  let S := {w : (ℝ ∙ (y0 - y1))ᗮ |
      score y0 c0 (z + (w : V)) = score y2 c2 (z + (w : V))}
  change μ S = 0
  by_cases hs : S.Nonempty
  · obtain ⟨w0, hw0⟩ := hs
    have horth : ⟪(w0 : V), y0 - y1⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp w0.property
    have h01' : score y0 c0 (z + (w0 : V)) = score y1 c1 (z + (w0 : V)) := by
      unfold score at h01 ⊢
      rw [inner_sub_right] at horth
      simp only [inner_add_left]
      linarith
    have hnonprop := no_proportional_slopes_of_tie hf hg hh h01' hw0
    have heq : S = {w : (ℝ ∙ (y0 - y1))ᗮ |
        ⟪(w : V), y0 - y2⟫ = c2 - c0 - (⟪z, y0⟫ - ⟪z, y2⟫)} := by
      ext w
      simp only [S, Set.mem_ofPred_eq, score, inner_add_left, inner_sub_right]
      constructor <;> intro hw <;> linarith
    rw [heq]
    exact tangent_inner_level_null hnonprop μ _
  · rw [Set.not_nonempty_iff_eq_empty.mp hs]
    exact MeasureTheory.measure_empty

/-- On a fixed interface of a finite strictly-active affine family, almost every
surface point avoids every other tie hyperplane. -/
theorem ae_no_other_ties_on_interface {ι : Type*} [Fintype ι]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (y : ι → V) (c : ι → ℝ)
    (hactive : ∀ i, ∃ x, ∀ j, j ≠ i → score (y j) (c j) x < score (y i) (c i) x)
    {i j : ι} (hij : i ≠ j) {z : V}
    (htie : score (y i) (c i) z = score (y j) (c j) z)
    (μ : MeasureTheory.Measure ((ℝ ∙ (y i - y j))ᗮ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ w : (ℝ ∙ (y i - y j))ᗮ ∂μ, ∀ k, k ≠ i → k ≠ j →
      score (y i) (c i) (z + (w : V)) ≠ score (y k) (c k) (z + (w : V)) := by
  apply (MeasureTheory.ae_all_iff).mpr
  intro k
  by_cases hki : k = i
  · subst k
    exact Filter.Eventually.of_forall (fun _ h => (h rfl).elim)
  by_cases hkj : k = j
  · subst k
    exact Filter.Eventually.of_forall (fun _ _ h => (h rfl).elim)
  have hnull : μ {w : (ℝ ∙ (y i - y j))ᗮ |
      score (y i) (c i) (z + (w : V)) = score (y k) (c k) (z + (w : V))} = 0 := by
    apply triple_tie_surface_null_of_first_tie (z := z) (μ := μ) ?_ ?_ ?_ htie
    · obtain ⟨x, hx⟩ := hactive i
      exact ⟨x, hx j hij.symm, hx k hki⟩
    · obtain ⟨x, hx⟩ := hactive j
      exact ⟨x, hx i hij, hx k hkj⟩
    · obtain ⟨x, hx⟩ := hactive k
      exact ⟨x, hx i (Ne.symm hki), hx j (Ne.symm hkj)⟩
  have hae : ∀ᵐ w : (ℝ ∙ (y i - y j))ᗮ ∂μ,
      score (y i) (c i) (z + (w : V)) ≠ score (y k) (c k) (z + (w : V)) := by
    simpa only [MeasureTheory.ae_iff, not_not] using hnull
  exact hae.mono (fun _ hw _ _ => hw)

end Problem358.TripleCell

end

namespace Problem358.GenericSegment

open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def affineScore (v : V) (c : ℝ) (x : V) : ℝ := inner ℝ v x + c

lemma affineScore_combination (v p q : V) (c a b : ℝ) (hab : a + b = 1) :
    affineScore v c (a • p + b • q) =
      a * affineScore v c p + b * affineScore v c q := by
  simp only [affineScore, inner_add_right, inner_smul_right]
  linear_combination -c * hab

/-- A nonzero endpoint determinant excludes a simultaneous affine zero on
the entire segment, including its endpoints. -/
theorem segment_avoids_common_zero_of_det_ne_zero
    {v w p q : V} {c d : ℝ}
    (hdet : affineScore v c p * affineScore w d q -
      affineScore w d p * affineScore v c q ≠ 0) :
    ∀ x ∈ segment ℝ p q,
      ¬ (affineScore v c x = 0 ∧ affineScore w d x = 0) := by
  rintro x ⟨a, b, _, _, hab, rfl⟩ ⟨hf, hg⟩
  rw [affineScore_combination v p q c a b hab] at hf
  rw [affineScore_combination w p q d a b hab] at hg
  by_cases hb : b = 0
  · have ha : a = 1 := by linarith
    simp only [ha, hb, one_mul, zero_mul, add_zero] at hf hg
    exact hdet (by simp [hf, hg])
  · have hzero : b * (affineScore v c p * affineScore w d q -
        affineScore w d p * affineScore v c q) = 0 := by
      linear_combination (affineScore v c p) * hg - (affineScore w d p) * hf
    exact hdet ((mul_eq_zero.mp hzero).resolve_left hb)

/-- For independent normals, the endpoint determinant is a nonconstant
affine function of the second endpoint, provided the first endpoint avoids
the first hyperplane. -/
theorem determinant_normal_ne_zero {v w p : V} {c d : ℝ}
    (hvw : LinearIndependent ℝ ![v, w]) (hp : affineScore v c p ≠ 0) :
    affineScore v c p • w - affineScore w d p • v ≠ 0 := by
  intro hzero
  have heq : affineScore w d p • v = affineScore v c p • w :=
    (sub_eq_zero.mp hzero).symm
  exact hp (hvw.eq_zero_of_pair' heq).2

lemma determinant_eq_affine (v w p q : V) (c d : ℝ) :
    affineScore v c p * affineScore w d q -
      affineScore w d p * affineScore v c q =
    inner ℝ (affineScore v c p • w - affineScore w d p • v) q +
      (affineScore v c p * d - affineScore w d p * c) := by
  simp [affineScore, inner_sub_left, inner_smul_left]
  ring

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (μ : Measure V) [IsAddHaarMeasure μ]
include μ

/-- The exceptional second endpoints for a fixed independent pair lie on a
single Haar-null affine hyperplane. -/
theorem ae_endpoint_determinant_ne_zero {v w p : V} {c d : ℝ}
    (hvw : LinearIndependent ℝ ![v, w]) (hp : affineScore v c p ≠ 0) :
    ∀ᵐ q ∂μ, affineScore v c p * affineScore w d q -
      affineScore w d p * affineScore v c q ≠ 0 := by
  rw [ae_iff]
  have hnormal := determinant_normal_ne_zero (d := d) hvw hp
  have hnull := haar_inner_level_null μ hnormal
    (-(affineScore v c p * d - affineScore w d p * c))
  convert hnull using 1
  congr 1
  ext q
  simp only [Set.mem_ofPred_eq, not_not, determinant_eq_affine]
  constructor <;> intro h <;> linarith

/-- A generic segment from a fixed endpoint avoids every member of a
countable family of codimension-two affine intersections. -/
theorem ae_segment_avoids_common_zeros {ι : Type*} [Countable ι]
    (v w : ι → V) (c d : ι → ℝ) {p : V}
    (hvw : ∀ i, LinearIndependent ℝ ![v i, w i])
    (hp : ∀ i, affineScore (v i) (c i) p ≠ 0) :
    ∀ᵐ q ∂μ, ∀ i, ∀ x ∈ segment ℝ p q,
      ¬ (affineScore (v i) (c i) x = 0 ∧
        affineScore (w i) (d i) x = 0) := by
  have hdet : ∀ᵐ q ∂μ, ∀ i,
      affineScore (v i) (c i) p * affineScore (w i) (d i) q -
      affineScore (w i) (d i) p * affineScore (v i) (c i) q ≠ 0 := by
    rw [ae_all_iff]
    intro i
    exact ae_endpoint_determinant_ne_zero μ (hvw i) (hp i)
  filter_upwards [hdet] with q hq i
  exact segment_avoids_common_zero_of_det_ne_zero (hq i)

/-- In particular one can choose the second endpoint in any prescribed
nonempty open region, as needed when connecting strict cell interiors. -/
theorem exists_endpoint_in_open_avoiding_common_zeros {ι : Type*} [Countable ι]
    (v w : ι → V) (c d : ι → ℝ) {p : V} {U : Set V}
    (hvw : ∀ i, LinearIndependent ℝ ![v i, w i])
    (hp : ∀ i, affineScore (v i) (c i) p ≠ 0)
    (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, ∀ i, ∀ x ∈ segment ℝ p q,
      ¬ (affineScore (v i) (c i) x = 0 ∧
        affineScore (w i) (d i) x = 0) := by
  apply Measure.exists_mem_of_measure_ne_zero_of_ae (hU.measure_ne_zero μ hUne)
  exact ae_restrict_of_ae (ae_segment_avoids_common_zeros μ v w c d hvw hp)

end Problem358.GenericSegment

/-! General-position segments for finite strictly active affine families. -/

namespace Problem358.TripleTieAvoidance

open Set MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The equality hyperplane of two affine scores. -/
def tieSpace (y z : V) (a b : ℝ) : AffineSubspace ℝ V :=
  (affineSpan ℝ ({b - a} : Set ℝ)).comap (innerₗ V (y - z)).toAffineMap

@[simp] theorem mem_tieSpace {y z x : V} {a b : ℝ} :
    x ∈ tieSpace y z a b ↔ TripleCell.score y a x = TripleCell.score z b x := by
  simp [tieSpace, TripleCell.score, real_inner_comm]
  constructor <;> intro h <;> linarith

theorem tieSpace_ne_top {y z : V} {a b : ℝ}
    (h : ∃ x, TripleCell.score y a x ≠ TripleCell.score z b x) :
    tieSpace y z a b ≠ ⊤ := by
  obtain ⟨x, hx⟩ := h
  intro heq
  apply hx
  apply mem_tieSpace.mp
  rw [heq]
  trivial

/-- The common equality locus of three affine scores. -/
def tripleSpace (y : Fin 3 → V) (c : Fin 3 → ℝ) : AffineSubspace ℝ V :=
  tieSpace (y 0) (y 1) (c 0) (c 1) ⊓ tieSpace (y 0) (y 2) (c 0) (c 2)

@[simp] theorem mem_tripleSpace {y : Fin 3 → V} {c : Fin 3 → ℝ} {x : V} :
    x ∈ tripleSpace y c ↔
      TripleCell.score (y 0) (c 0) x = TripleCell.score (y 1) (c 1) x ∧
      TripleCell.score (y 0) (c 0) x = TripleCell.score (y 2) (c 2) x := by
  simp only [tripleSpace, AffineSubspace.mem_inf_iff, mem_tieSpace]

/-- Strict activity of each branch forces every nonempty triple tie to have
codimension at least two. Empty loci satisfy the same bound in dimension at least two. -/
theorem tripleSpace_codimension [FiniteDimensional ℝ V]
    (hd : 2 ≤ Module.finrank ℝ V) (y : Fin 3 → V) (c : Fin 3 → ℝ)
    (hactive : ∀ i, ∃ x, ∀ j, j ≠ i →
      TripleCell.score (y j) (c j) x < TripleCell.score (y i) (c i) x) :
    Module.finrank ℝ (tripleSpace y c).direction + 1 < Module.finrank ℝ V := by
  by_cases hne : (tripleSpace y c : Set V).Nonempty
  · obtain ⟨z, hz⟩ := hne
    obtain ⟨h01, h02⟩ := mem_tripleSpace.mp hz
    have hli : LinearIndependent ℝ ![y 0 - y 1, y 0 - y 2] := by
      apply TripleCell.linearIndependent_slopes_of_tie ?_ ?_ ?_ h01 h02
      · obtain ⟨x, hx⟩ := hactive 0
        exact ⟨x, hx 1 (by decide), hx 2 (by decide)⟩
      · obtain ⟨x, hx⟩ := hactive 1
        exact ⟨x, hx 0 (by decide), hx 2 (by decide)⟩
      · obtain ⟨x, hx⟩ := hactive 2
        exact ⟨x, hx 0 (by decide), hx 1 (by decide)⟩
    have hdim := GenericSegmentAvoidance.finrank_direction_add_card_le_of_inner_eq
      (tripleSpace y c) ![y 0 - y 1, y 0 - y 2] ![c 1 - c 0, c 2 - c 0] hli
      (by
        intro x hx i
        obtain ⟨hx1, hx2⟩ := mem_tripleSpace.mp hx
        unfold TripleCell.score at hx1 hx2
        fin_cases i
        · change ⟪x, y 0 - y 1⟫ = c 1 - c 0
          rw [inner_sub_right]
          linarith
        · change ⟪x, y 0 - y 2⟫ = c 2 - c 0
          rw [inner_sub_right]
          linarith)
    simp only [Fintype.card_fin] at hdim
    omega
  · have heq : tripleSpace y c = ⊥ := by
      exact (AffineSubspace.coe_eq_bot_iff _).mp (Set.not_nonempty_iff_eq_empty.mp hne)
    rw [heq, AffineSubspace.direction_bot, finrank_bot]
    omega

variable {ι : Type*} [Fintype ι]

private abbrev PairIndex (ι : Type*) := {p : ι × ι // p.1 ≠ p.2}
private abbrev TripleIndex (ι : Type*) :=
  {t : ι × ι × ι // t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}

/-- No two affine scores agree at the point. -/
def NoPairTies (y : ι → V) (c : ι → ℝ) (x : V) : Prop :=
  ∀ i j, i ≠ j → TripleCell.score (y i) (c i) x ≠ TripleCell.score (y j) (c j) x

/-- No three distinct affine scores agree at the point. -/
def NoTripleTies (y : ι → V) (c : ι → ℝ) (x : V) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ¬ (TripleCell.score (y i) (c i) x = TripleCell.score (y j) (c j) x ∧
      TripleCell.score (y i) (c i) x = TripleCell.score (y k) (c k) x)

/-- Two prescribed nonempty open regions contain endpoints of a line avoiding
every triple tie of a finite strictly active affine family. -/
theorem exists_line_no_triple_ties [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsAddHaarMeasure μ] (hd : 2 ≤ Module.finrank ℝ V)
    (y : ι → V) (c : ι → ℝ)
    (hactive : ∀ i, ∃ x, ∀ j, j ≠ i →
      TripleCell.score (y j) (c j) x < TripleCell.score (y i) (c i) x)
    {U W : Set V} (hU : IsOpen U) (hUne : U.Nonempty)
    (hW : IsOpen W) (hWne : W.Nonempty) :
    ∃ p ∈ U, ∃ q ∈ W, NoPairTies y c p ∧ NoPairTies y c q ∧
      ∀ t : ℝ, NoTripleTies y c (AffineMap.lineMap p q t) := by
  classical
  let H : PairIndex ι → AffineSubspace ℝ V :=
    fun ij => tieSpace (y ij.1.1) (y ij.1.2) (c ij.1.1) (c ij.1.2)
  have hH : ∀ ij, H ij ≠ ⊤ := by
    intro ij
    obtain ⟨x, hx⟩ := hactive ij.1.1
    apply tieSpace_ne_top
    exact ⟨x, (ne_of_gt (hx ij.1.2 ij.2.symm))⟩
  have hae : ∀ᵐ p ∂μ, ∀ ij, p ∉ H ij := by
    rw [ae_all_iff]
    intro ij
    rw [ae_iff]
    simpa using addHaar_affineSubspace μ (H ij) (hH ij)
  obtain ⟨p, hpU, hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hU.measure_ne_zero μ hUne) (ae_restrict_of_ae hae)
  let S : TripleIndex ι → AffineSubspace ℝ V := fun ijk =>
    tripleSpace ![y ijk.1.1, y ijk.1.2.1, y ijk.1.2.2]
      ![c ijk.1.1, c ijk.1.2.1, c ijk.1.2.2]
  have hS : ∀ ijk, Module.finrank ℝ (S ijk).direction + 1 < Module.finrank ℝ V := by
    intro ijk
    apply tripleSpace_codimension hd
    intro i
    let v : Fin 3 → ι := ![ijk.1.1, ijk.1.2.1, ijk.1.2.2]
    have hv : Function.Injective v := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> dsimp only [v] at hij ⊢
      all_goals first | rfl | exact (ijk.2.1 hij).elim | exact (ijk.2.2.1 hij).elim | exact (ijk.2.2.2 hij).elim | exact (ijk.2.1 hij.symm).elim | exact (ijk.2.2.1 hij.symm).elim | exact (ijk.2.2.2 hij.symm).elim
    obtain ⟨x, hx⟩ := hactive (v i)
    refine ⟨x, fun j hji => ?_⟩
    convert hx (v j) (hv.ne hji) using 1 <;> fin_cases i <;> fin_cases j <;> rfl
  have hpS : ∀ ijk, p ∉ S ijk := by
    intro ijk hpijk
    apply hp ⟨(ijk.1.1, ijk.1.2.1), ijk.2.1⟩
    exact (show p ∈ S ijk from hpijk).1
  obtain ⟨q, hqW, hq, hline⟩ :=
    GenericSegmentAvoidance.exists_line_avoiding μ S H hS hH hpS hW hWne
  refine ⟨p, hpU, q, hqW, ?_, ?_, ?_⟩
  · intro i j hij heq
    exact hp ⟨(i, j), hij⟩ (mem_tieSpace.mpr heq)
  · intro i j hij heq
    exact hq ⟨(i, j), hij⟩ (mem_tieSpace.mpr heq)
  · intro t i j k hij hik hjk heq
    apply hline ⟨(i, j, k), hij, hik, hjk⟩ t
    exact mem_tripleSpace.mpr heq

/-- The interior region on which one affine score is strictly maximal. -/
def strictRegion (K : Set V) (y : ι → V) (c : ι → ℝ) (i : ι) : Set V :=
  {x | x ∈ interior K ∧ ∀ j, j ≠ i →
    TripleCell.score (y j) (c j) x < TripleCell.score (y i) (c i) x}

theorem isOpen_strictRegion (K : Set V) (y : ι → V) (c : ι → ℝ) (i : ι) :
    IsOpen (strictRegion K y c i) := by
  classical
  have hcont (j : ι) : Continuous (TripleCell.score (y j) (c j)) :=
    (continuous_id.inner continuous_const).add continuous_const
  have heq : strictRegion K y c i = interior K ∩
      ⋂ j, {x | j ≠ i → TripleCell.score (y j) (c j) x <
        TripleCell.score (y i) (c i) x} := by
    ext x
    simp [strictRegion]
  rw [heq]
  apply isOpen_interior.inter
  apply isOpen_iInter_of_finite
  intro j
  by_cases hji : j = i
  · simp [hji]
  · simpa [hji] using isOpen_lt (hcont j) (hcont i)

/-- The general-position segment needed for positive-facet connectivity:
its endpoints are in prescribed strict cells, every point lies in the interior
of the convex source, and no three affine scores agree anywhere on it. -/
theorem exists_segment_between_strict_regions [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsAddHaarMeasure μ] (hd : 2 ≤ Module.finrank ℝ V)
    (K : Set V) (hK : Convex ℝ K) (y : ι → V) (c : ι → ℝ)
    (hactive : ∀ i, (strictRegion K y c i).Nonempty) (i j : ι) :
    ∃ p ∈ strictRegion K y c i, ∃ q ∈ strictRegion K y c j,
      segment ℝ p q ⊆ interior K ∧
        ∀ x ∈ segment ℝ p q, NoTripleTies y c x := by
  have hglobal : ∀ k, ∃ x, ∀ l, l ≠ k →
      TripleCell.score (y l) (c l) x < TripleCell.score (y k) (c k) x := by
    intro k
    obtain ⟨x, hx⟩ := hactive k
    exact ⟨x, hx.2⟩
  obtain ⟨p, hp, q, hq, _, _, hline⟩ := exists_line_no_triple_ties μ hd y c hglobal
    (isOpen_strictRegion K y c i) (hactive i)
    (isOpen_strictRegion K y c j) (hactive j)
  refine ⟨p, hp, q, hq, hK.interior.segment_subset hp.1 hq.1, ?_⟩
  intro x hx
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, _, rfl⟩ := hx
  exact hline t

end Problem358.TripleTieAvoidance

end

end OAI
