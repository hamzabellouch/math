import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Topology

namespace Problem358.TangentNormalCoordinates

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Tangential directions to the normal `v`. -/
abbrev Tangent (v : V) := (ℝ ∙ v)ᗮ

/-- An orthogonal, unit-normal coordinate system, before forgetting the product L² norm. -/
def unitEquiv (v : V) (hv : ‖v‖ = 1) :
    WithLp 2 (ℝ × Tangent v) ≃ₗᵢ[ℝ] V :=
  (LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.toSpanUnitSingleton v hv)
    (LinearIsometryEquiv.refl ℝ (Tangent v))).trans
    (ℝ ∙ v).orthogonalDecomposition.symm

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem unitEquiv_apply [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (v : V) (hv : ‖v‖ = 1) (p : ℝ × Tangent v) :
    unitEquiv v hv (WithLp.toLp 2 p) = p.1 • v + (p.2 : V) := by
  simp [unitEquiv, Submodule.orthogonalDecomposition_symm_apply]

/-- Normal coordinate followed by tangential displacement. -/
def unitMap (v : V) (p : ℝ × Tangent v) : V := p.1 • v + (p.2 : V)

/-- Unit normal/tangent coordinates preserve the canonical Lebesgue measures. -/
theorem measurePreserving_unitMap (v : V) (hv : ‖v‖ = 1) :
    MeasurePreserving (unitMap v) (volume.prod volume) volume := by
  have h := (unitEquiv v hv).measurePreserving.comp
    (WithLp.volume_preserving_toLp ℝ (Tangent v))
  convert! h using 1

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem inner_unitMap [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (v : V) (hv : ‖v‖ = 1) (p : ℝ × Tangent v) :
    ⟪v, unitMap v p⟫_ℝ = p.1 := by
  have ht : ⟪v, (p.2 : V)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.2.property
  simp [unitMap, inner_add_right, inner_smul_right, ht, hv]

/-- The unit-speed isometry from the real line to the span of a nonzero normal. -/
def normalLineEquiv (n : V) (hn : n ≠ 0) : ℝ ≃ₗᵢ[ℝ] (ℝ ∙ n) :=
  (LinearIsometryEquiv.toSpanUnitSingleton ((‖n‖⁻¹ : ℝ) • n)
    (norm_smul_inv_norm hn)).trans
    (LinearIsometryEquiv.ofEq _ _
      (Submodule.span_singleton_smul_eq
        (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hn))) n))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem normalLineEquiv_coe [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (hn : n ≠ 0) (t : ℝ) :
    ((normalLineEquiv n hn t : ℝ ∙ n) : V) = t • ((‖n‖⁻¹ : ℝ) • n) := by
  simp [normalLineEquiv]

/-- Full orthogonal normal/tangent coordinates for an arbitrary nonzero normal. -/
def normalEquiv (n : V) (hn : n ≠ 0) :
    WithLp 2 (ℝ × Tangent n) ≃ₗᵢ[ℝ] V :=
  (LinearIsometryEquiv.withLpProdCongr 2 (normalLineEquiv n hn)
    (LinearIsometryEquiv.refl ℝ (Tangent n))).trans
    (ℝ ∙ n).orthogonalDecomposition.symm

/-- Unit-speed normal displacement plus a tangential vector. -/
def normalMap (n : V) (p : ℝ × Tangent n) : V :=
  p.1 • ((‖n‖⁻¹ : ℝ) • n) + (p.2 : V)

@[simp]
theorem normalEquiv_apply (n : V) (hn : n ≠ 0) (p : ℝ × Tangent n) :
    normalEquiv n hn (WithLp.toLp 2 p) = normalMap n p := by
  simp [normalEquiv, normalMap, Submodule.orthogonalDecomposition_symm_apply]

/-- Canonical product volume is transported to ambient volume by normal coordinates. -/
theorem measurePreserving_normalMap (n : V) (hn : n ≠ 0) :
    MeasurePreserving (normalMap n) (volume.prod volume) volume := by
  have h := (normalEquiv n hn).measurePreserving.comp
    (WithLp.volume_preserving_toLp ℝ (Tangent n))
  convert! h using 1

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem inner_normalMap [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (hn : n ≠ 0) (p : ℝ × Tangent n) :
    ⟪n, normalMap n p⟫_ℝ = p.1 * ‖n‖ := by
  have ht : ⟪n, (p.2 : V)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.2.property
  have hn0 : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  simp only [normalMap, inner_add_right, inner_smul_right, ht, add_zero,
    real_inner_self_eq_norm_sq]
  field_simp

/-- Translated coordinates for a hyperplane through `base`. -/
def affineMap (n base : V) (p : ℝ × Tangent n) : V :=
  base + normalMap n p

theorem measurePreserving_affineMap (n : V) (hn : n ≠ 0) (base : V) :
    MeasurePreserving (affineMap n base) (volume.prod volume) volume := by
  exact (measurePreserving_add_left volume base).comp (measurePreserving_normalMap n hn)

@[simp]
theorem inner_affineMap (n : V) (hn : n ≠ 0) (base : V) (p : ℝ × Tangent n) :
    ⟪n, affineMap n base p⟫_ℝ = ⟪n, base⟫_ℝ + p.1 * ‖n‖ := by
  simp [affineMap, inner_add_right, inner_normalMap n hn]

/-- An affine defining function is exactly normal distance times the normal length. -/
theorem affine_value (n : V) (hn : n ≠ 0) (base : V) (a : ℝ)
    (hface : ⟪n, base⟫_ℝ + a = 0) (p : ℝ × Tangent n) :
    ⟪n, affineMap n base p⟫_ℝ + a = p.1 * ‖n‖ := by
  rw [inner_affineMap n hn]
  linarith

/-- Tangent-first affine coordinates, convenient for iterated strip integrals. -/
def tangentMap (n base : V) (p : Tangent n × ℝ) : V :=
  affineMap n base (p.2, p.1)

theorem measurePreserving_tangentMap (n : V) (hn : n ≠ 0) (base : V) :
    MeasurePreserving (tangentMap n base) (volume.prod volume) volume :=
  (measurePreserving_affineMap n hn base).comp Measure.measurePreserving_swap

/-- The full normal coordinate map is a Borel embedding. -/
theorem measurableEmbedding_normalMap (n : V) (hn : n ≠ 0) :
    MeasurableEmbedding (normalMap n) := by
  have h := (normalEquiv n hn).toMeasurableEquiv.measurableEmbedding.comp
    (MeasurableEquiv.toLp 2 (ℝ × Tangent n)).measurableEmbedding
  convert! h using 1

theorem measurableEmbedding_affineMap (n : V) (hn : n ≠ 0) (base : V) :
    MeasurableEmbedding (affineMap n base) :=
  (MeasurableEquiv.addLeft base).measurableEmbedding.comp
    (measurableEmbedding_normalMap n hn)

theorem measurableEmbedding_tangentMap (n : V) (hn : n ≠ 0) (base : V) :
    MeasurableEmbedding (tangentMap n base) :=
  (measurableEmbedding_affineMap n hn base).comp
    MeasurableEquiv.prodComm.measurableEmbedding

/-- Change of variables into normal coordinates for any Bochner integrand. -/
theorem integral_tangentMap {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : V) (hn : n ≠ 0) (base : V) (f : V → G) :
    (∫ p, f (tangentMap n base p) ∂(volume.prod volume)) = ∫ x, f x :=
  (measurePreserving_tangentMap n hn base).integral_comp
    (measurableEmbedding_tangentMap n hn base) f

/-- The ambient integral is an iterated tangential/normal slice integral. -/
theorem integral_eq_iterated {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : V) (hn : n ≠ 0) (base : V) (f : V → G) (hf : Integrable f) :
    (∫ x, f x) = ∫ z : Tangent n, ∫ s : ℝ, f (base + s • ((‖n‖⁻¹ : ℝ) • n) + (z : V)) := by
  rw [← integral_tangentMap n hn base f]
  have hcomp : Integrable (fun p => f (tangentMap n base p)) (volume.prod volume) :=
    (measurePreserving_tangentMap n hn base).integrable_comp_of_integrable hf
  rw [integral_prod _ hcomp]
  simp only [tangentMap, affineMap, normalMap, add_assoc]

/-- Exact affine-algebra expansion when both normal and intercept move linearly. -/
theorem moving_affine_value (n : V) (hn : n ≠ 0) (base w : V) (a r t s : ℝ)
    (hface : ⟪n, base⟫_ℝ + a = 0) (z : Tangent n) :
    ⟪n + t • w, tangentMap n base (z, s)⟫_ℝ + (a + t * r) =
      (‖n‖ + t * ⟪w, (‖n‖⁻¹ : ℝ) • n⟫_ℝ) * s +
        t * (⟪w, base + (z : V)⟫_ℝ + r) := by
  have hnormal := affine_value n hn base a hface (s, z)
  simp only [tangentMap, inner_add_left, real_inner_smul_left]
  simp only [affineMap, normalMap, inner_add_right, inner_smul_right] at hnormal ⊢
  nlinarith [hnormal]

/-- A tilted moving halfspace becomes a variable endpoint in the normal coordinate. -/
theorem moving_halfspace_iff (n : V) (hn : n ≠ 0) (base w : V) (a r t s : ℝ)
    (hface : ⟪n, base⟫_ℝ + a = 0) (z : Tangent n)
    (hden : 0 < ‖n‖ + t * ⟪w, (‖n‖⁻¹ : ℝ) • n⟫_ℝ) :
    0 ≤ ⟪n + t • w, tangentMap n base (z, s)⟫_ℝ + (a + t * r) ↔
      -(t * (⟪w, base + (z : V)⟫_ℝ + r)) /
          (‖n‖ + t * ⟪w, (‖n‖⁻¹ : ℝ) • n⟫_ℝ) ≤ s := by
  rw [moving_affine_value n hn base w a r t s hface z, div_le_iff₀ hden]
  constructor <;> intro h <;> nlinarith

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The first-order moving-face speed is continuous at zero perturbation. -/
theorem continuousAt_moving_speed [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (hn : n ≠ 0) (base w : V)
    (r : ℝ) (z : Tangent n) :
    ContinuousAt (fun t : ℝ => -(⟪w, base + (z : V)⟫_ℝ + r) /
      (‖n‖ + t * ⟪w, (‖n‖⁻¹ : ℝ) • n⟫_ℝ)) 0 := by
  apply ContinuousAt.div continuousAt_const
  · fun_prop
  · simpa using norm_ne_zero_iff.mpr hn

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A sufficiently small tilt keeps the normal-coordinate denominator positive. -/
theorem eventually_moving_denominator_pos [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (n : V) (hn : n ≠ 0) (w : V) :
    ∀ᶠ t : ℝ in nhds 0, 0 < ‖n‖ + t * ⟪w, (‖n‖⁻¹ : ℝ) • n⟫_ℝ := by
  have hcont : ContinuousAt (fun t : ℝ => ‖n‖ + t * ⟪w, (‖n‖⁻¹ : ℝ) • n⟫_ℝ) 0 := by
    fun_prop
  exact hcont.eventually (eventually_gt_nhds (by simpa using norm_pos_iff.mpr hn))

/-- Pythagoras in normal coordinates, useful for compact-support majorants. -/
theorem norm_normalMap_sq (n : V) (hn : n ≠ 0) (p : ℝ × Tangent n) :
    ‖normalMap n p‖ ^ 2 = p.1 ^ 2 + ‖p.2‖ ^ 2 := by
  rw [← normalEquiv_apply n hn, LinearIsometryEquiv.norm_map,
    WithLp.prod_norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

/-- A point in a bounded ambient set has a bounded tangential coordinate. -/
theorem norm_tangent_le (n : V) (hn : n ≠ 0) (p : ℝ × Tangent n) :
    ‖p.2‖ ≤ ‖normalMap n p‖ := by
  rw [← normalEquiv_apply n hn, LinearIsometryEquiv.norm_map]
  exact WithLp.norm_snd_le ℝ (WithLp.toLp 2 p)

/-- A point in a bounded ambient set has a bounded normal coordinate. -/
theorem abs_normal_le (n : V) (hn : n ≠ 0) (p : ℝ × Tangent n) :
    |p.1| ≤ ‖normalMap n p‖ := by
  rw [← normalEquiv_apply n hn, LinearIsometryEquiv.norm_map]
  exact WithLp.norm_fst_le ℝ (WithLp.toLp 2 p)

end Problem358.TangentNormalCoordinates

end

noncomputable section

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace Problem358.AffinePlaneGraph

variable {X V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A nearby affine plane written as a graph in one fixed transverse direction.
The denominator is nonzero precisely when the direction remains transverse. -/
def graph (base : X → V) (u n : V) (c : ℝ) (x : X) : V :=
  base x - ((⟪n, base x⟫ + c) / ⟪n, u⟫) • u

theorem graph_eq_base (base : X → V) (u n : V) (c : ℝ)
    (hface : ∀ x, ⟪n, base x⟫ + c = 0) (x : X) :
    graph base u n c x = base x := by
  simp [graph, hface x]

theorem inner_graph_add (base : X → V) (u n : V) (c : ℝ)
    (htrans : ⟪n, u⟫ ≠ 0) (x : X) :
    ⟪n, graph base u n c x⟫ + c = 0 := by
  simp only [graph, inner_sub_right, inner_smul_right]
  field_simp
  ring

theorem projection_graph (base : X → V) (u n : V) (c : ℝ)
    (P : V → X) (hP : ∀ (x : X) (t : ℝ), P (base x + t • u) = x) (x : X) :
    P (graph base u n c x) = x := by
  simpa only [graph, sub_eq_add_neg, neg_smul] using
    hP x (-((⟪n, base x⟫ + c) / ⟪n, u⟫))

theorem projection_graph_add (base : X → V) (u n : V) (c : ℝ)
    (P : V → X) (hP : ∀ (x : X) (t : ℝ), P (base x + t • u) = x) (x : X) (t : ℝ) :
    P (graph base u n c x + t • u) = x := by
  have he : graph base u n c x + t • u =
      base x + (t - (⟪n, base x⟫ + c) / ⟪n, u⟫) • u := by
    simp only [graph, sub_smul]
    abel
  rw [he]
  exact hP x _

section Topology
theorem continuous_graph [TopologicalSpace X] (base : X → V) (hbase : Continuous base)
    (u n : V) (c : ℝ) : Continuous (graph base u n c) := by
  unfold graph
  fun_prop

theorem tendsto_graph {α : Type*} {l : Filter α}
    {base : X → V} (u : V) {n : α → V} {c : α → ℝ} {n₀ : V} {c₀ : ℝ}
    (hn : Tendsto n l (𝓝 n₀)) (hc : Tendsto c l (𝓝 c₀))
    (htrans : ⟪n₀, u⟫ ≠ 0) (x : X) :
    Tendsto (fun q => graph base u (n q) (c q) x) l
      (𝓝 (graph base u n₀ c₀ x)) := by
  unfold graph
  exact tendsto_const_nhds.sub
    (((hn.inner tendsto_const_nhds).add hc).div
      (hn.inner tendsto_const_nhds) htrans |>.smul tendsto_const_nhds)

theorem tendsto_graph_base {α : Type*} {l : Filter α}
    {base : X → V} (u : V) {n : α → V} {c : α → ℝ} {n₀ : V} {c₀ : ℝ}
    (hn : Tendsto n l (𝓝 n₀)) (hc : Tendsto c l (𝓝 c₀))
    (htrans : ⟪n₀, u⟫ ≠ 0) (hface : ∀ x, ⟪n₀, base x⟫ + c₀ = 0) (x : X) :
    Tendsto (fun q => graph base u (n q) (c q) x) l (𝓝 (base x)) := by
  simpa only [graph_eq_base base u n₀ c₀ hface] using
    tendsto_graph (base := base) u hn hc htrans x

end Topology

variable [MeasurableSpace X] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

theorem measurable_graph (base : X → V) (hbase : Measurable base)
    (u n : V) (c : ℝ) : Measurable (graph base u n c) := by
  unfold graph
  fun_prop

/-- Replacing the base plane by any transverse graph preserves the full
product disintegration. This is a fiberwise translation, so no surface
Jacobian calculation is needed. -/
theorem measurePreserving_graph_chart
    {μ : Measure X} [SFinite μ] {ρ : Measure V}
    (base : X → V) (hbase : Measurable base) (u n : V) (c : ℝ)
    (hchart : MeasurePreserving
      (fun p : X × ℝ => base p.1 + p.2 • u) (μ.prod volume) ρ) :
    MeasurePreserving
      (fun p : X × ℝ => graph base u n c p.1 + p.2 • u) (μ.prod volume) ρ := by
  let a : X → ℝ := fun x => (⟪n, base x⟫ + c) / ⟪n, u⟫
  have ha : Measurable a := by fun_prop
  have hshift : MeasurePreserving (fun p : X × ℝ => (p.1, p.2 - a p.1))
      (μ.prod volume) (μ.prod volume) := by
    apply (MeasurePreserving.id μ).skew_product
      (g := fun x t => t - a x) (μc := volume) (μd := volume)
    · exact measurable_snd.sub (ha.comp measurable_fst)
    · exact Eventually.of_forall fun x =>
        (measurePreserving_sub_right volume (a x)).map_eq
  convert hchart.comp hshift using 1
  ext p
  simp only [Function.comp_apply, graph, a, sub_smul]
  abel

end Problem358.AffinePlaneGraph

end

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Topology

namespace Problem358.TangentNormalCoordinates

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The canonical point of the affine hyperplane with normal `n` and intercept `a`. -/
def affineBase (n : V) (a : ℝ) : V := (-a / ‖n‖ ^ 2) • n

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem inner_affineBase [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (hn : n ≠ 0) (a : ℝ) :
    ⟪n, affineBase n a⟫_ℝ = -a := by
  have h : ‖n‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hn)
  simp [affineBase, inner_smul_right, h]

/-- Canonical tangential parametrization of an affine hyperplane. -/
def faceBase (n : V) (a : ℝ) (z : Tangent n) : V := affineBase n a + (z : V)

@[simp]
theorem inner_faceBase (n : V) (hn : n ≠ 0) (a : ℝ) (z : Tangent n) :
    ⟪n, faceBase n a z⟫_ℝ + a = 0 := by
  have hz : ⟪n, (z : V)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.property
  simp [faceBase, inner_add_right, inner_affineBase n hn, hz]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem continuous_faceBase [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (a : ℝ) : Continuous (faceBase n a) := by
  unfold faceBase
  fun_prop

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem faceBase_injective [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (a : ℝ) : Function.Injective (faceBase n a) := by
  intro z w h
  apply Subtype.ext
  exact add_left_cancel h

/-- Every point of the affine hyperplane occurs in the canonical parametrization. -/
theorem exists_faceBase_eq (n : V) (hn : n ≠ 0) (a : ℝ) (x : V)
    (hx : ⟪n, x⟫_ℝ + a = 0) : ∃ z : Tangent n, faceBase n a z = x := by
  have hz : x - affineBase n a ∈ Tangent n := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [inner_sub_right, inner_affineBase n hn]
    linarith
  refine ⟨⟨x - affineBase n a, hz⟩, ?_⟩
  simp [faceBase]

/-- Unit-normal displacement from the canonical hyperplane parametrization. -/
def faceChart (n : V) (a : ℝ) (p : Tangent n × ℝ) : V :=
  faceBase n a p.1 + p.2 • ((‖n‖⁻¹ : ℝ) • n)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem faceChart_eq_tangentMap [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (a : ℝ) :
    faceChart n a = tangentMap n (affineBase n a) := by
  funext p
  simp [faceChart, faceBase, tangentMap, affineMap, normalMap, add_assoc, add_comm, add_left_comm]

theorem measurePreserving_faceChart (n : V) (hn : n ≠ 0) (a : ℝ) :
    MeasurePreserving (faceChart n a) (volume.prod volume) volume := by
  rw [faceChart_eq_tangentMap]
  exact measurePreserving_tangentMap n hn _

theorem measurableEmbedding_faceChart (n : V) (hn : n ≠ 0) (a : ℝ) :
    MeasurableEmbedding (faceChart n a) := by
  rw [faceChart_eq_tangentMap]
  exact measurableEmbedding_tangentMap n hn _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem inner_unitNormal [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : V) (hn : n ≠ 0) :
    ⟪n, (‖n‖⁻¹ : ℝ) • n⟫_ℝ = ‖n‖ := by
  have h : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  simp only [inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

theorem inner_unitNormal_pos (n : V) (hn : n ≠ 0) :
    0 < ⟪n, (‖n‖⁻¹ : ℝ) • n⟫_ℝ := by
  rw [inner_unitNormal n hn]
  exact norm_pos_iff.mpr hn

end Problem358.TangentNormalCoordinates

end

end OAI
