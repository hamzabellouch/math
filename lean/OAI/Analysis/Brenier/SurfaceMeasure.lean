import OAI.Analysis.Brenier.SurfaceCoordinates

namespace OAI

/-! # Intrinsic affine-plane measure and orientation invariance

Surface measure is defined by translating canonical volume on a linear subspace.
The resulting ambient measure does not depend on the chosen basepoint in the
affine plane. In particular reversing a hyperplane equation preserves its measure.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped RealInnerProductSpace

namespace Problem358.IntrinsicSurface

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Canonical volume on a subspace, translated into the ambient space. -/
def planeMeasure (W : Submodule ℝ E) (base : E) : Measure E :=
  Measure.map (fun w : W => base + (w : E)) volume

omit [MeasurableSpace E] [BorelSpace E] in
theorem planeChart_isClosedEmbedding (W : Submodule ℝ E) (base : E) :
    Topology.IsClosedEmbedding (fun w : W => base + (w : E)) :=
  (Homeomorph.addLeft base).isClosedEmbedding.comp
    W.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal

theorem planeMeasure_apply_all (W : Submodule ℝ E) (base : E) (s : Set E) :
    planeMeasure W base s = volume {w : W | base + (w : E) ∈ s} :=
  (planeChart_isClosedEmbedding W base).measurableEmbedding.map_apply volume s

instance planeMeasure_finiteOnCompacts (W : Submodule ℝ E) (base : E) :
    IsFiniteMeasureOnCompacts (planeMeasure W base) where
  lt_top_of_isCompact {_} hK := by
    rw [planeMeasure_apply_all]
    exact ((planeChart_isClosedEmbedding W base).isCompact_preimage hK).measure_lt_top

theorem planeMeasure_setIntegral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : Submodule ℝ E) (base : E) (s : Set E) (f : E → F) :
    (∫ x in s, f x ∂planeMeasure W base) =
      ∫ w : W in {w : W | base + (w : E) ∈ s}, f (base + (w : E)) :=
  (planeChart_isClosedEmbedding W base).measurableEmbedding.setIntegral_map f s

/-- Translation of the basepoint within the plane does not change its intrinsic
measure. The equality is of ambient measures, not just of total face areas. -/
theorem planeMeasure_eq_of_sub_mem (W : Submodule ℝ E) {p q : E}
    (hpq : q - p ∈ W) : planeMeasure W q = planeMeasure W p := by
  let δ : W := ⟨q - p, hpq⟩
  have hcomp : (fun w : W => q + (w : E)) =
      (fun w : W => p + (w : E)) ∘ (fun w : W => δ + w) := by
    funext w
    change q + (w : E) = p + ((q - p) + (w : E))
    abel
  unfold planeMeasure
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    IsAddLeftInvariant.map_add_left_eq_self]

theorem planeMeasure_apply (W : Submodule ℝ E) (base : E)
    {s : Set E} (hs : MeasurableSet s) :
    planeMeasure W base s = volume {w : W | base + (w : E) ∈ s} := by
  rw [planeMeasure, Measure.map_apply (by fun_prop) hs]
  rfl

/-- Explicit basepoint-independence for a measurable face. -/
theorem face_volume_eq_of_sub_mem (W : Submodule ℝ E) {p q : E}
    (hpq : q - p ∈ W) {s : Set E} (hs : MeasurableSet s) :
    volume {w : W | q + (w : E) ∈ s} =
      volume {w : W | p + (w : E) ∈ s} := by
  rw [← planeMeasure_apply W q hs, ← planeMeasure_apply W p hs,
    planeMeasure_eq_of_sub_mem W hpq]

/-- A canonical basepoint of the affine equation `inner n x + c = 0`. -/
def normalBase (n : E) (c : ℝ) : E := (-c / ‖n‖ ^ 2) • n

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inner_normalBase {n : E} (hn : n ≠ 0) (c : ℝ) :
    ⟪n, normalBase n c⟫ = -c := by
  rw [normalBase, inner_smul_right, real_inner_self_eq_norm_sq]
  exact div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem normalBase_neg (n : E) (c : ℝ) :
    normalBase (-n) (-c) = normalBase n c := by
  simp [normalBase, neg_div, neg_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem orthogonal_span_neg (n : E) : (ℝ ∙ (-n))ᗮ = (ℝ ∙ n)ᗮ := by
  congr 1
  simpa only [Set.neg_singleton] using Submodule.span_neg (R := ℝ) ({n} : Set E)

/-- Intrinsic measure of a hyperplane, with a fixed canonical basepoint. -/
def hyperplaneMeasure (n : E) (c : ℝ) : Measure E :=
  planeMeasure (ℝ ∙ n)ᗮ (normalBase n c)

/-- Reversing the equation of a hyperplane does not change surface measure. -/
@[simp] theorem hyperplaneMeasure_neg (n : E) (c : ℝ) :
    hyperplaneMeasure (-n) (-c) = hyperplaneMeasure n c := by
  simp only [hyperplaneMeasure, orthogonal_span_neg, normalBase_neg]

/-- The canonical hyperplane measure agrees with any parametrization based at
a point of its affine equation. -/
theorem hyperplaneMeasure_eq_planeMeasure {n base : E} {c : ℝ}
    (hn : n ≠ 0) (hbase : ⟪n, base⟫ + c = 0) :
    hyperplaneMeasure n c = planeMeasure (ℝ ∙ n)ᗮ base := by
  symm
  apply planeMeasure_eq_of_sub_mem
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  rw [inner_sub_right, inner_normalBase hn]
  linarith

/-- Intrinsic tie-plane measure for a pair of affine scores. -/
def interfaceMeasure (y z : E) (a b : ℝ) : Measure E :=
  hyperplaneMeasure (y - z) (a - b)

/-- The intrinsic measure attached to a cell interface is symmetric in its labels. -/
theorem interfaceMeasure_swap (y z : E) (a b : ℝ) :
    interfaceMeasure z y b a = interfaceMeasure y z a b := by
  simpa only [interfaceMeasure, neg_sub] using hyperplaneMeasure_neg (y - z) (a - b)

/-- A concrete tie-plane chart computes the canonical interface measure. -/
theorem interfaceMeasure_eq_planeMeasure {y z base : E} {a b : ℝ}
    (hyz : y ≠ z) (htie : ⟪y, base⟫ + a = ⟪z, base⟫ + b) :
    interfaceMeasure y z a b = planeMeasure (ℝ ∙ (y - z))ᗮ base := by
  apply hyperplaneMeasure_eq_planeMeasure (sub_ne_zero.mpr hyz)
  rw [inner_sub_left]
  linarith

theorem interfaceMeasure_apply_of_tie {y z base : E} {a b : ℝ}
    (hyz : y ≠ z) (htie : ⟪y, base⟫ + a = ⟪z, base⟫ + b)
    {s : Set E} (hs : MeasurableSet s) :
    interfaceMeasure y z a b s =
      volume {w : (ℝ ∙ (y - z))ᗮ | base + (w : E) ∈ s} := by
  rw [interfaceMeasure_eq_planeMeasure hyz htie, planeMeasure_apply _ _ hs]

theorem interfaceMeasure_setIntegral_of_tie
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {y z base : E} {a b : ℝ} (hyz : y ≠ z)
    (htie : ⟪y, base⟫ + a = ⟪z, base⟫ + b) (s : Set E) (f : E → F) :
    (∫ x in s, f x ∂interfaceMeasure y z a b) =
      ∫ w : (ℝ ∙ (y - z))ᗮ in {w : (ℝ ∙ (y - z))ᗮ | base + (w : E) ∈ s}, f (base + (w : E)) := by
  rw [interfaceMeasure_eq_planeMeasure hyz htie, planeMeasure_setIntegral]

instance interfaceMeasure_finiteOnCompacts (y z : E) (a b : ℝ) :
    IsFiniteMeasureOnCompacts (interfaceMeasure y z a b) :=
  planeMeasure_finiteOnCompacts _ _

/-- Compact faces have finite intrinsic surface area. -/
theorem interfaceMeasure_lt_top (y z : E) (a b : ℝ) {s : Set E} (hs : IsCompact s) :
    interfaceMeasure y z a b s < ⊤ := hs.measure_lt_top

/-- Continuous scalar/vector/tensor weights on compact faces are integrable. -/
theorem integrableOn_interfaceMeasure
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (y z : E) (a b : ℝ) {s : Set E} (hs : IsCompact s)
    {f : E → F} (hf : ContinuousOn f s) :
    IntegrableOn f s (interfaceMeasure y z a b) := hf.integrableOn_compact hs

/-- Common-face restriction is symmetric as a measure. -/
theorem interfaceMeasure_restrict_swap (y z : E) (a b : ℝ) (s t : Set E) :
    (interfaceMeasure z y b a).restrict (t ∩ s) =
      (interfaceMeasure y z a b).restrict (s ∩ t) := by
  rw [interfaceMeasure_swap, inter_comm t s]

/-- All weighted face integrals, including first and second moments, inherit
the same symmetry. The weight need not be integrable for this equality. -/
theorem interface_integral_swap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (y z : E) (a b : ℝ) (s : Set E) (f : E → F) :
    (∫ x in s, f x ∂interfaceMeasure z y b a) =
      ∫ x in s, f x ∂interfaceMeasure y z a b := by
  rw [interfaceMeasure_swap]

/-- This is the symmetry needed for both mass and moment face coefficients,
including the source-volume and normal-length normalization. -/
theorem normalized_face_integral_swap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (y z : E) (a b M : ℝ) (s t : Set E) (f : E → F) :
    (M * ‖z - y‖)⁻¹ • (∫ x in t ∩ s, f x ∂interfaceMeasure z y b a) =
      (M * ‖y - z‖)⁻¹ • (∫ x in s ∩ t, f x ∂interfaceMeasure y z a b) := by
  rw [interfaceMeasure_swap, inter_comm t s, norm_sub_rev z y]

theorem normalized_face_area_swap (y z : E) (a b M : ℝ) (s t : Set E) :
    (interfaceMeasure z y b a (t ∩ s)).toReal / (M * ‖z - y‖) =
      (interfaceMeasure y z a b (s ∩ t)).toReal / (M * ‖y - z‖) := by
  rw [interfaceMeasure_swap, inter_comm t s, norm_sub_rev z y]

/-- Nonzero rescaling of a hyperplane equation does not alter its intrinsic measure. -/
theorem hyperplaneMeasure_smul {n : E} (hn : n ≠ 0) (c : ℝ)
    {r : ℝ} (hr : r ≠ 0) :
    hyperplaneMeasure (r • n) (r * c) = hyperplaneMeasure n c := by
  rw [hyperplaneMeasure_eq_planeMeasure (smul_ne_zero hr hn)
    (base := normalBase n c) (by
      rw [real_inner_smul_left, inner_normalBase hn]
      ring)]
  rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hr)]
  rfl

/-- Intrinsic hyperplane measure is concentrated on its defining affine equation. -/
theorem ae_hyperplane_equation {n : E} (hn : n ≠ 0) (c : ℝ) :
    ∀ᵐ x ∂hyperplaneMeasure n c, ⟪n, x⟫ + c = 0 := by
  change ∀ᵐ x ∂Measure.map (fun w : (ℝ ∙ n)ᗮ => normalBase n c + (w : E)) volume,
    ⟪n, x⟫ + c = 0
  rw [(planeChart_isClosedEmbedding (ℝ ∙ n)ᗮ (normalBase n c)).measurableEmbedding.ae_map_iff]
  exact Filter.Eventually.of_forall fun w => by
    rw [inner_add_right, inner_normalBase hn,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property]
    ring

/-- Almost every point for a genuine interface measure satisfies the affine tie. -/
theorem ae_interface_tie {y z : E} (hyz : y ≠ z) (a b : ℝ) :
    ∀ᵐ x ∂interfaceMeasure y z a b, ⟪x, y⟫ + a = ⟪x, z⟫ + b := by
  filter_upwards [ae_hyperplane_equation (sub_ne_zero.mpr hyz) (a - b)] with x hx
  rw [inner_sub_left] at hx
  linarith [real_inner_comm x y, real_inner_comm x z]

/-- Restricting intrinsic interface measure to the tie equation is redundant. -/
theorem interfaceMeasure_restrict_tie {y z : E} (hyz : y ≠ z) (a b : ℝ) :
    (interfaceMeasure y z a b).restrict {x | ⟪x, y⟫ + a = ⟪x, z⟫ + b} =
      interfaceMeasure y z a b :=
  Measure.restrict_eq_self_of_ae_mem (ae_interface_tie hyz a b)

end Problem358.IntrinsicSurface

end

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace Problem358.TransverseSurface

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Height on an affine plane, measured along a fixed transverse direction. -/
def height (n u : V) (c : ℝ) (x : V) : ℝ := (⟪n, x⟫ + c) / ⟪n, u⟫

/-- Retraction onto an affine plane along the transverse direction. -/
def retract (n u : V) (c : ℝ) (x : V) : V := x - height n u c x • u

lemma height_add_transverse {n u b : V} {c : ℝ}
    (ha : ⟪n, u⟫ ≠ 0) (hb : ⟪n, b⟫ + c = 0) (t : ℝ) :
    height n u c (b + t • u) = t := by
  unfold height
  rw [inner_add_right, inner_smul_right]
  apply (div_eq_iff ha).mpr
  linarith

lemma retract_add_transverse {n u b : V} {c : ℝ}
    (ha : ⟪n, u⟫ ≠ 0) (hb : ⟪n, b⟫ + c = 0) (t : ℝ) :
    retract n u c (b + t • u) = b := by
  rw [retract, height_add_transverse ha hb]
  simp

variable [MeasurableSpace V] [BorelSpace V]

/-- A full product disintegration determines its plane measure by applying the
common retraction and height. No surface Jacobian theorem is assumed. -/
theorem map_retract_height_eq_prod
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {ρ : Measure V} {n u : V} {c : ℝ} (ha : ⟪n, u⟫ ≠ 0)
    (base : X → V) (hbase : Measurable base)
    (hplane : ∀ x, ⟪n, base x⟫ + c = 0)
    (hchart : MeasurePreserving (fun p : X × ℝ => base p.1 + p.2 • u)
      (μ.prod volume) ρ) :
    Measure.map (fun x => (retract n u c x, height n u c x)) ρ =
      (Measure.map base μ).prod volume := by
  have hm : Measurable (fun x => (retract n u c x, height n u c x)) := by
    unfold retract height
    fun_prop
  rw [← hchart.map_eq, Measure.map_map hm hchart.measurable]
  have he : (fun x => (retract n u c x, height n u c x)) ∘
      (fun p : X × ℝ => base p.1 + p.2 • u) = Prod.map base id := by
    funext p
    exact Prod.ext (retract_add_transverse ha (hplane p.1) p.2)
      (height_add_transverse ha (hplane p.1) p.2)
  rw [he, ← Measure.map_prod_map μ volume hbase measurable_id, Measure.map_id]

/-- Two volume disintegrations along the same transverse direction have exactly
the same base measure. The proof cancels the real factor on a unit interval. -/
theorem map_base_eq_of_charts
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {ρ : Measure V} {n u : V} {c : ℝ} (ha : ⟪n, u⟫ ≠ 0)
    (base : X → V) (other : Y → V)
    (hb : Measurable base) (ho : Measurable other)
    (hbp : ∀ x, ⟪n, base x⟫ + c = 0)
    (hop : ∀ y, ⟪n, other y⟫ + c = 0)
    (hbc : MeasurePreserving (fun p : X × ℝ => base p.1 + p.2 • u)
      (μ.prod volume) ρ)
    (hoc : MeasurePreserving (fun p : Y × ℝ => other p.1 + p.2 • u)
      (ν.prod volume) ρ) :
    Measure.map base μ = Measure.map other ν := by
  have hp := (map_retract_height_eq_prod ha base hb hbp hbc).symm.trans
    (map_retract_height_eq_prod ha other ho hop hoc)
  ext s hs
  have h := congrArg (fun m : Measure (V × ℝ) => m (s ×ˢ Ioc (0 : ℝ) 1)) hp
  simpa only [Measure.prod_prod, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one,
    mul_one] using h

variable [FiniteDimensional ℝ V]

private theorem measurePreserving_tangent_shear (n : V)
    (w : TangentNormalCoordinates.Tangent n) (a : ℝ) :
    MeasurePreserving
      (fun p : TangentNormalCoordinates.Tangent n × ℝ =>
        (p.1 + (p.2 / a) • w, p.2))
      (volume.prod volume) (volume.prod volume) := by
  have hs : MeasurePreserving
      (fun p : ℝ × TangentNormalCoordinates.Tangent n =>
        (p.1, p.2 + (p.1 / a) • w))
      (volume.prod volume) (volume.prod volume) := by
    apply (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun t y => y + (t / a) • w)
    · fun_prop
    · exact Filter.Eventually.of_forall fun t =>
        (measurePreserving_add_right volume ((t / a) • w)).map_eq
  exact Measure.measurePreserving_swap.comp (hs.comp Measure.measurePreserving_swap)

/-- Intrinsic tangent volume, multiplied by the transverse cosine, gives the
full ambient-volume disintegration along an arbitrary non-tangential vector.
This is proved by a tangential shear and one-dimensional scaling only. -/
theorem measurePreserving_oblique_chart (n u b : V)
    (hn : n ≠ 0) (hu : ⟪n, u⟫ ≠ 0) :
    MeasurePreserving
      (fun p : TangentNormalCoordinates.Tangent n × ℝ => b + (p.1 : V) + p.2 • u)
      ((ENNReal.ofReal |⟪n, u⟫ / ‖n‖| • volume).prod volume) volume := by
  let a : ℝ := ⟪n, u⟫ / ‖n‖
  let v : V := (‖n‖⁻¹ : ℝ) • n
  have hn' : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have ha : a ≠ 0 := div_ne_zero hu hn'
  have hv : ⟪n, v⟫ = ‖n‖ := by
    dsimp [v]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hw : u - a • v ∈ TangentNormalCoordinates.Tangent n := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [inner_sub_right, inner_smul_right, hv]
    dsimp [a]
    rw [div_mul_cancel₀ _ hn', sub_self]
  let w : TangentNormalCoordinates.Tangent n := ⟨u - a • v, hw⟩
  have hscale : MeasurePreserving (fun t : ℝ => a * t)
      (ENNReal.ofReal |a| • volume) volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_smul _ (by fun_prop)]
    exact Real.smul_map_volume_mul_left ha
  have hp := (MeasurePreserving.id
    (volume : Measure (TangentNormalCoordinates.Tangent n))).prod hscale
  have hcomp := (TangentNormalCoordinates.measurePreserving_tangentMap n hn b).comp
    ((measurePreserving_tangent_shear n w a).comp hp)
  have he : (TangentNormalCoordinates.tangentMap n b) ∘
      (fun p : TangentNormalCoordinates.Tangent n × ℝ =>
        (p.1 + (p.2 / a) • w, p.2)) ∘ Prod.map id (fun t : ℝ => a * t) =
      (fun p : TangentNormalCoordinates.Tangent n × ℝ => b + (p.1 : V) + p.2 • u) := by
    funext p
    simp only [Function.comp_apply,
      TangentNormalCoordinates.tangentMap, TangentNormalCoordinates.affineMap,
      TangentNormalCoordinates.normalMap, Submodule.coe_add, Submodule.coe_smul]
    change b + ((a * p.2) • v + ((p.1 : V) + ((a * p.2) / a) • (u - a • v))) = _
    rw [mul_div_cancel_left₀ p.2 ha]
    module
  rw [he] at hcomp
  simpa only [Measure.prod_smul_left, Measure.prod_smul_right, a] using hcomp

/-- Exact intrinsic surface Jacobian for any product-preserving transverse
chart. This holds for arbitrary measurable base parameterizations. -/
theorem map_base_eq_smul_hyperplaneMeasure
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {n u : V} {c : ℝ} (hn : n ≠ 0) (hu : ⟪n, u⟫ ≠ 0)
    (base : X → V) (hb : Measurable base)
    (hplane : ∀ x, ⟪n, base x⟫ + c = 0)
    (hchart : MeasurePreserving (fun p : X × ℝ => base p.1 + p.2 • u)
      (μ.prod volume) volume) :
    Measure.map base μ = ENNReal.ofReal |⟪n, u⟫ / ‖n‖| •
      IntrinsicSurface.hyperplaneMeasure n c := by
  let b : V := IntrinsicSurface.normalBase n c
  have hbplane : ⟪n, b⟫ + c = 0 := by
    rw [IntrinsicSurface.inner_normalBase hn]
    ring
  have hp := map_base_eq_of_charts (ρ := volume) hu base
    (fun w : TangentNormalCoordinates.Tangent n => b + (w : V)) hb (by fun_prop)
    hplane (fun w => by
      rw [inner_add_right,
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property]
      simpa using hbplane)
    hchart (measurePreserving_oblique_chart n u b hn hu)
  rw [Measure.map_smul _ (by fun_prop)] at hp
  exact hp

/-- Equality of positively oriented normalized face integrals. The theorem
includes vector-valued weights and needs neither compact cells nor positivity
of their volumes. -/
theorem normalized_integral_eq_intrinsic
    {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure X} [SFinite μ] {n u : V} {c : ℝ}
    (hn : n ≠ 0) (hu : 0 < ⟪n, u⟫)
    (base : X → V) (hb : Measurable base)
    (hplane : ∀ x, ⟪n, base x⟫ + c = 0)
    (hchart : MeasurePreserving (fun p : X × ℝ => base p.1 + p.2 • u)
      (μ.prod volume) volume)
    (f : V → F) (hf : StronglyMeasurable f) :
    ⟪n, u⟫⁻¹ • (∫ x, f (base x) ∂μ) =
      ‖n‖⁻¹ • (∫ x, f x ∂IntrinsicSurface.hyperplaneMeasure n c) := by
  rw [← integral_map hb.aemeasurable hf.aestronglyMeasurable,
    map_base_eq_smul_hyperplaneMeasure hn hu.ne' base hb hplane hchart,
    integral_smul_measure]
  rw [ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (div_pos hu (norm_pos_iff.mpr hn)), smul_smul]
  congr 1
  field_simp

end Problem358.TransverseSurface

end

end OAI
