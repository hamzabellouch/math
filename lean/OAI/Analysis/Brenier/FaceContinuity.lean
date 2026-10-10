import OAI.Analysis.Brenier.Interfaces
import OAI.Analysis.Brenier.SurfaceMeasure

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace Problem358.MovingCellTrace

/-- Weighted face coefficients vary continuously for positive affine cells,
expressed in any nearby-plane chart preserving a fixed transverse projection.
The compact source supplies domination; positivity supplies all surface nullity. -/
theorem tendsto_positive_cell_face_integral
    {d : ℕ} {ι α : Type*} [Fintype ι] {l : Filter α} [l.IsCountablyGenerated]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d} (hz : z ∈ interior K)
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ)) [μ.IsAddHaarMeasure]
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    {P : E d → (ℝ ∙ (y i - y j))ᗮ} (hP : Continuous P)
    {chart : α → ((ℝ ∙ (y i - y j))ᗮ) → E d}
    (hproject : ∀ q p, P (chart q p) = p)
    (hchartmeas : ∀ q, Measurable (chart q))
    (hchartlim : ∀ᵐ p : (ℝ ∙ (y i - y j))ᗮ ∂μ,
      Tendsto (fun q => chart q p) l (𝓝 (z + (p : E d))))
    {w : E d → ℝ} (hwmeas : Measurable w) (hwcont : ContinuousOn w K)
    {a : α → ι → E d} {b : α → ι → ℝ}
    (ha : ∀ k ∈ J, Tendsto (fun q => a q k) l (𝓝 (y i - y k)))
    (hb : ∀ k ∈ J, Tendsto (fun q => b q k) l (𝓝 (c i - c k))) :
    Tendsto (fun q => ∫ p, K.indicator w (chart q p) * ∏ k ∈ J,
      cutIndicator (⟪chart q p, a q k⟫ + b q k) ∂μ) l
      (𝓝 (∫ p, K.indicator w (z + (p : E d)) * ∏ k ∈ J,
        cutIndicator (⟪z + (p : E d), y i - y k⟫ + (c i - c k)) ∂μ)) := by
  refine tendsto_integral_remainder_of_compact_projection
    (α := α) (X := (ℝ ∙ (y i - y j))ᗮ) (V := E d) (l := l) (μ := μ)
    (s := fun q v k => ⟪v, a q k⟫ + b q k)
    (b := fun p k => ⟪z + (p : E d), y i - y k⟫ + (c i - c k))
    J hK hP hproject hchartmeas hchartlim hwmeas hwcont ?_ ?_ ?_
  · intro q k _
    exact (continuous_id.inner continuous_const).measurable.add measurable_const
  · filter_upwards [hchartlim] with p hp
    intro k hk
    exact (hp.inner (ha k hk)).add (hb k hk)
  · filter_upwards [CellGeometry.ae_regular_interface hρ hK.isClosed hconv y c hy
      hpos hij hz htie μ] with p hp
    refine ⟨hp.1, ?_⟩
    intro k hk heq
    apply hp.2 k (hJ k hk).1 (hJ k hk).2
    rw [inner_sub_right] at heq
    linarith

end Problem358.MovingCellTrace

end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Problem358.AffinePlaneGraph

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Unit transverse vector of a nonzero reference normal. -/
def unitNormal (n : E d) : E d := ‖n‖⁻¹ • n

lemma inner_unitNormal (n : E d) (hn : n ≠ 0) :
    ⟪n, unitNormal n⟫ = ‖n‖ := by
  rw [unitNormal, inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

/-- Fixed tangential coordinates relative to a chosen point of the reference plane. -/
def tangentProjection (n z : E d) : E d → (ℝ ∙ n)ᗮ :=
  fun x => (ℝ ∙ n)ᗮ.orthogonalProjectionOnto (x - z)

lemma continuous_tangentProjection (n z : E d) :
    Continuous (tangentProjection n z) :=
  (ℝ ∙ n)ᗮ.orthogonalProjectionOnto.continuous.comp (continuous_id.sub continuous_const)

lemma tangentProjection_add (n z : E d) (x : (ℝ ∙ n)ᗮ) (t : ℝ) :
    tangentProjection n z (z + (x : E d) + t • unitNormal n) = x := by
  have he : z + (x : E d) + t • unitNormal n - z =
      (x : E d) + t • unitNormal n := by abel
  unfold tangentProjection
  rw [he]
  simp only [map_add, map_smul,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, unitNormal,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
    smul_zero, add_zero]

/-- Reference-normal graph coordinates for a varying selected interface. -/
def interfaceGraph (n₀ z : E d) (a : ι → E d) (b : ι → ℝ) (i j : ι) :
    (ℝ ∙ n₀)ᗮ → E d :=
  graph (fun x => z + (x : E d)) (unitNormal n₀) (a i - a j) (b i - b j)

/-- A transverse face coefficient; the fixed-plane measure and transverse
normal factor together are the disintegration coefficient in cell derivatives. -/
def faceCoefficient (K : Set (E d)) (n₀ z : E d) (J : Finset ι)
    (i j : ι) (w : E d → ℝ) (p : (ι → E d) × (ι → ℝ)) : ℝ :=
  (∫ x : (ℝ ∙ n₀)ᗮ,
    K.indicator w (interfaceGraph n₀ z p.1 p.2 i j x) *
      ∏ k ∈ J, MovingCellTrace.cutIndicator
        (⟪interfaceGraph n₀ z p.1 p.2 i j x, p.1 i - p.1 k⟫ +
          (p.2 i - p.2 k))) /
    ⟪p.1 i - p.1 j, unitNormal n₀⟫

/-- Continuity of actual weighted positive-cell face coefficients, with the
nearby charts, compact domination, and surface nullity all furnished internally.
Only the reference configuration needs positive cells. -/
theorem tendsto_faceCoefficient
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d} (hz : z ∈ interior K)
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j)
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    {w : E d → ℝ} (hw : Continuous w)
    {a : α → ι → E d} {b : α → ι → ℝ}
    (ha : ∀ k, Tendsto (fun q => a q k) l (𝓝 (y k)))
    (hb : ∀ k, Tendsto (fun q => b q k) l (𝓝 (c k))) :
    Tendsto (fun q => faceCoefficient K (y i - y j) z J i j w (a q, b q)) l
      (𝓝 (faceCoefficient K (y i - y j) z J i j w (y, c))) := by
  let n₀ := y i - y j
  let base : (ℝ ∙ n₀)ᗮ → E d := fun x => z + (x : E d)
  have hn : n₀ ≠ 0 := sub_ne_zero.mpr (hy.ne hij)
  have htrans : ⟪n₀, unitNormal n₀⟫ ≠ 0 := by
    rw [inner_unitNormal n₀ hn]
    exact norm_ne_zero_iff.mpr hn
  have hface : ∀ x : (ℝ ∙ n₀)ᗮ, ⟪n₀, base x⟫ + (c i - c j) = 0 := by
    intro x
    have hx : ⟪n₀, (x : E d)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
    simp only [base, inner_add_right, hx, add_zero, n₀, inner_sub_left]
    rw [real_inner_comm z (y i), real_inner_comm z (y j)]
    linarith
  have hlim : ∀ᵐ x : (ℝ ∙ n₀)ᗮ ∂volume,
      Tendsto (fun q => interfaceGraph n₀ z (a q) (b q) i j x) l (𝓝 (base x)) := by
    exact Eventually.of_forall fun x =>
      tendsto_graph_base (unitNormal n₀) ((ha i).sub (ha j))
        ((hb i).sub (hb j)) htrans hface x
  have hi := MovingCellTrace.tendsto_positive_cell_face_integral
    hρ hK hconv y c hy hpos hij hz htie volume J hJ
    (continuous_tangentProjection n₀ z)
    (fun q x => projection_graph base (unitNormal n₀) (a q i - a q j)
      (b q i - b q j) (tangentProjection n₀ z) (tangentProjection_add n₀ z) x)
    (fun q => measurable_graph base (by fun_prop) (unitNormal n₀)
      (a q i - a q j) (b q i - b q j))
    hlim hw.measurable hw.continuousOn
    (fun k _ => (ha i).sub (ha k)) (fun k _ => (hb i).sub (hb k))
  have hden : Tendsto (fun q => ⟪a q i - a q j, unitNormal n₀⟫) l
      (𝓝 ⟪n₀, unitNormal n₀⟫) :=
    ((ha i).sub (ha j)).inner tendsto_const_nhds
  have heq : ∀ x, interfaceGraph n₀ z y c i j x = base x :=
    graph_eq_base base (unitNormal n₀) n₀ (c i - c j) hface
  change Tendsto (fun q => faceCoefficient K n₀ z J i j w (a q, b q)) l
    (𝓝 (faceCoefficient K n₀ z J i j w (y, c)))
  simp only [faceCoefficient, heq]
  exact hi.div hden htrans

/-- Local continuity on the full joint site/intercept parameter space. -/
theorem continuousAt_faceCoefficient
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d} (hz : z ∈ interior K)
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j)
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    {w : E d → ℝ} (hw : Continuous w) :
    ContinuousAt (faceCoefficient K (y i - y j) z J i j w) (y, c) := by
  exact tendsto_faceCoefficient hρ hK hconv y c hy hpos hij hz htie J hJ hw
    (fun k => (continuous_apply k |>.comp continuous_fst).tendsto (y, c))
    (fun k => (continuous_apply k |>.comp continuous_snd).tendsto (y, c))

end Problem358.AffinePlaneGraph

end

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace Problem358.MovingCellTrace

/-- Weighted face coefficients vary continuously for positive affine cells,
expressed in any nearby-plane chart preserving a fixed transverse projection.
The compact source supplies domination; positivity supplies all surface nullity. -/
theorem tendsto_positive_cell_face_integral_of_tie
    {d : ℕ} {ι α : Type*} [Fintype ι] {l : Filter α} [l.IsCountablyGenerated]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d}
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ)) [μ.IsAddHaarMeasure]
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    {P : E d → (ℝ ∙ (y i - y j))ᗮ} (hP : Continuous P)
    {chart : α → ((ℝ ∙ (y i - y j))ᗮ) → E d}
    (hproject : ∀ q p, P (chart q p) = p)
    (hchartmeas : ∀ q, Measurable (chart q))
    (hchartlim : ∀ᵐ p : (ℝ ∙ (y i - y j))ᗮ ∂μ,
      Tendsto (fun q => chart q p) l (𝓝 (z + (p : E d))))
    {w : E d → ℝ} (hwmeas : Measurable w) (hwcont : ContinuousOn w K)
    {a : α → ι → E d} {b : α → ι → ℝ}
    (ha : ∀ k ∈ J, Tendsto (fun q => a q k) l (𝓝 (y i - y k)))
    (hb : ∀ k ∈ J, Tendsto (fun q => b q k) l (𝓝 (c i - c k))) :
    Tendsto (fun q => ∫ p, K.indicator w (chart q p) * ∏ k ∈ J,
      cutIndicator (⟪chart q p, a q k⟫ + b q k) ∂μ) l
      (𝓝 (∫ p, K.indicator w (z + (p : E d)) * ∏ k ∈ J,
        cutIndicator (⟪z + (p : E d), y i - y k⟫ + (c i - c k)) ∂μ)) := by
  refine tendsto_integral_remainder_of_compact_projection
    (α := α) (X := (ℝ ∙ (y i - y j))ᗮ) (V := E d) (l := l) (μ := μ)
    (s := fun q v k => ⟪v, a q k⟫ + b q k)
    (b := fun p k => ⟪z + (p : E d), y i - y k⟫ + (c i - c k))
    J hK hP hproject hchartmeas hchartlim hwmeas hwcont ?_ ?_ ?_
  · intro q k _
    exact (continuous_id.inner continuous_const).measurable.add measurable_const
  · filter_upwards [hchartlim] with p hp
    intro k hk
    exact (hp.inner (ha k hk)).add (hb k hk)
  · filter_upwards [CellGeometry.ae_regular_interface_of_tie hρ hK.isClosed hconv y c hy
      hpos hij htie μ] with p hp
    refine ⟨hp.1, ?_⟩
    intro k hk heq
    apply hp.2 k (hJ k hk).1 (hJ k hk).2
    rw [inner_sub_right] at heq
    linarith

end Problem358.MovingCellTrace

namespace Problem358.AffinePlaneGraph

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Continuity of actual weighted positive-cell face coefficients, with the
nearby charts, compact domination, and surface nullity all furnished internally.
Only the reference configuration needs positive cells. -/
theorem tendsto_faceCoefficient_of_tie
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d}
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j)
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    {w : E d → ℝ} (hw : Continuous w)
    {a : α → ι → E d} {b : α → ι → ℝ}
    (ha : ∀ k, Tendsto (fun q => a q k) l (𝓝 (y k)))
    (hb : ∀ k, Tendsto (fun q => b q k) l (𝓝 (c k))) :
    Tendsto (fun q => faceCoefficient K (y i - y j) z J i j w (a q, b q)) l
      (𝓝 (faceCoefficient K (y i - y j) z J i j w (y, c))) := by
  let n₀ := y i - y j
  let base : (ℝ ∙ n₀)ᗮ → E d := fun x => z + (x : E d)
  have hn : n₀ ≠ 0 := sub_ne_zero.mpr (hy.ne hij)
  have htrans : ⟪n₀, unitNormal n₀⟫ ≠ 0 := by
    rw [inner_unitNormal n₀ hn]
    exact norm_ne_zero_iff.mpr hn
  have hface : ∀ x : (ℝ ∙ n₀)ᗮ, ⟪n₀, base x⟫ + (c i - c j) = 0 := by
    intro x
    have hx : ⟪n₀, (x : E d)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
    simp only [base, inner_add_right, hx, add_zero, n₀, inner_sub_left]
    rw [real_inner_comm z (y i), real_inner_comm z (y j)]
    linarith
  have hlim : ∀ᵐ x : (ℝ ∙ n₀)ᗮ ∂volume,
      Tendsto (fun q => interfaceGraph n₀ z (a q) (b q) i j x) l (𝓝 (base x)) := by
    exact Eventually.of_forall fun x =>
      tendsto_graph_base (unitNormal n₀) ((ha i).sub (ha j))
        ((hb i).sub (hb j)) htrans hface x
  have hi := MovingCellTrace.tendsto_positive_cell_face_integral_of_tie
    hρ hK hconv y c hy hpos hij htie volume J hJ
    (continuous_tangentProjection n₀ z)
    (fun q x => projection_graph base (unitNormal n₀) (a q i - a q j)
      (b q i - b q j) (tangentProjection n₀ z) (tangentProjection_add n₀ z) x)
    (fun q => measurable_graph base (by fun_prop) (unitNormal n₀)
      (a q i - a q j) (b q i - b q j))
    hlim hw.measurable hw.continuousOn
    (fun k _ => (ha i).sub (ha k)) (fun k _ => (hb i).sub (hb k))
  have hden : Tendsto (fun q => ⟪a q i - a q j, unitNormal n₀⟫) l
      (𝓝 ⟪n₀, unitNormal n₀⟫) :=
    ((ha i).sub (ha j)).inner tendsto_const_nhds
  have heq : ∀ x, interfaceGraph n₀ z y c i j x = base x :=
    graph_eq_base base (unitNormal n₀) n₀ (c i - c j) hface
  change Tendsto (fun q => faceCoefficient K n₀ z J i j w (a q, b q)) l
    (𝓝 (faceCoefficient K n₀ z J i j w (y, c)))
  simp only [faceCoefficient, heq]
  exact hi.div hden htrans

/-- Local continuity on the full joint site/intercept parameter space. -/
theorem continuousAt_faceCoefficient_of_tie
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d}
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j)
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    {w : E d → ℝ} (hw : Continuous w) :
    ContinuousAt (faceCoefficient K (y i - y j) z J i j w) (y, c) := by
  exact tendsto_faceCoefficient_of_tie hρ hK hconv y c hy hpos hij htie J hJ hw
    (fun k => (continuous_apply k |>.comp continuous_fst).tendsto (y, c))
    (fun k => (continuous_apply k |>.comp continuous_snd).tendsto (y, c))

end Problem358.AffinePlaneGraph

end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Problem358.AffinePlaneGraph

variable {d : ℕ} {ι : Type*}

/-- The normalized intrinsic integral over an interface with additional affine
cuts. Unlike the local `faceCoefficient`, this definition uses no reference
normal or basepoint. -/
def intrinsicCutCoefficient (K : Set (E d)) (J : Finset ι) (i j : ι)
    (w : E d → ℝ) (p : (ι → E d) × (ι → ℝ)) : ℝ :=
  (∫ x, K.indicator w x * ∏ k ∈ J, MovingCellTrace.cutIndicator
    (⟪x, p.1 i - p.1 k⟫ + (p.2 i - p.2 k))
    ∂IntrinsicSurface.hyperplaneMeasure (p.1 i - p.1 j) (p.2 i - p.2 j)) /
      ‖p.1 i - p.1 j‖

/-- The fixed transverse coefficient equals the intrinsic coefficient throughout
the neighborhood where the transverse orientation stays positive. -/
theorem faceCoefficient_eq_intrinsicCutCoefficient
    {K : Set (E d)} (hK : MeasurableSet K) (n₀ z : E d) (hn₀ : n₀ ≠ 0)
    (J : Finset ι) (i j : ι) (w : E d → ℝ) (hw : Measurable w)
    (p : (ι → E d) × (ι → ℝ))
    (htrans : 0 < ⟪p.1 i - p.1 j, unitNormal n₀⟫) :
    faceCoefficient K n₀ z J i j w p = intrinsicCutCoefficient K J i j w p := by
  let n := p.1 i - p.1 j
  let c := p.2 i - p.2 j
  let base : (ℝ ∙ n₀)ᗮ → E d := fun x => z + (x : E d)
  have hn : n ≠ 0 := by
    intro he
    have he' : ⟪n, unitNormal n₀⟫ = 0 := by rw [he, inner_zero_left]
    exact (ne_of_gt htrans) he'
  have hbase : Measurable base := by fun_prop
  have hchart₀ : MeasurePreserving
      (fun q : (ℝ ∙ n₀)ᗮ × ℝ => base q.1 + q.2 • unitNormal n₀)
      (volume.prod volume) volume := by
    convert TangentNormalCoordinates.measurePreserving_tangentMap n₀ hn₀ z using 1
    funext q
    simp only [base, unitNormal, TangentNormalCoordinates.tangentMap,
      TangentNormalCoordinates.affineMap, TangentNormalCoordinates.normalMap]
    abel
  have hchart := measurePreserving_graph_chart base hbase (unitNormal n₀) n c hchart₀
  let f : E d → ℝ := fun x => K.indicator w x * ∏ k ∈ J,
    MovingCellTrace.cutIndicator (⟪x, p.1 i - p.1 k⟫ + (p.2 i - p.2 k))
  have hf : Measurable f := MovingCellTrace.measurable_remainder J hK hw
    (fun _ _ => by fun_prop)
  have he := TransverseSurface.normalized_integral_eq_intrinsic hn htrans
    (graph base (unitNormal n₀) n c) (measurable_graph base hbase _ _ _)
    (inner_graph_add base (unitNormal n₀) n c htrans.ne') hchart f hf.stronglyMeasurable
  change (∫ x : (ℝ ∙ n₀)ᗮ, f (graph base (unitNormal n₀) n c x)) /
      ⟪n, unitNormal n₀⟫ =
    (∫ x, f x ∂IntrinsicSurface.hyperplaneMeasure n c) / ‖n‖
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using he

/-- Actual intrinsic face coefficients are continuous in all sites and
intercepts at each positive-cell configuration. No choice of a moving frame,
Jacobian, exceptional set, or local derivative field is left as a hypothesis. -/
theorem continuousAt_intrinsicCutCoefficient [Fintype ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j)
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    {w : E d → ℝ} (hw : Continuous w) :
    ContinuousAt (intrinsicCutCoefficient K J i j w) (y, c) := by
  let n₀ := y i - y j
  let z := IntrinsicSurface.normalBase n₀ (c i - c j)
  have hn : n₀ ≠ 0 := sub_ne_zero.mpr (hy.ne hij)
  have htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j := by
    have he := IntrinsicSurface.inner_normalBase hn (c i - c j)
    change ⟪n₀, z⟫ = -(c i - c j) at he
    dsimp [n₀] at he
    rw [inner_sub_left, real_inner_comm z (y i), real_inner_comm z (y j)] at he
    linarith
  have hc := continuousAt_faceCoefficient_of_tie hρ hK hconv y c hy hpos hij
    htie J hJ hw
  have hden : ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      ⟪p.1 i - p.1 j, unitNormal n₀⟫) (y, c) := by fun_prop
  have htrans : 0 < ⟪n₀, unitNormal n₀⟫ := by
    rw [inner_unitNormal n₀ hn]
    exact norm_pos_iff.mpr hn
  apply hc.congr_of_eventuallyEq
  filter_upwards [hden.eventually (eventually_gt_nhds htrans)] with p hp
  exact (faceCoefficient_eq_intrinsicCutCoefficient hK.measurableSet n₀ z hn
    J i j w hw.measurable p hp).symm

end Problem358.AffinePlaneGraph

end

end OAI
