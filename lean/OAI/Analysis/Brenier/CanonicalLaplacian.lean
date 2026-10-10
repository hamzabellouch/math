import OAI.Analysis.Brenier.CellContinuity
import OAI.Analysis.Brenier.CellFaces
import OAI.Analysis.Brenier.FaceContinuity
import OAI.Analysis.Brenier.FacetConnectivity
import OAI.Analysis.Brenier.Laplacian

namespace OAI

/-! The normalized cell Laplacian with its actual intrinsic geometric weights.

All graph hypotheses in the algebraic inverse theorem are discharged here for
positive-mass convex affine cells. No analytic differentiability assertion is
made: the resulting equivalence is ready to identify with the mass Jacobian.
-/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace BigOperators

namespace Problem358.PositiveFacet

variable {d : ℕ} {ι : Type*}

/-- Canonical normalized intrinsic area of the common closed cell face. -/
def canonicalFaceWeight (K : Set (E d)) (y : ι → E d) (c : ι → ℝ)
    (i j : ι) : ℝ :=
  (IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)
    (CellGeometry.closedCell K y c i ∩ CellGeometry.closedCell K y c j)).toReal /
      ((volume K).toReal * ‖y i - y j‖)

theorem canonicalFaceWeight_symm (K : Set (E d)) (y : ι → E d)
    (c : ι → ℝ) (i j : ι) :
    canonicalFaceWeight K y c i j = canonicalFaceWeight K y c j i := by
  exact (IntrinsicSurface.normalized_face_area_swap (y i) (y j) (c i) (c j)
    (volume K).toReal (CellGeometry.closedCell K y c i)
    (CellGeometry.closedCell K y c j)).symm

theorem canonicalFaceWeight_nonneg (K : Set (E d)) (y : ι → E d)
    (c : ι → ℝ) (i j : ι) : 0 ≤ canonicalFaceWeight K y c i j :=
  div_nonneg ENNReal.toReal_nonneg (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _))

@[simp] theorem canonicalFaceWeight_self (K : Set (E d)) (y : ι → E d)
    (c : ι → ℝ) (i : ι) : canonicalFaceWeight K y c i i = 0 := by
  simp [canonicalFaceWeight]

/-- An arbitrary tie-plane chart computes the canonical coefficient. -/
theorem canonicalFaceWeight_eq_chart [Finite ι]
    (K : Set (E d)) (hK : IsCompact K) (y : ι → E d) (c : ι → ℝ)
    {i j : ι} (hy : y i ≠ y j) (base : E d)
    (hbase : TripleCell.score (y i) (c i) base = TripleCell.score (y j) (c j) base) :
    canonicalFaceWeight K y c i j =
      (volume (surfaceFace K y c i j base)).toReal /
        ((volume K).toReal * ‖y i - y j‖) := by
  have hb : ⟪y i, base⟫_ℝ + c i = ⟪y j, base⟫_ℝ + c j := by
    rw [real_inner_comm base (y i), real_inner_comm base (y j)]
    exact hbase
  have hs : MeasurableSet
      (CellGeometry.closedCell K y c i ∩ CellGeometry.closedCell K y c j) :=
    ((CellGeometry.isClosed_closedCell hK.isClosed y c i).inter
      (CellGeometry.isClosed_closedCell hK.isClosed y c j)).measurableSet
  unfold canonicalFaceWeight
  rw [IntrinsicSurface.interfaceMeasure_apply_of_tie hy hb hs,
    surfaceFace_eq_preimage_closedCells]
  rfl

/-- Every strict geometric facet has genuinely positive canonical weight. -/
theorem strictTieGraph_adj_canonicalFaceWeight_pos [Finite ι]
    (K : Set (E d)) (hK : IsCompact K) (hvol : volume K ≠ 0)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y) {i j : ι}
    (hedge : (strictTieGraph K (fun k => TripleCell.score (y k) (c k))).Adj i j) :
    0 < canonicalFaceWeight K y c i j := by
  obtain ⟨base, _, hb, _⟩ := hedge.2
  rw [canonicalFaceWeight_eq_chart K hK y c (hy.ne hedge.1) base hb]
  exact strictTieGraph_adj_normalized_surface_pos K hK hvol y c hy hedge base hb volume

/-- Positive cell masses supply all conditions required by the abstract
connected weighted-graph Laplacian API. -/
theorem canonicalFaceWeight_connected [Finite ι] [Nonempty ι]
    (ρ : Measure (E d)) (hρ : ρ ≪ volume)
    (K : Set (E d)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, ρ (CellGeometry.closedCell K y c i) ≠ 0) :
    ∃ G : SimpleGraph ι, G.Connected ∧
      ∀ i j, G.Adj i j → 0 < canonicalFaceWeight K y c i j := by
  have hvol : volume K ≠ 0 := by
    intro hz
    let i : ι := Classical.choice inferInstance
    exact hpos i (hρ (measure_mono_null (CellGeometry.closedCell_subset K y c i) hz))
  exact ⟨strictTieGraph K (fun i => TripleCell.score (y i) (c i)),
    strictTieGraph_connected_of_positive_cells ρ hρ K hconv y c hy hpos,
    fun _ _ hij => strictTieGraph_adj_canonicalFaceWeight_pos K hK hvol y c hy hij⟩

/-- The actual geometric cell Laplacian has exactly the constant kernel. -/
theorem canonicalLaplacian_eq_zero_iff_constant [Fintype ι] [Nonempty ι]
    (ρ : Measure (E d)) (hρ : ρ ≪ volume)
    (K : Set (E d)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, ρ (CellGeometry.closedCell K y c i) ≠ 0) (q : ι → ℝ) :
    CellLaplacian.apply (canonicalFaceWeight K y c) q = 0 ↔
      ∃ a : ℝ, ∀ i, q i = a := by
  obtain ⟨G, hG, hGp⟩ := canonicalFaceWeight_connected ρ hρ K hK hconv y c hy hpos
  exact CellLaplacian.apply_eq_zero_iff_constant _ (canonicalFaceWeight_symm K y c)
    (canonicalFaceWeight_nonneg K y c) G hG hGp q

/-- Every zero-sum mass variation has one and only one normalized geometric
intercept variation. -/
theorem canonicalLaplacian_existsUnique_normalized_solution [Fintype ι] [Nonempty ι]
    (ρ : Measure (E d)) (hρ : ρ ≪ volume)
    (K : Set (E d)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, ρ (CellGeometry.closedCell K y c i) ≠ 0)
    (m z : ι → ℝ) (hm : ∑ i, m i = 1) (hz : ∑ i, z i = 0) :
    ∃! q : ι → ℝ, CellLaplacian.apply (canonicalFaceWeight K y c) q = z ∧
      ∑ i, m i * q i = 0 := by
  obtain ⟨G, hG, hGp⟩ := canonicalFaceWeight_connected ρ hρ K hK hconv y c hy hpos
  exact CellLaplacian.existsUnique_normalized_solution _
    (canonicalFaceWeight_symm K y c) (canonicalFaceWeight_nonneg K y c)
    G hG hGp m z hm hz

/-- The canonical normalized geometric cell Laplacian is a continuous linear
isomorphism, with all positivity and connectivity consequences proved. -/
def canonicalNormalizedEquiv [Fintype ι] [Nonempty ι]
    (ρ : Measure (E d)) (hρ : ρ ≪ volume)
    (K : Set (E d)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, ρ (CellGeometry.closedCell K y c i) ≠ 0)
    (m : ι → ℝ) (hm : ∑ i, m i = 1) :
    CellLaplacian.normalizedSpace m ≃L[ℝ]
      CellLaplacian.normalizedSpace (fun _ : ι => 1) := by
  let h := canonicalFaceWeight_connected ρ hρ K hK hconv y c hy hpos
  exact CellLaplacian.normalizedEquiv _ (canonicalFaceWeight_symm K y c)
    (canonicalFaceWeight_nonneg K y c) h.choose h.choose_spec.1 h.choose_spec.2 m hm

@[simp] theorem canonicalNormalizedEquiv_apply [Fintype ι] [Nonempty ι]
    (ρ : Measure (E d)) (hρ : ρ ≪ volume)
    (K : Set (E d)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, ρ (CellGeometry.closedCell K y c i) ≠ 0)
    (m : ι → ℝ) (hm : ∑ i, m i = 1) (q : CellLaplacian.normalizedSpace m) :
    (canonicalNormalizedEquiv ρ hρ K hK hconv y c hy hpos m hm q : ι → ℝ) =
      CellLaplacian.apply (canonicalFaceWeight K y c) q := rfl

end Problem358.PositiveFacet

end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The global intrinsic cut integral is the actual common-face integral. -/
theorem intrinsicCutCoefficient_eq_faceIntegral
    {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) {i j : ι} (hy : y i ≠ y j)
    (w : E d → ℝ) :
    AffinePlaneGraph.intrinsicCutCoefficient K ((Finset.univ.erase i).erase j) i j w
      (y, c) =
      (∫ x in closedCell K y c i ∩ closedCell K y c j, w x
        ∂IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)) / ‖y i - y j‖ := by
  unfold AffinePlaneGraph.intrinsicCutCoefficient
  congr 1
  rw [← integral_indicator ((isClosed_closedCell hK y c i).inter
    (isClosed_closedCell hK y c j)).measurableSet]
  apply integral_congr_ae
  filter_upwards [IntrinsicSurface.ae_interface_tie hy (c i) (c j)] with x hx
  exact (commonFace_indicator_eq_cut_product K y c i j
    ((Finset.univ.erase i).erase j) (by
      intro k
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact and_comm) w hx).symm

/-- Continuity of an arbitrary continuous scalar common-face integral, with the
actual source and normal normalization. -/
theorem continuousAt_normalizedFaceIntegral
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {w : E d → ℝ} (hw : Continuous w) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      (∫ x in closedCell K p.1 p.2 i ∩ closedCell K p.1 p.2 j, w x
        ∂IntrinsicSurface.interfaceMeasure (p.1 i) (p.1 j) (p.2 i) (p.2 j)) /
          ((volume K).toReal * ‖p.1 i - p.1 j‖)) (y, c) := by
  have hc := (AffinePlaneGraph.continuousAt_intrinsicCutCoefficient hρ hK hconv
    y c hy hpos hij ((Finset.univ.erase i).erase j)
    (by
      intro k hk
      exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1,
        (Finset.mem_erase.mp hk).1⟩) hw).div_const (volume K).toReal
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_injective_sites y c hy] with p hp
  rw [intrinsicCutCoefficient_eq_faceIntegral hK.isClosed p.1 p.2 (hp.ne hij) w]
  ring

/-- Canonical normalized face areas vary continuously at positive cells. -/
theorem continuousAt_canonicalFaceWeight
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0) (i j : ι) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      PositiveFacet.canonicalFaceWeight K p.1 p.2 i j) (y, c) := by
  by_cases hij : i = j
  · subst j
    simpa using (continuousAt_const : ContinuousAt (fun _ :
      (ι → E d) × (ι → ℝ) => (0 : ℝ)) (y, c))
  have hc := continuousAt_normalizedFaceIntegral hρ hK hconv y c hy hpos hij
    (w := fun _ => (1 : ℝ)) continuous_const
  simpa only [PositiveFacet.canonicalFaceWeight, integral_const, Measure.real,
    Measure.restrict_apply_univ, smul_eq_mul, mul_one] using hc

/-- Canonical normalized first face moments also vary continuously. -/
theorem continuousAt_faceMoment
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0) (i j : ι) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) => faceMoment K p.1 p.2 i j) (y, c) := by
  by_cases hij : i = j
  · subst j
    simpa using (continuousAt_const : ContinuousAt (fun _ :
      (ι → E d) × (ι → ℝ) => (0 : E d)) (y, c))
  have heq (p : (ι → E d) × (ι → ℝ)) (k : Fin d) :
      faceMoment K p.1 p.2 i j k =
      (∫ x in closedCell K p.1 p.2 i ∩ closedCell K p.1 p.2 j, x k
        ∂IntrinsicSurface.interfaceMeasure (p.1 i) (p.1 j) (p.2 i) (p.2 j)) /
          ((volume K).toReal * ‖p.1 i - p.1 j‖) := by
    have hi := IntrinsicSurface.integrableOn_interfaceMeasure
      (p.1 i) (p.1 j) (p.2 i) (p.2 j)
      ((isCompact_closedCell hK p.1 p.2 i).inter
        (isCompact_closedCell hK p.1 p.2 j)) continuous_id.continuousOn
    have hp := ((EuclideanSpace.proj k).integral_comp_comm hi).symm
    change ((volume K).toReal * ‖p.1 i - p.1 j‖)⁻¹ *
      (∫ x in closedCell K p.1 p.2 i ∩ closedCell K p.1 p.2 j, x
        ∂IntrinsicSurface.interfaceMeasure (p.1 i) (p.1 j) (p.2 i) (p.2 j)) k = _
    rw [show (∫ x in closedCell K p.1 p.2 i ∩ closedCell K p.1 p.2 j, x
      ∂IntrinsicSurface.interfaceMeasure (p.1 i) (p.1 j) (p.2 i) (p.2 j)) k =
      ∫ x in closedCell K p.1 p.2 i ∩ closedCell K p.1 p.2 j, x k
      ∂IntrinsicSurface.interfaceMeasure (p.1 i) (p.1 j) (p.2 i) (p.2 j) by simpa using hp]
    ring
  have hc : ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      fun k : Fin d => faceMoment K p.1 p.2 i j k) (y, c) := by
    apply continuousAt_pi.mpr
    intro k
    simpa only [heq] using continuousAt_normalizedFaceIntegral hρ hK hconv y c hy hpos
      hij (w := fun x => x k) (by fun_prop)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).continuousAt.comp hc

end Problem358.CellGeometry

end

end OAI
