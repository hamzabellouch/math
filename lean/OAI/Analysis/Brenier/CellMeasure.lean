import OAI.Analysis.Brenier.CellGeometry

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.NormalizedCell

variable {X : Type*} [MeasurableSpace X]

/-- The probability law obtained by normalizing the restriction to a positive finite cell. -/
def measure (ρ : Measure X) (P : Set X) : Measure X :=
  (ρ P)⁻¹ • ρ.restrict P

variable {ρ : Measure X} {P : Set X}

/-- Positive finite extended mass is positive in the real-mass convention. -/
theorem real_mass_pos (hpos : 0 < ρ P) (hfinite : ρ P ≠ ∞) :
    0 < ρ.real P :=
  ENNReal.toReal_pos hpos.ne' hfinite

/-- Normalization is a probability whenever the cell has positive finite mass. -/
theorem probability (hpos : 0 < ρ P) (hfinite : ρ P ≠ ∞) :
    IsProbabilityMeasure (measure ρ P) := by
  constructor
  simp only [measure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hfinite

/-- Multiplying the normalized law by its cell mass recovers the raw restriction. -/
theorem mass_smul (hpos : 0 < ρ P) (hfinite : ρ P ≠ ∞) :
    (ρ P) • measure ρ P = ρ.restrict P := by
  rw [measure, smul_smul, ENNReal.mul_inv_cancel hpos.ne' hfinite, one_smul]

/-- The same cancellation in the real-mass notation used by cell derivatives. -/
theorem ofReal_mass_smul (hpos : 0 < ρ P) (hfinite : ρ P ≠ ∞) :
    ENNReal.ofReal (ρ.real P) • measure ρ P = ρ.restrict P := by
  rw [Measure.real, ENNReal.ofReal_toReal hfinite]
  exact mass_smul hpos hfinite

/-- The normalized restriction remains almost surely inside its measurable cell. -/
theorem ae_mem (hP : MeasurableSet P) : ∀ᵐ x ∂measure ρ P, x ∈ P := by
  rw [ae_iff]
  change measure ρ P Pᶜ = 0
  simp [measure, Measure.smul_apply, Measure.restrict_apply hP.compl]

/-- No integrability is lost or gained by a positive finite cell normalization. -/
theorem integrable_iff {V : Type*} [NormedAddCommGroup V] {f : X → V}
    (hpos : 0 < ρ P) (hfinite : ρ P ≠ ∞) :
    Integrable f (measure ρ P) ↔ IntegrableOn f P ρ := by
  exact integrable_smul_measure (ENNReal.inv_ne_zero.mpr hfinite)
    (ENNReal.inv_ne_top.mpr hpos.ne')

/-- Weighted averages under the normalized cell law recover raw cell integrals.
The identity is valid for real or vector valued functions, even without integrability. -/
theorem mass_smul_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hpos : 0 < ρ P) (hfinite : ρ P ≠ ∞) (f : X → V) :
    ρ.real P • (∫ x, f x ∂measure ρ P) = ∫ x in P, f x ∂ρ := by
  change (ρ P).toReal • (∫ x, f x ∂measure ρ P) = _
  rw [← integral_smul_measure f (ρ P), mass_smul hpos hfinite]

/-- Scalar form of the weighted-average identity. -/
theorem mass_mul_integral (hpos : 0 < ρ P) (hfinite : ρ P ≠ ∞) (f : X → ℝ) :
    ρ.real P * (∫ x, f x ∂measure ρ P) = ∫ x in P, f x ∂ρ :=
  mass_smul_integral hpos hfinite f

/-- Any random variable with the normalized cell law has the same weighted moments. -/
theorem mass_smul_integral_of_map_eq
    {Z : Type*} [MeasurableSpace Z] {π : Measure Z} {g : Z → X}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hpos : 0 < ρ P) (hfinite : ρ P ≠ ∞) (hg : Measurable g)
    (hmap : Measure.map g π = measure ρ P) {f : X → V}
    (hf : AEStronglyMeasurable f (measure ρ P)) :
    ρ.real P • (∫ z, f (g z) ∂π) = ∫ x in P, f x ∂ρ := by
  have hf' : AEStronglyMeasurable f (Measure.map g π) := hmap.symm ▸ hf
  rw [← integral_map hg.aemeasurable hf', hmap]
  exact mass_smul_integral hpos hfinite f

/-- Normalizing a cell removes any positive finite scalar prefactor in the source. -/
theorem measure_smul (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    measure (c • ρ) P = measure ρ P := by
  unfold measure
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_smul, smul_smul,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), mul_right_comm,
    ENNReal.inv_mul_cancel hc0 hctop, one_mul]

/-- Restricting the source to a larger set does not change the normalized cell law. -/
theorem measure_restrict {K : Set X} (hP : MeasurableSet P) (hPK : P ⊆ K) :
    measure (ρ.restrict K) P = measure ρ P := by
  unfold measure
  rw [Measure.restrict_apply hP, Set.inter_eq_left.mpr hPK,
    Measure.restrict_restrict_of_subset hPK]

end Problem358.NormalizedCell

namespace Problem358

/-- The probability law obtained by conditioning a measure on a positive finite cell. -/
def normalizedCellLaw {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) (P : Set X) : Measure X :=
  (ρ P)⁻¹ • ρ.restrict P

variable {X V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Measure X} {P : Set X}

lemma normalizedCellLaw_isProbabilityMeasure (hpos : ρ P ≠ 0) (hfin : ρ P ≠ ∞) :
    IsProbabilityMeasure (normalizedCellLaw ρ P) := by
  constructor
  rw [normalizedCellLaw, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos hfin

lemma normalizedCellLaw_ae_mem (hP : MeasurableSet P) :
    ∀ᵐ x ∂normalizedCellLaw ρ P, x ∈ P := by
  exact Measure.ae_smul_measure (ae_restrict_mem hP) _

/-- Multiplying a normalized cell law by its original mass recovers the restricted measure. -/
lemma mass_smul_normalizedCellLaw (hpos : ρ P ≠ 0) (hfin : ρ P ≠ ∞) :
    ENNReal.ofReal (ρ.real P) • normalizedCellLaw ρ P = ρ.restrict P := by
  rw [Measure.real_def, ENNReal.ofReal_toReal hfin, normalizedCellLaw, smul_smul,
    ENNReal.mul_inv_cancel hpos hfin, one_smul]

lemma integral_normalizedCellLaw (f : X → V) :
    (∫ x, f x ∂normalizedCellLaw ρ P) = (ρ.real P)⁻¹ • ∫ x in P, f x ∂ρ := by
  rw [normalizedCellLaw, integral_smul_measure, ENNReal.toReal_inv, Measure.real_def]

/-- Raw scalar moments and vector barycentres are the mass times their normalized integrals. -/
lemma mass_smul_integral_normalizedCellLaw (f : X → V)
    (hpos : ρ P ≠ 0) (hfin : ρ P ≠ ∞) :
    (ρ.real P) • (∫ x, f x ∂normalizedCellLaw ρ P) = ∫ x in P, f x ∂ρ := by
  rw [← mass_smul_normalizedCellLaw hpos hfin, integral_smul_measure,
    ENNReal.toReal_ofReal (measureReal_nonneg)]

omit [NormedSpace ℝ V] in
lemma integrable_normalizedCellLaw_iff (f : X → V)
    (hpos : ρ P ≠ 0) (hfin : ρ P ≠ ∞) :
    Integrable f (normalizedCellLaw ρ P) ↔ IntegrableOn f P ρ := by
  exact integrable_smul_measure (ENNReal.inv_ne_zero.2 hfin) (ENNReal.inv_ne_top.2 hpos)

lemma lintegral_normalizedCellLaw (f : X → ℝ≥0∞) :
    (∫⁻ x, f x ∂normalizedCellLaw ρ P) = (ρ P)⁻¹ * ∫⁻ x in P, f x ∂ρ := by
  exact lintegral_smul_measure _ f

/-- A first marginal equal to a normalized cell law recovers the cell's raw moment. -/
lemma mass_smul_integral_fst_of_normalizedCellLaw
    {Y : Type*} [MeasurableSpace Y] (π : Measure (X × Y)) (f : X → V)
    (hpos : ρ P ≠ 0) (hfin : ρ P ≠ ∞)
    (hmarg : Measure.map Prod.fst π = normalizedCellLaw ρ P)
    (hf : IntegrableOn f P ρ) :
    (ρ.real P) • (∫ p, f p.1 ∂π) = ∫ x in P, f x ∂ρ := by
  have hi : Integrable f (Measure.map Prod.fst π) := by
    rw [hmarg]
    exact (integrable_normalizedCellLaw_iff f hpos hfin).2 hf
  rw [← integral_map measurable_fst.aemeasurable hi.aestronglyMeasurable, hmarg]
  exact mass_smul_integral_normalizedCellLaw f hpos hfin

/-- The corresponding second-marginal formula, used for the other coupled cell. -/
lemma mass_smul_integral_snd_of_normalizedCellLaw
    {Y : Type*} [MeasurableSpace Y] (π : Measure (Y × X)) (f : X → V)
    (hpos : ρ P ≠ 0) (hfin : ρ P ≠ ∞)
    (hmarg : Measure.map Prod.snd π = normalizedCellLaw ρ P)
    (hf : IntegrableOn f P ρ) :
    (ρ.real P) • (∫ p, f p.2 ∂π) = ∫ x in P, f x ∂ρ := by
  have hi : Integrable f (Measure.map Prod.snd π) := by
    rw [hmarg]
    exact (integrable_normalizedCellLaw_iff f hpos hfin).2 hf
  rw [← integral_map measurable_snd.aemeasurable hi.aestronglyMeasurable, hmarg]
  exact mass_smul_integral_normalizedCellLaw f hpos hfin

/-- Normalized laws of a finite almost-everywhere partition reconstruct the source. -/
lemma sum_mass_smul_normalizedCellLaw {ι : Type*} [Fintype ι]
    (P : ι → Set X) (hP : ∀ i, MeasurableSet (P i))
    (hdis : Pairwise (fun i j => AEDisjoint ρ (P i) (P j)))
    (hcover : ∀ᵐ x ∂ρ, x ∈ ⋃ i, P i)
    (hpos : ∀ i, ρ (P i) ≠ 0) (hfin : ∀ i, ρ (P i) ≠ ∞) :
    (∑ i, ENNReal.ofReal (ρ.real (P i)) • normalizedCellLaw ρ (P i)) = ρ := by
  simp_rw [mass_smul_normalizedCellLaw (hpos _) (hfin _)]
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion_ae hdis
    (fun i => (hP i).nullMeasurableSet)]
  exact Measure.restrict_eq_self_of_ae_mem hcover

/-- Scalar moments and vector barycentres sum over normalized cell laws with raw masses. -/
lemma sum_mass_smul_integral_normalizedCellLaw {ι : Type*} [Fintype ι]
    (P : ι → Set X) (hP : ∀ i, MeasurableSet (P i))
    (hdis : Pairwise (fun i j => AEDisjoint ρ (P i) (P j)))
    (hcover : ∀ᵐ x ∂ρ, x ∈ ⋃ i, P i)
    (hpos : ∀ i, ρ (P i) ≠ 0) (hfin : ∀ i, ρ (P i) ≠ ∞)
    (f : X → V) (hf : Integrable f ρ) :
    (∑ i, (ρ.real (P i)) • ∫ x, f x ∂normalizedCellLaw ρ (P i)) = ∫ x, f x ∂ρ := by
  simp_rw [mass_smul_integral_normalizedCellLaw f (hpos _) (hfin _)]
  have h := integral_iUnion_ae (fun i => (hP i).nullMeasurableSet) hdis hf.restrict
  rw [Measure.restrict_eq_self_of_ae_mem hcover, tsum_fintype] at h
  exact h.symm

end Problem358

namespace Problem358

/-- The normalized restriction of a uniform source to a cell is exactly the
uniform law of that cell; this identifies the laws used by midpoint couplings. -/
theorem normalizedCell_uniformMeasure {d : ℕ} {K P : Set (E d)}
    (hKpos : 0 < volume K) (hKfinite : volume K ≠ ∞)
    (hP : MeasurableSet P) (hPK : P ⊆ K) :
    NormalizedCell.measure (uniformMeasure K) P = uniformMeasure P := by
  rw [uniformMeasure, NormalizedCell.measure_smul _
    (ENNReal.inv_ne_zero.mpr hKfinite) (ENNReal.inv_ne_top.mpr hKpos.ne'),
    NormalizedCell.measure_restrict hP hPK]
  rfl

/-- Cell mass for a uniform source is the ratio of cell and source volume. -/
theorem uniformMeasure_real_cell {d : ℕ} {K P : Set (E d)}
    (hP : MeasurableSet P) (hPK : P ⊆ K) :
    (uniformMeasure K).real P = (volume P).toReal / (volume K).toReal := by
  unfold Measure.real uniformMeasure
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hP,
    Set.inter_eq_left.mpr hPK, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

end Problem358

end

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*}

/-- A closed-cell mass is the normalized scalar volume integral used by the
moving-cut calculus. No positivity or distinct-site hypothesis is needed. -/
theorem uniformMass_eq_normalized_integral_one
    {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) :
    (uniformMeasure K).real (closedCell K y c i) =
      (volume K).toReal⁻¹ * ∫ _x in closedCell K y c i, (1 : ℝ) := by
  rw [uniformMeasure_real_cell (isClosed_closedCell hK y c i).measurableSet
    (closedCell_subset K y c i)]
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one]
  ring

/-- The uniform restriction on a cell rescales its volume integral. This also
holds for nonscalar moments and for degenerate source volume. -/
theorem integral_uniform_closedCell
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i : ι)
    (f : E d → V) :
    (∫ x in closedCell K y c i, f x ∂uniformMeasure K) =
      (volume K).toReal⁻¹ • ∫ x in closedCell K y c i, f x := by
  rw [uniformMeasure, Measure.restrict_smul,
    Measure.restrict_restrict_of_subset (closedCell_subset K y c i),
    integral_smul_measure, ENNReal.toReal_inv]

/-- A scalar moving-volume derivative immediately gives the actual normalized
real cell-mass derivative. -/
theorem hasDerivAt_uniformMass_of_integral_one
    {K : Set (E d)} (hK : IsClosed K)
    (y : ℝ → ι → E d) (c : ℝ → ι → ℝ) (i : ι) {t D : ℝ}
    (hD : HasDerivAt (fun s => ∫ _x in closedCell K (y s) (c s) i, (1 : ℝ)) D t) :
    HasDerivAt (fun s => (uniformMeasure K).real (closedCell K (y s) (c s) i))
      ((volume K).toReal⁻¹ * D) t := by
  have h := hD.const_mul (volume K).toReal⁻¹
  simpa only [uniformMass_eq_normalized_integral_one hK] using h

/-- The same normalization bridge for a Fréchet derivative in an arbitrary
real normed parameter space. -/
theorem hasFDerivAt_uniformMass_of_integral_one
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {K : Set (E d)} (hK : IsClosed K)
    (y : P → ι → E d) (c : P → ι → ℝ) (i : ι) {p : P} {D : P →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun q => ∫ _x in closedCell K (y q) (c q) i, (1 : ℝ)) D p) :
    HasFDerivAt (fun q => (uniformMeasure K).real (closedCell K (y q) (c q) i))
      ((volume K).toReal⁻¹ • D) p := by
  have h := hD.const_smul (volume K).toReal⁻¹
  simpa only [uniformMass_eq_normalized_integral_one hK, Pi.smul_def, smul_eq_mul] using h

/-- Strict differentiability is preserved by the fixed source normalization,
as required by the implicit-function theorem. -/
theorem hasStrictFDerivAt_uniformMass_of_integral_one
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {K : Set (E d)} (hK : IsClosed K)
    (y : P → ι → E d) (c : P → ι → ℝ) (i : ι) {p : P} {D : P →L[ℝ] ℝ}
    (hD : HasStrictFDerivAt
      (fun q => ∫ _x in closedCell K (y q) (c q) i, (1 : ℝ)) D p) :
    HasStrictFDerivAt
      (fun q => (uniformMeasure K).real (closedCell K (y q) (c q) i))
      ((volume K).toReal⁻¹ • D) p := by
  have h := hD.const_smul (volume K).toReal⁻¹
  simpa only [uniformMass_eq_normalized_integral_one hK, Pi.smul_def, smul_eq_mul] using h

end Problem358.CellGeometry

end

/-! Coordinate assembly and source normalization for genuine vector cell moments.
The scalar moving-cell calculus is an explicit input; no differentiability of a
cell or of its coefficients is assumed implicitly. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology BigOperators

namespace Problem358.CellVectorDerivative

variable {d : ℕ}

/-- A coordinate of a Bochner integral in the problem's Euclidean space. -/
theorem integral_coordinate {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → E d} (hf : Integrable f μ) (k : Fin d) :
    (∫ x, f x ∂μ) k = ∫ x, f x k ∂μ :=
  eval_integral_piLp (fun k => hf.eval_piLp k) k

/-- Assemble scalar coordinate derivatives in the Euclidean, rather than sup, norm. -/
theorem hasDerivAt_of_coordinates {f : ℝ → E d} {b : E d} {t : ℝ}
    (h : ∀ k : Fin d, HasDerivAt (fun s => f s k) (b k) t) :
    HasDerivAt f b t := by
  have hp : HasDerivAt (fun s k => f s k) (fun k => b k) t := hasDerivAt_pi.mpr h
  have hh := (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt t hp
  convert hh using 1 <;> simp [Function.comp_def]

/-- Restriction to a subset of the source removes the extra source indicator.
This identity is valid even in the zero-volume degenerate case. -/
theorem setIntegral_uniformMeasure {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {K P : Set (E d)} (hPK : P ⊆ K) (f : E d → V) :
    (∫ x in P, f x ∂uniformMeasure K) =
      (volume K).toReal⁻¹ • ∫ x in P, f x ∂volume := by
  rw [uniformMeasure, Measure.restrict_smul,
    Measure.restrict_restrict_of_subset hPK, integral_smul_measure, ENNReal.toReal_inv]

/-- Scalar volume derivatives of the coordinate weights give the actual
uniform-source vector-moment derivative, with the source normalization explicit. -/
theorem hasDerivAt_uniform_cellMoment_of_coordinates
    {ι : Type*} {K : Set (E d)} (hK : IsCompact K)
    (y : ℝ → ι → E d) (c : ℝ → ι → ℝ) (i : ι) {t : ℝ} {b : E d}
    (h : ∀ k : Fin d, HasDerivAt
      (fun s => ∫ x in CellGeometry.closedCell K (y s) (c s) i, x k ∂volume)
      (b k) t) :
    HasDerivAt
      (fun s => ∫ x in CellGeometry.closedCell K (y s) (c s) i, x ∂uniformMeasure K)
      ((volume K).toReal⁻¹ • b) t := by
  have hi (s : ℝ) : IntegrableOn (fun x : E d => x)
      (CellGeometry.closedCell K (y s) (c s) i) volume :=
    ContinuousOn.integrableOn_compact
      (CellGeometry.isCompact_closedCell hK (y s) (c s) i) continuousOn_id
  have hv : HasDerivAt
      (fun s => ∫ x in CellGeometry.closedCell K (y s) (c s) i, x ∂volume) b t := by
    apply hasDerivAt_of_coordinates
    intro k
    simpa only [integral_coordinate (hi _) k] using h k
  have hn := hv.const_smul (volume K).toReal⁻¹
  apply hn.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun s =>
    setIntegral_uniformMeasure (CellGeometry.closedCell_subset K (y s) (c s) i) id

/-- Normalize the scalar cell-mass derivative using the same source factor. -/
theorem hasDerivAt_uniform_cellMass
    {ι : Type*} {K : Set (E d)} (hK : IsCompact K)
    (y : ℝ → ι → E d) (c : ℝ → ι → ℝ) (i : ι) {t a : ℝ}
    (h : HasDerivAt
      (fun s => (volume (CellGeometry.closedCell K (y s) (c s) i)).toReal) a t) :
    HasDerivAt
      (fun s => (uniformMeasure K).real (CellGeometry.closedCell K (y s) (c s) i))
      (a / (volume K).toReal) t := by
  simpa only [uniformMeasure_real_cell
    (CellGeometry.isClosed_closedCell hK.isClosed _ _ _).measurableSet
    (CellGeometry.closedCell_subset K _ _ _)] using h.div_const (volume K).toReal

/-- Coordinate formula for a finite sum of weighted vector surface moments. -/
theorem coordinate_sum_integral_smul {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ j, MeasurableSpace (X j)]
    (μ : ∀ j, Measure (X j)) (z : ∀ j, X j → E d) (w : ∀ j, X j → ℝ)
    (hw : ∀ j, Integrable (fun x => w j x • z j x) (μ j)) (k : Fin d) :
    (∑ j, ∫ x, w j x • z j x ∂μ j) k =
      ∑ j, ∫ x, w j x * z j x k ∂μ j := by
  change (EuclideanSpace.proj k) (∑ j, ∫ x, w j x • z j x ∂μ j) = _
  rw [map_sum]
  congr 1
  funext j
  exact integral_coordinate (hw j) k

/-- The scalar face formulas for every coordinate assemble into the vector face
formula; integrability of the actual surface integrands is the only extra input. -/
theorem hasDerivAt_uniform_cellMoment_of_faces
    {ι κ : Type*} [Fintype κ] {X : κ → Type*} [∀ j, MeasurableSpace (X j)]
    {K : Set (E d)} (hK : IsCompact K)
    (y : ℝ → ι → E d) (c : ℝ → ι → ℝ) (i : ι) {t : ℝ}
    (μ : ∀ j, Measure (X j)) (z : ∀ j, X j → E d) (w : ∀ j, X j → ℝ)
    (hw : ∀ j, Integrable (fun x => w j x • z j x) (μ j))
    (h : ∀ k : Fin d, HasDerivAt
      (fun s => ∫ x in CellGeometry.closedCell K (y s) (c s) i, x k ∂volume)
      (∑ j, ∫ x, w j x * z j x k ∂μ j) t) :
    HasDerivAt
      (fun s => ∫ x in CellGeometry.closedCell K (y s) (c s) i, x ∂uniformMeasure K)
      ((volume K).toReal⁻¹ • ∑ j, ∫ x, w j x • z j x ∂μ j) t := by
  apply hasDerivAt_uniform_cellMoment_of_coordinates hK y c i
  intro k
  rw [coordinate_sum_integral_smul μ z w hw k]
  exact h k

/-- Separate the stationary intercept speed from normalized vector face moments.
No nonzero denominator assumptions are needed for this algebraic identity. -/
theorem normalized_stationary_face_sum
    {κ : Type*} [Fintype κ] {X : κ → Type*} [∀ j, MeasurableSpace (X j)]
    (μ : ∀ j, Measure (X j)) (z : ∀ j, X j → E d)
    (M : ℝ) (a q : κ → ℝ) :
    M⁻¹ • (∑ j, ∫ x, (q j / a j) • z j x ∂μ j) =
      ∑ j, q j • ((M * a j)⁻¹ • ∫ x, z j x ∂μ j) := by
  simp_rw [integral_smul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Convenient stationary-direction form, ready for the canonical face coefficient
`b_ij = (volume(K) * normalLength_ij)⁻¹ • firstMoment_ij`. -/
theorem hasDerivAt_uniform_cellMoment_stationary
    {ι κ : Type*} [Fintype κ] {X : κ → Type*} [∀ j, MeasurableSpace (X j)]
    {K : Set (E d)} (hK : IsCompact K)
    (y : ι → E d) (c q : ι → ℝ) (i : ι)
    (μ : ∀ j, Measure (X j)) (z : ∀ j, X j → E d)
    (a r : κ → ℝ) (hz : ∀ j, Integrable (z j) (μ j))
    (h : ∀ k : Fin d, HasDerivAt
      (fun s => ∫ x in CellGeometry.closedCell K y (fun j => c j + s * q j) i,
        x k ∂volume)
      (∑ j, ∫ x, (r j / a j) * z j x k ∂μ j) 0) :
    HasDerivAt
      (fun s => ∫ x in CellGeometry.closedCell K y (fun j => c j + s * q j) i,
        x ∂uniformMeasure K)
      (∑ j, r j • (((volume K).toReal * a j)⁻¹ • ∫ x, z j x ∂μ j)) 0 := by
  have hd := hasDerivAt_uniform_cellMoment_of_faces hK (fun _ => y)
    (fun s j => c j + s * q j) i μ z (fun j _ => r j / a j)
    (fun j => (hz j).smul (r j / a j)) h
  rw [normalized_stationary_face_sum] at hd
  exact hd

end Problem358.CellVectorDerivative

end

end OAI
