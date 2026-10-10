import OAI.Geometry.DoublingHilbert.Construction

namespace OAI

/-! Derivative fields, good points, and the compact set of derivative norms. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace DoublingHilbert

section BoundedFields
variable {E : Type*} [NormedAddCommGroup E]

/-- A measurable uniformly bounded field on the source plane is locally integrable. -/
theorem locallyIntegrable_of_uniform_bound {G : ℝ × ℝ → E}
    (hG : AEStronglyMeasurable G volume) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ p, ‖G p‖ ≤ M) :
    LocallyIntegrable G volume := by
  apply (locallyIntegrable_const (μ := volume) M).mono hG
  filter_upwards with p
  simpa only [Real.norm_eq_abs, abs_of_nonneg hM] using hbound p

/-- Lebesgue differentiation for bounded fields. -/
theorem ae_tendsto_average_norm_sub_sq {G : ℝ × ℝ → E}
    (hG : AEStronglyMeasurable G volume) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ p, ‖G p‖ ≤ M) :
    ∀ᵐ p, Tendsto (fun r : ℝ => ⨍ q in Metric.closedBall p r, ‖G q - G p‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hloc := locallyIntegrable_of_uniform_bound hG hM hbound
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hloc (0 : ℝ)]
    with p hp
  have hlim := hp (fun _ : ℝ => p) (fun r : ℝ => r) tendsto_id
    (Eventually.of_forall fun _ => by simp)
  have hdiff (q : ℝ × ℝ) : ‖G q - G p‖ ≤ 2 * M :=
    (norm_sub_le _ _).trans (by linarith [hbound q, hbound p])
  have hsquareloc : LocallyIntegrable (fun q => ‖G q - G p‖ ^ 2) volume := by
    apply locallyIntegrable_of_uniform_bound
      ((hG.sub (aestronglyMeasurable_const (b := G p))).norm.pow 2) (by positivity : 0 ≤ (2 * M) ^ 2)
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdiff q) 2
  have hnormloc : LocallyIntegrable (fun q => ‖G q - G p‖) volume := by
    apply locallyIntegrable_of_uniform_bound
      (hG.sub (aestronglyMeasurable_const (b := G p))).norm (by positivity : 0 ≤ 2 * M)
    intro q
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hdiff q
  have hlim' : Tendsto
      (fun r : ℝ => (2 * M) * (⨍ q in Metric.closedBall p r, ‖G q - G p‖))
      (𝓝[>] 0) (𝓝 0) := by simpa using tendsto_const_nhds.mul hlim
  apply squeeze_zero' (Eventually.of_forall fun r => ?_) (Eventually.of_forall fun r => ?_) hlim'
  · exact integral_nonneg fun _ => sq_nonneg _
  · have hi := hnormloc.integrableOn_isCompact (isCompact_closedBall p r)
    have hisq := hsquareloc.integrableOn_isCompact (isCompact_closedBall p r)
    change (∫ q, ‖G q - G p‖ ^ 2 ∂_) ≤ 2 * M * (∫ q, ‖G q - G p‖ ∂_)
    rw [← integral_const_mul]
    exact integral_mono hisq.to_average (hi.const_mul _).to_average
      (fun q => by nlinarith [hdiff q, norm_nonneg (G q - G p)])

end BoundedFields

section DerivativeFields
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Derivative column, extended by zero off the open sheet domain. -/
def sheetColumn (f : ℝ × ℝ → E) (Ω : Set (ℝ × ℝ)) (v : ℝ × ℝ) : ℝ × ℝ → E :=
  Ω.indicator (fun p => fderiv ℝ f p v)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem norm_sheetColumn_le {f : ℝ × ℝ → E} {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) {C : NNReal} (hf : LipschitzOnWith C f Ω) (v : ℝ × ℝ) (p : ℝ × ℝ) :
    ‖sheetColumn f Ω v p‖ ≤ C * ‖v‖ := by
  by_cases hp : p ∈ Ω
  · rw [sheetColumn, indicator_of_mem hp]
    exact ((fderiv ℝ f p).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hp) hf)
        (norm_nonneg v))
  · rw [sheetColumn, indicator_of_notMem hp, norm_zero]
    positivity

theorem aestronglyMeasurable_sheetColumn (f : ℝ × ℝ → E) {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (v : ℝ × ℝ) :
    AEStronglyMeasurable (sheetColumn f Ω v) volume := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  apply AEStronglyMeasurable.indicator _ hΩ.measurableSet
  exact ((ContinuousLinearMap.apply ℝ E v).continuous.measurable.comp
    (measurable_fderiv ℝ f)).aestronglyMeasurable

/-- Good derivative points have full measure on every sheet. -/
theorem ae_good_sheet_points {f : ℝ × ℝ → E} {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) {C : NNReal} (hf : LipschitzOnWith C f Ω) (v₁ v₂ : ℝ × ℝ) :
    ∀ᵐ p, p ∈ Ω → DifferentiableAt ℝ f p ∧
      Tendsto (fun r : ℝ => ⨍ q in Metric.closedBall p r,
        ‖sheetColumn f Ω v₁ q - sheetColumn f Ω v₁ p‖ ^ 2)
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r : ℝ => ⨍ q in Metric.closedBall p r,
        ‖sheetColumn f Ω v₂ q - sheetColumn f Ω v₂ p‖ ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
  have h₁ := ae_tendsto_average_norm_sub_sq (aestronglyMeasurable_sheetColumn f hΩ v₁)
    (mul_nonneg C.coe_nonneg (norm_nonneg v₁)) (norm_sheetColumn_le hΩ hf v₁)
  have h₂ := ae_tendsto_average_norm_sub_sq (aestronglyMeasurable_sheetColumn f hΩ v₂)
    (mul_nonneg C.coe_nonneg (norm_nonneg v₂)) (norm_sheetColumn_le hΩ hf v₂)
  filter_upwards [hf.ae_differentiableWithinAt_of_mem (μ := volume), h₁, h₂] with p hp h₁p h₂p hpm
  exact ⟨(hp hpm).differentiableAt (hΩ.mem_nhds hpm), h₁p, h₂p⟩

end DerivativeFields
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

section Embedding
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A sheet is the actual embedding on its domain; the arbitrary outside value is zero. -/
def embeddingSheet (f : constructedSet → E) (w : Tuple) (p : Base) : E := by
  classical
  exact if h : admissible p w then f ⟨point p w, point_mem p w h⟩ else 0

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem embeddingSheet_eq (f : constructedSet → E) (w : Tuple) (p : Base)
    (hp : admissible p w) : embeddingSheet f w p = f ⟨point p w, point_mem p w hp⟩ := by
  simp only [embeddingSheet, dite_eq_left hp]

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem embeddingSheet_lipschitz {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    LipschitzOnWith (2 * D) (embeddingSheet f w) (sheetDomain w) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  rw [embeddingSheet_eq _ _ _ hp, embeddingSheet_eq _ _ _ hq]
  calc
    _ ≤ (D : ℝ) * dist (point p w) (point q w) :=
      hf.dist_le_mul ⟨point p w, point_mem p w hp⟩ ⟨point q w, point_mem q w hq⟩
    _ ≤ (D : ℝ) * (2 * dist p q) := mul_le_mul_of_nonneg_left (point_dist_sameTuple_le p q w) D.coe_nonneg
    _ = _ := by push_cast; ring

def goodSheetPoint (f : constructedSet → E) (w : Tuple) (p : Base) : Prop :=
  p ∈ sheetDomain w ∧ DifferentiableAt ℝ (embeddingSheet f w) p ∧
    Tendsto (fun r : ℝ => ⨍ q in Metric.closedBall p r,
      ‖sheetColumn (embeddingSheet f w) (sheetDomain w) (1, 0) q -
        sheetColumn (embeddingSheet f w) (sheetDomain w) (1, 0) p‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun r : ℝ => ⨍ q in Metric.closedBall p r,
      ‖sheetColumn (embeddingSheet f w) (sheetDomain w) (0, 1) q -
        sheetColumn (embeddingSheet f w) (sheetDomain w) (0, 1) p‖ ^ 2)
      (𝓝[>] 0) (𝓝 0)

theorem ae_good_embeddingSheet {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    ∀ᵐ p, p ∈ sheetDomain w → goodSheetPoint f w p := by
  filter_upwards [ae_good_sheet_points (isOpen_sheetDomain w) (embeddingSheet_lipschitz hf w)
    (1, 0) (0, 1)] with p hp hmem
  exact ⟨hmem, hp hmem⟩

/-- Squared derivative columns, the pairs used in the one fixed compact set. -/
def derivativePair (f : constructedSet → E) (w : Tuple) (p : Base) : ℝ × ℝ :=
  (‖sheetColumn (embeddingSheet f w) (sheetDomain w) (1, 0) p‖ ^ 2,
   ‖sheetColumn (embeddingSheet f w) (sheetDomain w) (0, 1) p‖ ^ 2)

def derivativeData (f : constructedSet → E) : Set (ℝ × ℝ) :=
  {z | ∃ w p, goodSheetPoint f w p ∧ derivativePair f w p = z}

def derivativeCompact (f : constructedSet → E) : Set (ℝ × ℝ) := closure (derivativeData f)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem derivativePair_bounds {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (p : Base) :
    derivativePair f w p ∈ Icc (0, 0) ((2 * (D : ℝ)) ^ 2, (2 * (D : ℝ)) ^ 2) := by
  have hx := norm_sheetColumn_le (isOpen_sheetDomain w) (embeddingSheet_lipschitz hf w) (1, 0) p
  have hy := norm_sheetColumn_le (isOpen_sheetDomain w) (embeddingSheet_lipschitz hf w) (0, 1) p
  simp only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one,
    max_eq_right zero_le_one, NNReal.coe_mul, NNReal.coe_ofNat, mul_one] at hx hy
  refine ⟨⟨sq_nonneg _, sq_nonneg _⟩, ?_⟩
  exact ⟨pow_le_pow_left₀ (norm_nonneg _) hx 2, pow_le_pow_left₀ (norm_nonneg _) hy 2⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem derivativeCompact_subset {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) :
    derivativeCompact f ⊆ Icc (0, 0) ((2 * (D : ℝ)) ^ 2, (2 * (D : ℝ)) ^ 2) := by
  apply closure_minimal _ isClosed_Icc
  rintro z ⟨w, p, _, rfl⟩
  exact derivativePair_bounds hf w p

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem isCompact_derivativeCompact {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) : IsCompact (derivativeCompact f) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (derivativeCompact_subset hf)

theorem derivativeData_nonempty {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) : (derivativeData f).Nonempty := by
  obtain ⟨p, hp⟩ := (ae_good_embeddingSheet hf 0).exists
  exact ⟨derivativePair f 0 p, 0, p, hp (admissible_zero p), rfl⟩

theorem derivativeCompact_nonempty {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) : (derivativeCompact f).Nonempty :=
  (derivativeData_nonempty hf).mono subset_closure

end Embedding
end DoublingHilbert

open Set
noncomputable section
namespace DoublingHilbert

/-- Finite-dimensional Lipschitz sheet maps have some global Lipschitz extension.
Only agreement on the original open domain is used for sharp derivative estimates. -/
theorem exists_lipschitz_extension_finiteDimensional
    {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : X → E} {s : Set X} {C : NNReal}
    (hf : LipschitzOnWith C f s) :
    ∃ g : X → E, ∃ L : NNReal, LipschitzWith L g ∧ EqOn f g s := by
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  obtain ⟨g, hg, heq⟩ := (e.lipschitzWith.comp_lipschitzOnWith hf).extend_pi
  refine ⟨e.symm ∘ g, _, e.symm.lipschitzWith.comp hg, ?_⟩
  intro x hx
  change f x = e.symm (g x)
  rw [← heq hx]
  exact (e.symm_apply_apply (f x)).symm

end DoublingHilbert

end
end

end OAI
