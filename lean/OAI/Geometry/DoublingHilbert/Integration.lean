import OAI.Geometry.DoublingHilbert.Derivatives

namespace OAI

/-! Line integration and global Lipschitz extensions of sheets. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace DoublingHilbert

section FTC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Vector-valued FTC for a Lipschitz curve with its a.e. derivative specified.
This is the scalar absolutely-continuous FTC tested against the continuous dual. -/
theorem integral_eq_sub_of_lipschitz_ae_derivative
    {f g : ℝ → E} {a b : ℝ} {C : NNReal}
    (hf : LipschitzOnWith C f (uIcc a b))
    (hg : IntervalIntegrable g volume a b)
    (hderiv : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    (∫ x in a..b, g x) = f b - f a := by
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun L => ?_
  rw [← L.intervalIntegral_comp_comm hg, L.map_sub]
  have hAC := (L.lipschitzWith.comp_lipschitzOnWith hf).absolutelyContinuousOnInterval
  calc
    (∫ x in a..b, L (g x)) = ∫ x in a..b, deriv (L ∘ f) x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hderiv] with x hx hxab
      have h'x := L.hasFDerivAt.comp_hasDerivAt x (hx (uIoc_subset_uIcc hxab))
      exact h'x.deriv.symm
    _ = L (f b) - L (f a) := hAC.integral_deriv_eq_sub

/-- The endpoint estimate used for each full horizontal or vertical strip. -/
theorem norm_integral_derivative_sub_le
    {f g f' g' : ℝ → E} {a b R : ℝ} {C₁ C₂ : NNReal}
    (hf : LipschitzOnWith C₁ f (uIcc a b))
    (hg : LipschitzOnWith C₂ g (uIcc a b))
    (hf' : IntervalIntegrable f' volume a b)
    (hg' : IntervalIntegrable g' volume a b)
    (hdf : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (f' x) x)
    (hdg : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt g (g' x) x)
    (ha : ‖f a - g a‖ ≤ R) (hb : ‖f b - g b‖ ≤ R) :
    ‖∫ x in a..b, f' x - g' x‖ ≤ 2 * R := by
  rw [intervalIntegral.integral_sub hf' hg',
    integral_eq_sub_of_lipschitz_ae_derivative hf hf' hdf,
    integral_eq_sub_of_lipschitz_ae_derivative hg hg' hdg]
  have heq : f b - f a - (g b - g a) = (f b - g b) - (f a - g a) := by abel
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith)

end FTC

section MeanSquares
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Hilbert-space Cauchy--Schwarz in the form needed for line transport;
in fact convexity makes this valid for every normed target. -/
theorem norm_average_sq_le_average_norm_sq [IsFiniteMeasure μ] [NeZero μ]
    {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) :
    ‖⨍ x, G x ∂μ‖ ^ 2 ≤ ⨍ x, ‖G x‖ ^ 2 ∂μ := by
  exact ((convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set E))).pow
    (fun _ _ => norm_nonneg _) 2).map_average_le
      (continuous_norm.pow 2).continuousOn isClosed_univ
      (Eventually.of_forall fun _ => mem_univ _) hG hG2

/-- The integral version of the preceding averaged estimate, retaining the exact mass. -/
theorem norm_integral_sq_le_mass_mul [IsFiniteMeasure μ]
    {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) :
    ‖∫ x, G x ∂μ‖ ^ 2 ≤ μ.real Set.univ * (∫ x, ‖G x‖ ^ 2 ∂μ) := by
  by_cases hμ : μ = 0
  · subst μ; simp
  have : NeZero μ := ⟨hμ⟩
  have hm := measureReal_univ_pos (μ := μ)
  have hj := norm_average_sq_le_average_norm_sq hG hG2
  simp only [average_eq, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg hm.le, smul_eq_mul, ← div_eq_inv_mul] at hj
  have hj' := mul_le_mul_of_nonneg_left hj (sq_nonneg (μ.real univ))
  field_simp at hj'
  nlinarith

/-- Squared oscillation of a Lipschitz curve is bounded by its derivative energy. -/
theorem curve_oscillation_sq_le_integral
    {f g : ℝ → E} {a b : ℝ} {C : NNReal} (hab : a ≤ b)
    (hf : LipschitzOnWith C f (uIcc a b))
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun x => ‖g x‖ ^ 2) volume a b)
    (hderiv : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    ‖f b - f a‖ ^ 2 ≤ (b - a) * (∫ x in a..b, ‖g x‖ ^ 2) := by
  rw [← integral_eq_sub_of_lipschitz_ae_derivative hf hg hderiv]
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have h := norm_integral_sq_le_mass_mul hg.1 hg2.1
  simpa only [measureReal_restrict_apply_univ, Real.volume_real_Ioc,
    max_eq_left (sub_nonneg.mpr hab)] using h

end MeanSquares
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

section PartialIntegration
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Actual derivative columns of global extensions. -/
def column (f : ℝ × ℝ → E) (v : ℝ × ℝ) (p : ℝ × ℝ) : E := fderiv ℝ f p v

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem norm_column_le {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f)
    (v : ℝ × ℝ) (p : ℝ × ℝ) : ‖column f v p‖ ≤ C * ‖v‖ :=
  ((fderiv ℝ f p).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))

omit [CompleteSpace E] in
theorem stronglyMeasurable_column (f : ℝ × ℝ → E) (v : ℝ × ℝ) :
    StronglyMeasurable (column f v) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  exact ((ContinuousLinearMap.apply ℝ E v).continuous.measurable.comp
    (measurable_fderiv ℝ f)).stronglyMeasurable

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem intervalIntegrable_of_bound {g : ℝ → E} (hg : AEStronglyMeasurable g volume)
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (a b : ℝ) : IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff']
  exact IntegrableOn.of_bound isCompact_uIcc.measure_lt_top hg.restrict M
    (Eventually.of_forall hM)

omit [CompleteSpace E] in
theorem intervalIntegrable_column_x {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f)
    (v : ℝ × ℝ) (y a b : ℝ) :
    IntervalIntegrable (fun x => column f v (x, y)) volume a b := by
  apply intervalIntegrable_of_bound
    ((stronglyMeasurable_column f v).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  intro x
  exact norm_column_le hf v (x, y)

omit [CompleteSpace E] in
theorem intervalIntegrable_column_y {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f)
    (v : ℝ × ℝ) (x a b : ℝ) :
    IntervalIntegrable (fun y => column f v (x, y)) volume a b := by
  apply intervalIntegrable_of_bound
    ((stronglyMeasurable_column f v).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  intro y
  exact norm_column_le hf v (x, y)

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem lipschitz_line_x {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f) (y : ℝ) :
    LipschitzWith C (fun x => f (x, y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x x'
  simpa only [dist_prod_same_right] using hf.dist_le_mul (x, y) (x', y)

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem lipschitz_line_y {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f) (x : ℝ) :
    LipschitzWith C (fun y => f (x, y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y y'
  simpa only [dist_prod_same_left] using hf.dist_le_mul (x, y) (x, y')

omit [CompleteSpace E] in
theorem ae_line_derivative_x {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f) :
    ∀ᵐ y, ∀ᵐ x, HasDerivAt (fun t => f (t, y)) (column f (1, 0) (x, y)) x := by
  have hd := hf.ae_differentiableAt (μ := (volume : Measure (ℝ × ℝ)))
  rw [Measure.volume_eq_prod] at hd
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hd
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with y hy
  filter_upwards [hy] with x hx
  exact hx.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

omit [CompleteSpace E] in
theorem ae_line_derivative_y {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f) :
    ∀ᵐ x, ∀ᵐ y, HasDerivAt (fun t => f (x, t)) (column f (0, 1) (x, y)) y := by
  have hd := hf.ae_differentiableAt (μ := (volume : Measure (ℝ × ℝ)))
  rw [Measure.volume_eq_prod] at hd
  filter_upwards [Measure.ae_ae_of_ae_prod hd] with x hx
  filter_upwards [hx] with y hy
  exact hy.hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

/-- Fubini plus the vector FTC controls every subinterval on almost every horizontal line. -/
theorem ae_integral_column_x {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f) :
    ∀ᵐ y, ∀ a b : ℝ, (∫ x in a..b, column f (1, 0) (x, y)) = f (b, y) - f (a, y) := by
  filter_upwards [ae_line_derivative_x hf] with y hy
  intro a b
  exact integral_eq_sub_of_lipschitz_ae_derivative (lipschitz_line_x hf y).lipschitzOnWith
    (intervalIntegrable_column_x hf (1, 0) y a b) (hy.mono fun _ h _ => h)

/-- The corresponding vertical-line identity. -/
theorem ae_integral_column_y {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f) :
    ∀ᵐ x, ∀ a b : ℝ, (∫ y in a..b, column f (0, 1) (x, y)) = f (x, b) - f (x, a) := by
  filter_upwards [ae_line_derivative_y hf] with x hx
  intro a b
  exact integral_eq_sub_of_lipschitz_ae_derivative (lipschitz_line_y hf x).lipschitzOnWith
    (intervalIntegrable_column_y hf (0, 1) x a b) (hx.mono fun _ h _ => h)

end PartialIntegration
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
section Extensions
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def globalSheet {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) : Base → E :=
  (exists_lipschitz_extension_finiteDimensional (embeddingSheet_lipschitz hf w)).choose

omit [CompleteSpace E] in
theorem globalSheet_lipschitz {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    ∃ L : NNReal, LipschitzWith L (globalSheet hf w) := by
  obtain ⟨L, hL, _⟩ :=
    (exists_lipschitz_extension_finiteDimensional (embeddingSheet_lipschitz hf w)).choose_spec
  exact ⟨L, hL⟩

omit [CompleteSpace E] in
theorem globalSheet_eqOn {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    EqOn (globalSheet hf w) (embeddingSheet f w) (sheetDomain w) := by
  obtain ⟨_, _, heq⟩ :=
    (exists_lipschitz_extension_finiteDimensional (embeddingSheet_lipschitz hf w)).choose_spec
  exact heq.symm

omit [CompleteSpace E] in
theorem column_globalSheet {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) {p : Base} (hp : p ∈ sheetDomain w) (v : Base) :
    column (globalSheet hf w) v p = sheetColumn (embeddingSheet f w) (sheetDomain w) v p := by
  have heq : globalSheet hf w =ᶠ[𝓝 p] embeddingSheet f w :=
    (isOpen_sheetDomain w).eventually_mem hp |>.mono fun q hq => globalSheet_eqOn hf w hq
  rw [column, heq.fderiv_eq]
  simp only [sheetColumn, Set.indicator_of_mem hp]

theorem ae_globalSheet_pair {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    ∀ᵐ p, p ∈ sheetDomain w →
      (‖column (globalSheet hf w) (1, 0) p‖ ^ 2,
       ‖column (globalSheet hf w) (0, 1) p‖ ^ 2) ∈ derivativeCompact f := by
  filter_upwards [ae_good_embeddingSheet hf w] with p hp hmem
  rw [column_globalSheet hf w hmem, column_globalSheet hf w hmem]
  exact subset_closure ⟨w, p, hp hmem, rfl⟩

end Extensions
end
end DoublingHilbert

end

end OAI
