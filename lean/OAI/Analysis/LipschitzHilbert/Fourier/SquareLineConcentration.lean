import OAI.Analysis.LipschitzHilbert.Estimates.ShortPositiveSquare
import OAI.Analysis.LipschitzHilbert.Estimates.LongDyadicSum
import OAI.Analysis.LipschitzHilbert.Packets.PacketLineConcentration

namespace OAI

/-! Every-line BMO and moments of the positive packet square function. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.LinePacketFamily

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

def squareSum (P : LinePacketFamily N κ ι) (x : ℝ) : ℝ := ∑ j, P.positiveScale j x ^ 2
def shortSquare (P : LinePacketFamily N κ ι) (r x : ℝ) : ℝ :=
  ∑ j, if P.length j ≤ r then P.positiveScale j x ^ 2 else 0
def longSquare (P : LinePacketFamily N κ ι) (r x : ℝ) : ℝ :=
  ∑ j, if r < P.length j then P.positiveScale j x ^ 2 else 0
def squareFunction (P : LinePacketFamily N κ ι) (x : ℝ) : ℝ := Real.sqrt (P.squareSum x)
def squareMeanConstant (B : ℝ) : ℝ := (65536 * Real.pi) * (4 * Real.pi) ^ 6 * B

theorem squareSum_nonneg (P : LinePacketFamily N κ ι) (x : ℝ) : 0 ≤ P.squareSum x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem shortSquare_nonneg (P : LinePacketFamily N κ ι) (r x : ℝ) : 0 ≤ P.shortSquare r x :=
  Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)

theorem squareSum_continuous (P : LinePacketFamily N κ ι) : Continuous P.squareSum :=
  continuous_finsetSum _ (fun j _ => (P.positiveScale_continuous j).pow 2)

theorem shortSquare_continuous (P : LinePacketFamily N κ ι) (r : ℝ) : Continuous (P.shortSquare r) := by
  apply continuous_finsetSum
  intro j _
  by_cases hj : P.length j ≤ r
  · simp only [ite_eq_left hj]
    exact (P.positiveScale_continuous j).pow 2
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem longSquare_continuous (P : LinePacketFamily N κ ι) (r : ℝ) : Continuous (P.longSquare r) := by
  apply continuous_finsetSum
  intro j _
  by_cases hj : r < P.length j
  · simp only [ite_eq_left hj]
    exact (P.positiveScale_continuous j).pow 2
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem squareSum_split (P : LinePacketFamily N κ ι) (r x : ℝ) :
    P.squareSum x = P.shortSquare r x + P.longSquare r x := by
  unfold squareSum shortSquare longSquare
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : P.length j ≤ r
  · simp only [ite_eq_left hj, ite_eq_right (not_lt.mpr hj), add_zero]
  · simp only [ite_eq_right hj, ite_eq_left (lt_of_not_ge hj), zero_add]

theorem longSquare_oscillation (P : LinePacketFamily N κ ι) (u r : ℝ) (hr : 0 < r)
    {x y : ℝ} (hx : x ∈ Icc (u-r) (u+r)) (hy : y ∈ Icc (u-r) (u+r)) :
    |P.longSquare r x - P.longSquare r y| ≤ 48 * (4 * Real.pi) ^ 4 := by
  have h := long_dyadic_sum_oscillation (fun j x => P.positiveScale j x ^ 2)
    P.topLength u r (12 * (4 * Real.pi)^4) P.topLength_pos hr (by positivity)
    (fun j x => (P.positiveScale_square_hasDerivAt j x).differentiableAt)
    (fun j x => by simpa only [Real.norm_eq_abs, length] using P.positiveScale_square_derivative_bound j x) hx hy
  change |P.longSquare r x - P.longSquare r y| ≤ 4 * (12 * (4 * Real.pi)^4) at h
  exact h.trans_eq (by ring)

theorem squareSum_mean_oscillation (P : LinePacketFamily N κ ι) (g : FiniteLineGrid)
    {B : ℝ} (hB : 0 ≤ B) (hbudget : P.HasLocalBudget B) :
    g.HasFullMeanOscillationBound P.squareSum
      (2 * squareMeanConstant B + 48 * (4 * Real.pi)^4) := by
  intro level i _
  let r := g.meshWidth level / 2
  let u := g.origin + g.meshWidth level * i + r
  have hr : 0 < r := half_pos (g.meshWidth_pos level)
  have hcell : g.cell level i = Ico (u-r) (u+r) := by
    dsimp [FiniteLineGrid.cell,u,r]
    congr 1 <;> ring
  have hs := g.continuous_integrable_cell (P.shortSquare_continuous r) level i
  have hl := g.continuous_integrable_cell (P.longSquare_continuous r) level i
  have hshort : (∫ x in g.cell level i, ‖P.shortSquare r x‖) ≤
      squareMeanConstant B * (volume.restrict (g.cell level i)).real univ := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (P.shortSquare_nonneg r _)]
    rw [g.cell_mass, hcell, ← integral_Icc_eq_integral_Ico]
    have h := P.short_positive_square u r B hr hB hbudget
    change (∫ x in Icc (u-r) (u+r), P.shortSquare r x) ≤ squareMeanConstant B * r at h
    apply h.trans
    have hK : 0 ≤ squareMeanConstant B := by unfold squareMeanConstant; positivity
    exact mul_le_mul_of_nonneg_left (by dsimp [r]; linarith [g.meshWidth_pos level]) hK
  have hlong : ∀ᵐ x ∂volume.restrict (g.cell level i), ∀ᵐ y ∂volume.restrict (g.cell level i),
      ‖P.longSquare r x - P.longSquare r y‖ ≤ 48 * (4 * Real.pi)^4 := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    rw [hcell] at hx hy
    simpa only [Real.norm_eq_abs] using P.longSquare_oscillation u r hr
      (Ico_subset_Icc_self hx) (Ico_subset_Icc_self hy)
  have h := short_long_mean_oscillation (volume.restrict (g.cell level i))
    (P.shortSquare r) (P.longSquare r) hs hl (by rw [g.cell_mass]; exact g.meshWidth_pos level) hshort hlong
  simp_rw [← P.squareSum_split r] at h
  simpa only [Real.norm_eq_abs, g.cellMean_eq_integralAverage, g.cell_mass] using h

theorem squareSum_root_integral (P : LinePacketFamily N κ ι) (g : FiniteLineGrid)
    (hwidth : P.topLength ≤ g.width) {B : ℝ} (hB : 0 ≤ B) (hbudget : P.HasLocalBudget B) :
    (∫ x, P.squareSum x ∂g.lineMeasure) ≤ squareMeanConstant B * g.width := by
  have heq : P.shortSquare g.width = P.squareSum := by
    funext x
    unfold shortSquare squareSum
    apply Finset.sum_congr rfl
    intro j _
    exact ite_eq_left ((P.length_le_topLength j).trans hwidth)
  have h := P.short_positive_square g.origin g.width B g.width_pos hB hbudget
  change (∫ x in Icc (g.origin-g.width) (g.origin+g.width), P.shortSquare g.width x) ≤
    squareMeanConstant B * g.width at h
  rw [heq] at h
  have hint : IntegrableOn P.squareSum (Icc (g.origin-g.width) (g.origin+g.width)) :=
    P.squareSum_continuous.continuousOn.integrableOn_Icc
  have hsub : g.root ⊆ Icc (g.origin-g.width) (g.origin+g.width) := by
    intro x hx
    exact ⟨by linarith [hx.1,g.width_pos], hx.2.le⟩
  exact (setIntegral_mono_set hint (Filter.Eventually.of_forall (fun x => P.squareSum_nonneg x))
    (Filter.Eventually.of_forall (fun _ hx => hsub hx))).trans h

theorem squareSum_mean (P : LinePacketFamily N κ ι) (g : FiniteLineGrid)
    (hwidth : P.topLength ≤ g.width) {B : ℝ} (hB : 0 ≤ B) (hbudget : P.HasLocalBudget B) :
    |integralAverage g.lineMeasure P.squareSum| ≤ squareMeanConstant B := by
  have hmass : g.lineMeasure.real univ = g.width := by
    change (volume.restrict g.root).real univ = g.width
    simpa only [g.cell_zero, FiniteLineGrid.meshWidth, pow_zero, div_one] using g.cell_mass 0 0
  have hnonneg : 0 ≤ ∫ x, P.squareSum x ∂g.lineMeasure := integral_nonneg P.squareSum_nonneg
  rw [integralAverage, smul_eq_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg),
    abs_of_nonneg hnonneg, hmass]
  calc
    _ ≤ g.width⁻¹ * (squareMeanConstant B * g.width) :=
      mul_le_mul_of_nonneg_left (P.squareSum_root_integral g hwidth hB hbudget)
        (inv_nonneg.mpr g.width_pos.le)
    _ = _ := by field_simp [g.width_pos.ne']

theorem squareFunction_moment (P : LinePacketFamily N κ ι) (g : FiniteLineGrid)
    (hb : 1 < g.branching) (hwidth : P.topLength ≤ g.width) {B p : ℝ}
    (hB : 0 ≤ B) (hbudget : P.HasLocalBudget B) (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal |P.squareFunction x|)^p ∂g.lineMeasure) ≤
      (2 : ℝ≥0∞)^(p/2) *
        (7 * ENNReal.ofReal (((p/2) * (((g.branching : ℝ)+2) *
          (2 * squareMeanConstant B + 48 * (4 * Real.pi)^4)) / Real.log (3/2))^(p/2)) +
          (ENNReal.ofReal (squareMeanConstant B))^(p/2)) * g.lineMeasure univ := by
  have hint : Integrable P.squareSum g.lineMeasure := by
    have h := g.continuous_integrable_cell P.squareSum_continuous 0 0
    rw [g.cell_zero] at h
    exact h
  have hK : 0 ≤ squareMeanConstant B := by unfold squareMeanConstant; positivity
  have hA : 0 < 2 * squareMeanConstant B + 48 * (4 * Real.pi)^4 := by positivity
  have h := g.continuous_raw_moment hb P.squareSum P.squareSum_continuous.measurable hint
    (fun _ _ => P.squareSum_continuous.continuousAt) hA
    (P.squareSum_mean_oscillation g hB hbudget) (P.squareSum_mean g hwidth hB hbudget)
    (div_nonneg hp (by norm_num : (0 : ℝ) ≤ 2))
  have heq (x : ℝ) : (ENNReal.ofReal |P.squareFunction x|)^p =
      (ENNReal.ofReal |P.squareSum x|)^(p/2) := by
    rw [squareFunction, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (P.squareSum_nonneg x),
      Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (P.squareSum_nonneg x)
        (by norm_num : (0 : ℝ) ≤ 1/2),
      ← ENNReal.rpow_mul]
    congr 1
    ring
  simp_rw [heq]
  exact h

end LipschitzHilbert.LinePacketFamily

end

end OAI
