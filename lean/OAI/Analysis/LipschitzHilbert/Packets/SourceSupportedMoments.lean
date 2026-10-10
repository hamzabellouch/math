import OAI.Analysis.LipschitzHilbert.Fourier.SquareLineConcentration
import OAI.Analysis.LipschitzHilbert.Fourier.UniformLineMoments

namespace OAI

/-! Empty initial scales impose no lower bound on the reference window.
The root moment estimates need only contain the lengths of actual
retained packets. This is the situation for the fixed short reference
collection in §8. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.LinePacketFamily
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : LinePacketFamily N κ ι)

theorem shortPackets_eq_of_supported (r : ℝ) (hr : ∀ j (_u : ι j), P.length j ≤ r) :
    P.shortPackets r = P.packets := by
  funext j k
  by_cases hj : P.length j ≤ r
  · exact ite_eq_left hj
  · have : IsEmpty (ι j) := ⟨fun u => hj (hr j u)⟩
    simp [shortPackets,hj,packets,packetSynthesis]

theorem shortSquare_eq_of_supported (r : ℝ) (hr : ∀ j (_u : ι j), P.length j ≤ r) :
    P.shortSquare r = P.squareSum := by
  funext x
  unfold shortSquare squareSum
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : P.length j ≤ r
  · exact ite_eq_left hj
  · have : IsEmpty (ι j) := ⟨fun u => hj (hr j u)⟩
    simp [hj,positiveScale]

theorem root_square_bound_of_supported (grid : FiniteLineGrid)
    (hwidth : ∀ j (_u : ι j), P.length j ≤ grid.width) {D : ℝ}
    (hshort : ∀ u r : ℝ, 0 < r →
      (∫ x in Icc (u-r) (u+r),
        (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N)^2) ≤ D*r) :
    (∫ x, P.variation x^2 ∂grid.lineMeasure) ≤ D*grid.width := by
  have hs := hshort grid.origin grid.width grid.width_pos
  rw [P.shortPackets_eq_of_supported grid.width hwidth] at hs
  have hsub : grid.root ⊆ Icc (grid.origin-grid.width) (grid.origin+grid.width) := by
    intro x hx
    exact ⟨by linarith [hx.1,grid.width_pos],hx.2.le⟩
  have hi : IntegrableOn (fun x => P.variation x^2)
      (Icc (grid.origin-grid.width) (grid.origin+grid.width)) :=
    (P.continuous_variation.pow 2).continuousOn.integrableOn_Icc
  exact (setIntegral_mono_set hi
    (Filter.Eventually.of_forall (fun x => sq_nonneg (P.variation x)))
    (Filter.Eventually.of_forall (fun _ hx => hsub hx))).trans hs

theorem mean_bound_of_supported (grid : FiniteLineGrid)
    (hwidth : ∀ j (_u : ι j), P.length j ≤ grid.width) {D : ℝ} (hD : 0 ≤ D)
    (hshort : ∀ u r : ℝ, 0 < r →
      (∫ x in Icc (u-r) (u+r),
        (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N)^2) ≤ D*r) :
    |integralAverage grid.lineMeasure P.variation| ≤ Real.sqrt (D+1) := by
  have hv : Integrable P.variation grid.lineMeasure := by
    have h := grid.continuous_integrable_cell P.continuous_variation 0 0
    rw [grid.cell_zero] at h
    exact h
  have hv2 : Integrable (fun x => P.variation x^2) grid.lineMeasure := by
    have h := grid.continuous_integrable_cell (P.continuous_variation.pow 2) 0 0
    rw [grid.cell_zero] at h
    exact h
  have hmass : grid.lineMeasure.real univ = grid.width := by
    change (volume.restrict grid.root).real univ = grid.width
    simpa only [grid.cell_zero,FiniteLineGrid.meshWidth,pow_zero,div_one] using grid.cell_mass 0 0
  have hroot := P.root_square_bound_of_supported grid hwidth hshort
  have hsq : (∫ x, P.variation x^2 ∂grid.lineMeasure) ≤
      (Real.sqrt (D+1))^2*grid.lineMeasure.real univ := by
    rw [Real.sq_sqrt (by linarith : 0 ≤ D+1),hmass]
    nlinarith [grid.width_pos]
  have hmean := integral_le_of_square_mean_bound grid.lineMeasure P.variation hv hv2
    (Real.sqrt_pos.mpr (by linarith)) hsq
  have hnonneg : 0 ≤ integralAverage grid.lineMeasure P.variation := by
    unfold integralAverage
    exact smul_nonneg (inv_nonneg.mpr measureReal_nonneg)
      (integral_nonneg (fun _ => cubicVariation_nonneg _ _))
  rw [abs_of_nonneg hnonneg,integralAverage,smul_eq_mul]
  calc
    _ ≤ (grid.lineMeasure.real univ)⁻¹*(Real.sqrt (D+1)*grid.lineMeasure.real univ) :=
      mul_le_mul_of_nonneg_left hmean (inv_nonneg.mpr measureReal_nonneg)
    _ = _ := by rw [hmass]; field_simp [grid.width_pos.ne']

theorem squareSum_root_integral_of_supported (grid : FiniteLineGrid)
    (hwidth : ∀ j (_u : ι j), P.length j ≤ grid.width)
    {B : ℝ} (hB : 0 ≤ B) (hbudget : P.HasLocalBudget B) :
    (∫ x, P.squareSum x ∂grid.lineMeasure) ≤ squareMeanConstant B*grid.width := by
  have h := P.short_positive_square grid.origin grid.width B grid.width_pos hB hbudget
  change (∫ x in Icc (grid.origin-grid.width) (grid.origin+grid.width), P.shortSquare grid.width x) ≤ _ at h
  rw [P.shortSquare_eq_of_supported grid.width hwidth] at h
  have hi : IntegrableOn P.squareSum (Icc (grid.origin-grid.width) (grid.origin+grid.width)) :=
    P.squareSum_continuous.continuousOn.integrableOn_Icc
  have hsub : grid.root ⊆ Icc (grid.origin-grid.width) (grid.origin+grid.width) := by
    intro x hx
    exact ⟨by linarith [hx.1,grid.width_pos],hx.2.le⟩
  exact (setIntegral_mono_set hi (Filter.Eventually.of_forall P.squareSum_nonneg)
    (Filter.Eventually.of_forall (fun _ hx => hsub hx))).trans h

theorem squareSum_mean_of_supported (grid : FiniteLineGrid)
    (hwidth : ∀ j (_u : ι j), P.length j ≤ grid.width)
    {B : ℝ} (hB : 0 ≤ B) (hbudget : P.HasLocalBudget B) :
    |integralAverage grid.lineMeasure P.squareSum| ≤ squareMeanConstant B := by
  have hmass : grid.lineMeasure.real univ = grid.width := by
    change (volume.restrict grid.root).real univ = grid.width
    simpa only [grid.cell_zero,FiniteLineGrid.meshWidth,pow_zero,div_one] using grid.cell_mass 0 0
  have hnonneg : 0 ≤ ∫ x, P.squareSum x ∂grid.lineMeasure := integral_nonneg P.squareSum_nonneg
  rw [integralAverage,smul_eq_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg),
    abs_of_nonneg hnonneg,hmass]
  calc
    _ ≤ grid.width⁻¹*(squareMeanConstant B*grid.width) :=
      mul_le_mul_of_nonneg_left (P.squareSum_root_integral_of_supported grid hwidth hB hbudget)
        (inv_nonneg.mpr grid.width_pos.le)
    _ = _ := by field_simp [grid.width_pos.ne']

theorem squareFunction_moment_of_supported (grid : FiniteLineGrid)
    (hb : 1 < grid.branching) (hwidth : ∀ j (_u : ι j), P.length j ≤ grid.width)
    {B p : ℝ} (hB : 0 ≤ B) (hbudget : P.HasLocalBudget B) (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal |P.squareFunction x|)^p ∂grid.lineMeasure) ≤
      (2:ℝ≥0∞)^(p/2)*(7*ENNReal.ofReal (((p/2)*(((grid.branching:ℝ)+2)*
        (2*squareMeanConstant B+48*(4*Real.pi)^4))/Real.log (3/2))^(p/2))+
        (ENNReal.ofReal (squareMeanConstant B))^(p/2))*grid.lineMeasure univ := by
  have hint : Integrable P.squareSum grid.lineMeasure := by
    have h := grid.continuous_integrable_cell P.squareSum_continuous 0 0
    rw [grid.cell_zero] at h
    exact h
  have hK : 0 ≤ squareMeanConstant B := by unfold squareMeanConstant; positivity
  have hA : 0 < 2*squareMeanConstant B+48*(4*Real.pi)^4 := by positivity
  have h := grid.continuous_raw_moment hb P.squareSum P.squareSum_continuous.measurable hint
    (fun _ _ => P.squareSum_continuous.continuousAt) hA
    (P.squareSum_mean_oscillation grid hB hbudget)
    (P.squareSum_mean_of_supported grid hwidth hB hbudget)
    (div_nonneg hp (by norm_num : (0:ℝ) ≤ 2))
  have heq (x : ℝ) : (ENNReal.ofReal |P.squareFunction x|)^p =
      (ENNReal.ofReal |P.squareSum x|)^(p/2) := by
    rw [squareFunction,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (P.squareSum_nonneg x),
      Real.sqrt_eq_rpow,← ENNReal.ofReal_rpow_of_nonneg (P.squareSum_nonneg x)
        (by norm_num : (0:ℝ) ≤ 1/2),← ENNReal.rpow_mul]
    congr 1
    ring
  simp_rw [heq]
  exact h

/-- The published-input constant is uniform before choosing the finite
packet family. The reference window contains only the retained lengths. -/
theorem uniform_line_moment_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : LinePacketFamily N κ ι) (B : ℝ),
      0 ≤ B → P.HasLocalBudget B →
      (∀ j i k xi, |xi| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k) xi = 0) →
      (∀ j i k xi, hi*(2:ℝ)^j.val < |xi| → 𝓕 (P.wave j i k) xi = 0) →
      ∀ (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ j (_u : ι j), P.length j ≤ grid.width) → ∀ p : ℝ, 0 ≤ p →
      (∫⁻ x, (ENNReal.ofReal |P.variation x|)^p ∂grid.lineMeasure) ≤
        (2:ℝ≥0∞)^p*(7*ENNReal.ofReal ((p*(((grid.branching:ℝ)+2)*
          (2*Real.sqrt (A*P.constant^2*B+1)+4*(P.constant*(4*Real.pi)^2)))/
            Real.log (3/2))^p)+
          (ENNReal.ofReal (Real.sqrt (A*P.constant^2*B+1)))^p)*grid.lineMeasure univ := by
  obtain ⟨A,hA,hshort⟩ := uniform_short_energy hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P B hB hbudget hlow hhigh grid hb hwidth p hp
  have hD : 0 ≤ A*P.constant^2*B := by positivity
  have hs := hshort N κ ι P B hB hbudget hlow hhigh
  have hpos : 0 < 2*Real.sqrt (A*P.constant^2*B+1)+4*(P.constant*(4*Real.pi)^2) := by
    have hC := P.constant_pos
    positivity
  have hint : Integrable P.variation grid.lineMeasure := by
    have h := grid.continuous_integrable_cell P.continuous_variation 0 0
    rw [grid.cell_zero] at h
    exact h
  exact grid.continuous_raw_moment hb P.variation P.continuous_variation.measurable hint
    (fun _ _ => P.continuous_variation.continuousAt) hpos
    (P.full_mean_oscillation grid hD hs) (P.mean_bound_of_supported grid hwidth hD hs) hp

end LipschitzHilbert.LinePacketFamily

end

end OAI
