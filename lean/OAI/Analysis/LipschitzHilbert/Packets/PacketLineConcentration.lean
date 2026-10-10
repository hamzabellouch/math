import OAI.Analysis.LipschitzHilbert.Packets.LinePacketFamily
import OAI.Analysis.LipschitzHilbert.Estimates.RawBMOMoments

namespace OAI

/-! Reference-line concentration of the full packet variation, assembled
from the actual short-scale energy and long-scale derivative estimates. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal FourierTransform

namespace LipschitzHilbert.LinePacketFamily

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

theorem length_le_topLength (P : LinePacketFamily N κ ι) (j : Fin N) :
    P.length j ≤ P.topLength :=
  div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

theorem full_mean_oscillation (P : LinePacketFamily N κ ι) (g : FiniteLineGrid)
    {D : ℝ} (hD : 0 ≤ D)
    (hshort : ∀ u r : ℝ, 0 < r →
      (∫ x in Icc (u-r) (u+r),
        (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ 2) ≤ D * r) :
    g.HasFullMeanOscillationBound P.variation
      (2 * Real.sqrt (D + 1) + 4 * (P.constant * (4 * Real.pi) ^ 2)) := by
  let r := fun level => g.meshWidth level / 2
  let u := fun level i => g.origin + g.meshWidth level * i + r level
  let S := fun level (_i : ℕ) n x => hilbertPartialBandSum (P.shortPackets (r level)) n x
  let L := fun level (_i : ℕ) n x => hilbertPartialBandSum (P.longPackets (r level)) n x
  have hr (level : ℕ) : 0 < r level := by dsimp [r]; exact half_pos (g.meshWidth_pos level)
  have hcell (level i : ℕ) : g.cell level i = Ico (u level i - r level) (u level i + r level) := by
    dsimp [FiniteLineGrid.cell, u, r]
    congr 1 <;> ring
  apply g.variation_full_mean_oscillation
    (fun n x => hilbertPartialBandSum P.packets n x) S L N
    (fun level _ n => hilbertPartialBandSum_continuous _ n)
    (fun level _ n => hilbertPartialBandSum_continuous _ n)
    (fun level _ n x => P.partial_sum_split (r level) n x)
    (Real.sqrt_pos.mpr (by linarith))
  · intro level i _
    change (∫ x in g.cell level i,
      (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets (r level)) n x) N) ^ 2) ≤ _
    rw [hcell, ← integral_Icc_eq_integral_Ico]
    apply (hshort (u level i) (r level) (hr level)).trans
    rw [Real.sq_sqrt (by linarith : 0 ≤ D + 1)]
    dsimp [r]
    nlinarith [g.meshWidth_pos level]
  · intro level i _ x hx z hz
    change cubicVariation (fun n => hilbertPartialBandSum (P.longPackets (r level)) n x -
      hilbertPartialBandSum (P.longPackets (r level)) n z) N ≤ _
    rw [hcell] at hx hz
    exact P.long_oscillation (u level i) (r level) (hr level)
      (Ico_subset_Icc_self hx) (Ico_subset_Icc_self hz)

theorem root_square_bound (P : LinePacketFamily N κ ι) (g : FiniteLineGrid)
    (hwidth : P.topLength ≤ g.width) {D : ℝ}
    (hshort : ∀ u r : ℝ, 0 < r →
      (∫ x in Icc (u-r) (u+r),
        (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ 2) ≤ D * r) :
    (∫ x, P.variation x ^ 2 ∂g.lineMeasure) ≤ D * g.width := by
  have hpack : P.shortPackets g.width = P.packets := by
    funext j k
    exact ite_eq_left ((P.length_le_topLength j).trans hwidth)
  have hs := hshort g.origin g.width g.width_pos
  rw [hpack] at hs
  have hsub : g.root ⊆ Icc (g.origin-g.width) (g.origin+g.width) := by
    intro x hx
    exact ⟨by linarith [hx.1,g.width_pos], hx.2.le⟩
  have hi : IntegrableOn (fun x => P.variation x ^ 2)
      (Icc (g.origin-g.width) (g.origin+g.width)) :=
    (P.continuous_variation.pow 2).continuousOn.integrableOn_Icc
  have hm := setIntegral_mono_set hi (Filter.Eventually.of_forall (fun x => sq_nonneg (P.variation x)))
    (Filter.Eventually.of_forall (fun _ hx => hsub hx))
  exact hm.trans hs

theorem mean_bound (P : LinePacketFamily N κ ι) (g : FiniteLineGrid)
    (hwidth : P.topLength ≤ g.width) {D : ℝ} (hD : 0 ≤ D)
    (hshort : ∀ u r : ℝ, 0 < r →
      (∫ x in Icc (u-r) (u+r),
        (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ 2) ≤ D * r) :
    |integralAverage g.lineMeasure P.variation| ≤ Real.sqrt (D + 1) := by
  have hv : Integrable P.variation g.lineMeasure := by
    have h := g.continuous_integrable_cell P.continuous_variation 0 0
    rw [g.cell_zero] at h
    exact h
  have hv2 : Integrable (fun x => P.variation x ^ 2) g.lineMeasure := by
    have h := g.continuous_integrable_cell (P.continuous_variation.pow 2) 0 0
    rw [g.cell_zero] at h
    exact h
  have hmass : g.lineMeasure.real univ = g.width := by
    change (volume.restrict g.root).real univ = g.width
    have h := g.cell_mass 0 0
    simpa only [g.cell_zero, FiniteLineGrid.meshWidth, pow_zero, div_one] using h
  have hroot := P.root_square_bound g hwidth hshort
  have hsq : (∫ x, P.variation x ^ 2 ∂g.lineMeasure) ≤
      (Real.sqrt (D+1)) ^ 2 * g.lineMeasure.real univ := by
    rw [Real.sq_sqrt (by linarith : 0 ≤ D+1), hmass]
    nlinarith [g.width_pos]
  have hmean := integral_le_of_square_mean_bound g.lineMeasure P.variation hv hv2
    (Real.sqrt_pos.mpr (by linarith)) hsq
  have hnonneg : 0 ≤ integralAverage g.lineMeasure P.variation := by
    unfold integralAverage
    simp only [smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (measureReal_nonneg))
      (integral_nonneg (fun _ => cubicVariation_nonneg _ _))
  rw [abs_of_nonneg hnonneg, integralAverage, smul_eq_mul]
  calc
    _ ≤ (g.lineMeasure.real univ)⁻¹ * (Real.sqrt (D+1) * g.lineMeasure.real univ) :=
      mul_le_mul_of_nonneg_left hmean (inv_nonneg.mpr measureReal_nonneg)
    _ = Real.sqrt (D+1) := by rw [hmass]; field_simp [g.width_pos.ne']

theorem line_moment (hL : LepingleInput) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : LinePacketFamily N κ ι) (B : ℝ), 0 ≤ B → P.HasLocalBudget B →
      (∀ j i k ξ, |ξ| < lo * (2 : ℝ) ^ j.val → 𝓕 (P.wave j i k) ξ = 0) →
      (∀ j i k ξ, hi * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (P.wave j i k) ξ = 0) →
      ∀ (g : FiniteLineGrid), 1 < g.branching → P.topLength ≤ g.width →
      ∀ p : ℝ, 0 ≤ p →
      (∫⁻ x, (ENNReal.ofReal |P.variation x|) ^ p ∂g.lineMeasure) ≤
        (2 : ℝ≥0∞) ^ p *
          (7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) *
            (2 * Real.sqrt (A * P.constant ^ 2 * B + 1) +
              4 * (P.constant * (4 * Real.pi) ^ 2))) / Real.log (3/2)) ^ p) +
            (ENNReal.ofReal (Real.sqrt (A * P.constant ^ 2 * B + 1))) ^ p) *
          g.lineMeasure univ := by
  obtain ⟨A,hA,hshort⟩ := short_energy (N := N) (κ := κ) (ι := ι) hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro P B hB hbudget hlow hhigh g hb hwidth p hp
  have hD : 0 ≤ A * P.constant ^ 2 * B := by positivity
  have hs := hshort P B hB hbudget hlow hhigh
  have hpos : 0 < 2 * Real.sqrt (A * P.constant ^ 2 * B + 1) +
      4 * (P.constant * (4 * Real.pi) ^ 2) := by
    have hC := P.constant_pos
    positivity
  have hint : Integrable P.variation g.lineMeasure := by
    have h := g.continuous_integrable_cell P.continuous_variation 0 0
    rw [g.cell_zero] at h
    exact h
  exact g.continuous_raw_moment hb P.variation P.continuous_variation.measurable hint
    (fun _ _ => P.continuous_variation.continuousAt) hpos
    (P.full_mean_oscillation g hD hs) (P.mean_bound g hwidth hD hs) hp

end LipschitzHilbert.LinePacketFamily

end

end OAI
