import OAI.Analysis.LipschitzHilbert.Packets.PacketLineConcentration

namespace OAI

/-! Expose the dimension and scale-count uniformity of the already proved
short energy and line moments. The constant is chosen before the finite
packet spaces, as required for the final uniform operator estimate. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform

namespace LipschitzHilbert.LinePacketFamily

theorem uniform_short_energy (hL : LepingleInput) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : LinePacketFamily N κ ι) (B : ℝ), 0 ≤ B → P.HasLocalBudget B →
      (∀ j i k ξ, |ξ| < lo * (2 : ℝ) ^ j.val → 𝓕 (P.wave j i k) ξ = 0) →
      (∀ j i k ξ, hi * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (P.wave j i k) ξ = 0) →
      ∀ u r : ℝ, 0 < r →
      (∫ x in Icc (u-r) (u+r),
        (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ 2) ≤
        A * P.constant ^ 2 * B * r := by
  obtain ⟨A,hA,hshort⟩ := short_line_variation hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P B hB hbudget hlow hhigh u r hr
  have he := hshort N κ ι P.coeff P.wave P.centerX P.centerZ P.site P.length
    P.baseX P.baseZ u P.lineY r P.width P.constant B P.site_injective P.length_pos hr
    P.width_pos hB (fun _ _ => rfl) (fun _ _ => rfl) P.wave_bound (hbudget u r hr) hlow hhigh
  have hc := continuous_cubicVariation _ (hilbertPartialBandSum_continuous (P.shortPackets r)) N
  have hint : IntegrableOn (fun x =>
      (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ 2)
      (Icc (u-r) (u+r)) volume := (hc.pow 2).continuousOn.integrableOn_Icc
  have heq : ENNReal.ofReal (∫ x in Icc (u-r) (u+r),
      (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ 2) =
      ∫⁻ x in Icc (u-r) (u+r), ENNReal.ofReal (finiteCubicVariation
        (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ (2 / 3 : ℝ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
    apply lintegral_congr
    intro x
    rw [cubicVariation_sq]
    exact (ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)).symm
  change (∫⁻ x in Icc (u-r) (u+r), ENNReal.ofReal (finiteCubicVariation
    (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ (2 / 3 : ℝ)) ≤
      ENNReal.ofReal (A * P.constant ^ 2 * B * r) at he
  rw [← heq] at he
  have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ A * P.constant ^ 2 * B * r)] using ht


theorem uniform_line_moment (hL : LepingleInput) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : LinePacketFamily N κ ι) (B : ℝ), 0 ≤ B → P.HasLocalBudget B →
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
  obtain ⟨A,hA,hshort⟩ := uniform_short_energy hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P B hB hbudget hlow hhigh g hb hwidth p hp
  have hD : 0 ≤ A * P.constant ^ 2 * B := by positivity
  have hs := hshort N κ ι P B hB hbudget hlow hhigh
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
