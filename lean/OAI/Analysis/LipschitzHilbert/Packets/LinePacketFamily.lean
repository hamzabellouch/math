import OAI.Analysis.LipschitzHilbert.Fourier.ShortLineVariation
import OAI.Analysis.LipschitzHilbert.Fourier.LongLineVariation
import OAI.Analysis.LipschitzHilbert.Fourier.VariationLineBMO

namespace OAI

/-! Actual finite packet data on a reference line, with local coefficient
budgets kept explicit. No concentration or synthesis estimate is part of
the data. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform ENNReal

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

structure LinePacketFamily (N : ℕ) (κ : Type) (ι : Fin N → Type)
    [Fintype κ] [∀ j, Fintype (ι j)] where
  baseX : ℝ
  baseZ : ℝ
  topLength : ℝ
  width : ℝ
  lineY : ℝ
  constant : ℝ
  topLength_pos : 0 < topLength
  width_pos : 0 < width
  constant_pos : 0 < constant
  coeff : ∀ j, ι j → EuclideanSpace ℂ κ
  wave : ∀ j, ι j → κ → SchwartzMap ℝ ℂ
  site : ∀ j, ι j → ℤ × ℤ
  site_injective : ∀ j, Function.Injective (site j)
  coeff_norm : ∀ j i, ‖coeff j i‖ ≤ 1
  wave_bound : ∀ j i k x, ‖wave j i k x‖ ≤ constant *
    (lineEnvelope (baseX + (topLength / (2 : ℝ) ^ j.val) * (site j i).1)
      (topLength / (2 : ℝ) ^ j.val) 3 x *
      lineEnvelope (baseZ + width * (site j i).2) width 2 lineY)
  deriv_bound : ∀ j i k x, ‖deriv (wave j i k) x‖ ≤
    (constant / (topLength / (2 : ℝ) ^ j.val)) *
    (lineEnvelope (baseX + (topLength / (2 : ℝ) ^ j.val) * (site j i).1)
      (topLength / (2 : ℝ) ^ j.val) 3 x *
      lineEnvelope (baseZ + width * (site j i).2) width 2 lineY)

namespace LinePacketFamily

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

def length (P : LinePacketFamily N κ ι) (j : Fin N) : ℝ := P.topLength / (2 : ℝ) ^ j.val
def centerX (P : LinePacketFamily N κ ι) (j : Fin N) (i : ι j) : ℝ :=
  P.baseX + P.length j * (P.site j i).1
def centerZ (P : LinePacketFamily N κ ι) (j : Fin N) (i : ι j) : ℝ :=
  P.baseZ + P.width * (P.site j i).2
def packets (P : LinePacketFamily N κ ι) (j : Fin N) (k : κ) : SchwartzMap ℝ ℂ :=
  packetSynthesis (fun i => P.coeff j i k) (fun i => P.wave j i k)
def shortPackets (P : LinePacketFamily N κ ι) (r : ℝ) (j : Fin N) (k : κ) : SchwartzMap ℝ ℂ :=
  if P.length j ≤ r then P.packets j k else 0
def longPackets (P : LinePacketFamily N κ ι) (r : ℝ) (j : Fin N) (k : κ) : SchwartzMap ℝ ℂ :=
  if r < P.length j then P.packets j k else 0
def variation (P : LinePacketFamily N κ ι) (x : ℝ) : ℝ :=
  cubicVariation (fun n => hilbertPartialBandSum P.packets n x) N

def HasLocalBudget (P : LinePacketFamily N κ ι) (B : ℝ) : Prop :=
  ∀ u r : ℝ, 0 < r → ∀ b : ℤ × ℤ,
    (∑ j, P.length j * ∑ i : ShortBoxFiber P.length
      (centerBoxIndex P.centerX P.centerZ u P.lineY r P.width) r b j, ‖P.coeff j i‖ ^ 2) ≤ B * r

theorem length_pos (P : LinePacketFamily N κ ι) (j : Fin N) : 0 < P.length j :=
  div_pos P.topLength_pos (pow_pos (by norm_num) _)

theorem continuous_variation (P : LinePacketFamily N κ ι) : Continuous P.variation :=
  continuous_cubicVariation _ (hilbertPartialBandSum_continuous P.packets) N

theorem partial_sum_split (P : LinePacketFamily N κ ι) (r : ℝ) (n : ℕ) (x : ℝ) :
    hilbertPartialBandSum P.packets n x =
      hilbertPartialBandSum (P.shortPackets r) n x +
      hilbertPartialBandSum (P.longPackets r) n x := by
  ext k
  change partialBandSum (fun j => P.packets j k) n x =
    partialBandSum (fun j => P.shortPackets r j k) n x +
      partialBandSum (fun j => P.longPackets r j k) n x
  unfold partialBandSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < n
  · simp only [hj, ite_true]
    by_cases hlen : P.length j ≤ r
    · simp only [shortPackets, longPackets, ite_eq_left hlen, ite_eq_right (not_lt.mpr hlen),
        zero_apply, add_zero]
    · simp only [shortPackets, longPackets, ite_eq_right hlen, ite_eq_left (lt_of_not_ge hlen),
        zero_apply, zero_add]
  · simp only [hj, ite_false, zero_add]

theorem long_oscillation (P : LinePacketFamily N κ ι) (u r : ℝ) (hr : 0 < r)
    {x z : ℝ} (hx : x ∈ Icc (u-r) (u+r)) (hz : z ∈ Icc (u-r) (u+r)) :
    cubicVariation (fun n => hilbertPartialBandSum (P.longPackets r) n x -
      hilbertPartialBandSum (P.longPackets r) n z) N ≤ 4 * (P.constant * (4 * Real.pi) ^ 2) :=
  long_line_variation P.coeff P.wave P.site P.site_injective P.baseX P.baseZ
    P.topLength P.width P.lineY u r P.constant P.topLength_pos P.width_pos.ne' hr
    P.constant_pos.le P.coeff_norm P.deriv_bound hx hz

theorem short_energy (hL : LepingleInput) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : LinePacketFamily N κ ι) (B : ℝ), 0 ≤ B → P.HasLocalBudget B →
      (∀ j i k ξ, |ξ| < lo * (2 : ℝ) ^ j.val → 𝓕 (P.wave j i k) ξ = 0) →
      (∀ j i k ξ, hi * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (P.wave j i k) ξ = 0) →
      ∀ u r : ℝ, 0 < r →
      (∫ x in Icc (u-r) (u+r),
        (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ 2) ≤
        A * P.constant ^ 2 * B * r := by
  obtain ⟨A,hA,hshort⟩ := short_line_variation hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro P B hB hbudget hlow hhigh u r hr
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

end LinePacketFamily
end LipschitzHilbert

end

end OAI
