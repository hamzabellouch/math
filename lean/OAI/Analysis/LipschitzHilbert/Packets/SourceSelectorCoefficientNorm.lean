import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalSingleScale
import OAI.Analysis.LipschitzHilbert.Packets.AnalyzingCoefficientNorm

namespace OAI

/-! Uniform coefficient normalization for the original smooth selectors.
It uses the physical analyzing packet, with no replacement of its selector
by a sharp cutoff and no dependence on the number of coordinates. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalMultiplierCoefficient_norm (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (l : P.labels j) (u : Item j l) :
    ‖P.physicalMultiplierCoefficient t b v g j l u‖ ≤ P.constant*Real.pi^2 := by
  let C : ℝ := (2^P.order*P.profileBound)*P.ratioBound^2
  let W : ℝ×ℝ → ℝ := fun z => C*
    (lineEnvelope (P.actualX j l u) (P.length j) 1 z.1*
      lineEnvelope (P.actualZ j l u) P.width 1 z.2)
  have hC : 0 < C := by
    have hR := zero_lt_one.trans_le P.ratioBound_ge_one
    have hP := P.profileBound_pos
    dsimp [C]
    positivity
  have hW : Integrable W :=
    ((integrable_lineEnvelope_one _ _ (P.length_pos j)).mul_prod
      (integrable_lineEnvelope_one _ _ P.width_pos)).const_mul C
  have hW0 (z : ℝ×ℝ) : 0 ≤ W z := by
    dsimp [W]
    exact mul_nonneg hC.le (mul_nonneg (lineEnvelope_nonneg _ _ _ _)
      (lineEnvelope_nonneg _ _ _ _))
  let test := fun z => g (slopeShear t z)
  let wave := fun (u : Item j l) (k : κ) (z : ℝ×ℝ) =>
    b j l k (v (slopeShear t z))*P.raw 0 j l u k z.2 z.1
  have htest : Measurable test := hg.comp (slopeShear t).measurable
  have hwave (k : κ) : Measurable (wave u k) :=
    ((hb j l k).comp (hv.comp (slopeShear t).measurable)).mul
      (P.raw_swapped_joint_measurable 0 j l u k)
  have hbound (k : κ) (z : ℝ×ℝ) : ‖wave u k z‖ ≤ W z := by
    have hr := P.raw_absolute_envelope 0 j l u k z.2 z.1
    have ho : 1 ≤ P.order := by have := P.order_ge_three; omega
    have he : lineEnvelope (P.actualX j l u) (P.length j) P.order z.1*
        lineEnvelope (P.actualZ j l u) P.width P.order z.2 ≤
      lineEnvelope (P.actualX j l u) (P.length j) 1 z.1*
        lineEnvelope (P.actualZ j l u) P.width 1 z.2 :=
      mul_le_mul (lineEnvelope_antitone _ _ _ ho) (lineEnvelope_antitone _ _ _ ho)
        (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
    have hr' : ‖P.raw 0 j l u k z.2 z.1‖ ≤ W z :=
      hr.trans (mul_le_mul_of_nonneg_left he hC.le)
    dsimp only [wave]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hb1 j l k _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hr')
  have hint (k : κ) : Integrable (fun z => test z k*conj (wave u k z)) := by
    have hgm : Measurable (fun z => test z k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp htest)
    apply hW.mono' (hgm.mul (continuous_star.measurable.comp (hwave k))).aestronglyMeasurable
    filter_upwards [] with z
    change ‖test z k*conj (wave u k z)‖ ≤ W z
    rw [norm_mul,Complex.norm_conj]
    have hk : ‖test z k‖ ≤ 1 := (PiLp.norm_apply_le (test z) k).trans (hg1 _)
    exact (mul_le_mul_of_nonneg_right hk (norm_nonneg _)).trans
      (by simpa only [one_mul] using hbound k z)
  have hn := analyzingCoefficient_norm_le volume (fun _ : Item j l => P.length j*P.width)
    wave test u W (mul_pos (P.length_pos j) P.width_pos) hW hW0 hint
    (fun z => hg1 _) hbound
  have hI : (∫ z, W z) = (C*Real.pi^2)*(P.length j*P.width) := by
    dsimp only [W]
    rw [integral_const_mul,Measure.volume_eq_prod,integral_prod_mul,
      integral_lineEnvelope_one _ _ (P.length_pos j),
      integral_lineEnvelope_one _ _ P.width_pos]
    ring
  rw [hI] at hn
  have hn' : ‖P.physicalMultiplierCoefficient t b v g j l u‖ ≤ C*Real.pi^2 := by
    have harea : P.length j*P.width ≠ 0 := (mul_pos (P.length_pos j) P.width_pos).ne'
    have hcancel : (P.length j*P.width)⁻¹*(C*Real.pi^2*(P.length j*P.width)) =
        C*Real.pi^2 := by
      calc
        _ = (C*Real.pi^2)*((P.length j*P.width)⁻¹*(P.length j*P.width)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ harea,mul_one]
    rw [hcancel] at hn
    rw [← P.physicalMultiplierCoefficient_shear t b v g j l u]
    exact hn
  have hc : C ≤ P.constant := by
    have hcar : 1 ≤ P.carrierBound+2 := by linarith [P.carrierBound_nonneg]
    have hpow : (1:ℝ) ≤ 3^(2*P.order) := one_le_pow₀ (by norm_num)
    calc
      C = C*1*1 := by ring
      _ ≤ C*(P.carrierBound+2)*3^(2*P.order) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcar hC.le) hpow
          (by norm_num) (mul_nonneg hC.le (by linarith))
      _ = P.constant := by dsimp [C,constant]; ring
  exact hn'.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
