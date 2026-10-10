import OAI.Analysis.LipschitzHilbert.Packets.WeightedPacketEnergy

namespace OAI

/-! The actual finite packet data in one reference box. Coefficients are
left arbitrary for the weighted synthesis and subsequent duality argument. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

structure ReferencePacketFamily (N : ℕ) (κ : Type*) (ι : Fin N → Type*)
    [Fintype κ] [∀ j, Fintype (ι j)] where
  baseX : ℝ
  baseZ : ℝ
  centerX : ℝ
  centerZ : ℝ
  radius : ℝ
  width : ℝ
  constant : ℝ
  radius_pos : 0 < radius
  width_pos : 0 < width
  length : Fin N → ℝ
  length_pos : ∀ j, 0 < length j
  length_le : ∀ j, ∀ _ : ι j, length j ≤ radius
  site : ∀ j, ι j → ℤ × ℤ
  site_injective : ∀ j, Function.Injective (site j)
  center_x : ∀ j i, |baseX + length j * (site j i).1 - centerX| ≤ radius
  center_z : ∀ j i, |baseZ + width * (site j i).2 - centerZ| ≤ width
  wave : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ
  wave_bound : ∀ j i k y x, ‖wave j i k y x‖ ≤ constant *
    (lineEnvelope (baseX + length j * (site j i).1) (length j) 3 x *
     lineEnvelope (baseZ + width * (site j i).2) width 3 y)

namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
  [Fintype κ] [∀ j, Fintype (ι j)]

def packets (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (y : ℝ) (j : Fin N) (k : κ) :
    SchwartzMap ℝ ℂ := packetSynthesis (fun i => c j i k) (fun i => P.wave j i k y)

def coefficientEnergy (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) : ℝ :=
  ∑ j, P.length j * ∑ i, ‖c j i‖ ^ 2

theorem coefficientEnergy_nonneg (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) : 0 ≤ P.coefficientEnergy c := by
  unfold coefficientEnergy
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (P.length_pos j).le
    (Finset.sum_nonneg (fun i _ => sq_nonneg ‖c j i‖)))

theorem horizontal_energy (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (y : ℝ) :
    (∑ j, ∑ k, ∫ x, ‖polynomialLocalization P.centerX P.radius 1
      (P.packets c y j k) x‖ ^ 2) ≤
      ((4 * Real.pi)^2 * P.constant^2 * 16 * Real.pi) *
        ∑ j, P.length j * ∑ i, ‖c j i‖ ^ 2 *
          lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 3 y :=
  weighted_packet_energy c (fun j i k => P.wave j i k y)
    (fun j i => P.baseX + P.length j * (P.site j i).1)
    (fun j i => P.baseZ + P.width * (P.site j i).2)
    P.site P.length P.baseX P.baseZ P.centerX P.radius P.width y P.constant
    P.radius_pos P.width_pos P.length_pos P.length_le P.site_injective
    (fun _ _ => rfl) (fun _ _ => rfl) P.center_x
    (fun j i k x => P.wave_bound j i k y x)

theorem weighted_energy (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (y : ℝ) :
    polynomialWeight P.centerZ P.width 1 y ^ 2 *
      (∑ j, ∑ k, ∫ x, ‖polynomialLocalization P.centerX P.radius 1
        (P.packets c y j k) x‖ ^ 2) ≤
      ((4 * Real.pi)^2 * P.constant^2 * 256 * Real.pi) *
        ∑ j, P.length j * ∑ i, ‖c j i‖ ^ 2 *
          lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 1 y := by
  have hp (j : Fin N) (i : ι j) := polynomialWeight_sq_mul_envelope y
    (P.baseZ + P.width * (P.site j i).2) P.centerZ P.width P.width 1 1
    P.width_pos P.width_pos le_rfl (P.center_z j i)
  have hm : polynomialWeight P.centerZ P.width 1 y ^ 2 *
      (∑ j, P.length j * ∑ i, ‖c j i‖ ^ 2 *
        lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 3 y) ≤
      16 * (∑ j, P.length j * ∑ i, ‖c j i‖ ^ 2 *
        lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 1 y) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro i _
    calc
      _ = (P.length j * ‖c j i‖^2) *
          (polynomialWeight P.centerZ P.width 1 y ^ 2 *
            lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 3 y) := by ring
      _ ≤ (P.length j * ‖c j i‖^2) *
          (16 * lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 1 y) :=
        mul_le_mul_of_nonneg_left (by simpa only [pow_one] using hp j i)
          (mul_nonneg (P.length_pos j).le (sq_nonneg _))
      _ = _ := by ring

  calc
    _ ≤ polynomialWeight P.centerZ P.width 1 y ^ 2 *
        (((4 * Real.pi)^2 * P.constant^2 * 16 * Real.pi) * _) :=
      mul_le_mul_of_nonneg_left (P.horizontal_energy c y) (sq_nonneg _)
    _ = ((4 * Real.pi)^2 * P.constant^2 * 16 * Real.pi) *
        (polynomialWeight P.centerZ P.width 1 y ^ 2 * _) := by ring
    _ ≤ ((4 * Real.pi)^2 * P.constant^2 * 16 * Real.pi) * (16 * _) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
