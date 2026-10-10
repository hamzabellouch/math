import OAI.Analysis.LipschitzHilbert.Packets.LinePacketFamily
import OAI.Analysis.LipschitzHilbert.Estimates.LocalizedEnvelope
import OAI.Analysis.LipschitzHilbert.Estimates.ShortPositiveBoxes

namespace OAI

/-! The positive lattice square estimate and local coefficient energy on
one reference line. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.LinePacketFamily

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

def envelope (P : LinePacketFamily N κ ι) (j : Fin N) (i : ι j) (x : ℝ) : ℝ :=
  lineEnvelope (P.centerX j i) (P.length j) 3 x * lineEnvelope (P.centerZ j i) P.width 2 P.lineY

def positiveScale (P : LinePacketFamily N κ ι) (j : Fin N) (x : ℝ) : ℝ :=
  ∑ i, ‖P.coeff j i‖ * P.envelope j i x

def coefficientEnergy (P : LinePacketFamily N κ ι) (j : Fin N) (x : ℝ) : ℝ :=
  ∑ i, ‖P.coeff j i‖ ^ 2 * P.envelope j i x

theorem envelope_nonneg (P : LinePacketFamily N κ ι) (j : Fin N) (i : ι j) (x : ℝ) :
    0 ≤ P.envelope j i x := mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem envelope_integrable (P : LinePacketFamily N κ ι) (j : Fin N) (i : ι j) :
    Integrable (P.envelope j i) :=
  (integrable_lineEnvelope (P.centerX j i) (P.length j) (P.length_pos j) (by decide : 1 ≤ 3)).mul_const _

theorem envelope_overlap (P : LinePacketFamily N κ ι) (j : Fin N) (x : ℝ) :
    (∑ i, P.envelope j i x) ≤ (4 * Real.pi) ^ 2 :=
  injective_tile_lattice_overlap (P.site j) (P.site_injective j) P.baseX P.baseZ
    (P.length j) P.width x P.lineY (P.length_pos j).ne' P.width_pos.ne' (by decide) (by decide)

theorem positiveScale_square (P : LinePacketFamily N κ ι) (j : Fin N) (x : ℝ) :
    P.positiveScale j x ^ 2 ≤ (4 * Real.pi) ^ 2 * P.coefficientEnergy j x := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := fun i => P.envelope j i x) (g := fun i => ‖P.coeff j i‖ ^ 2 * P.envelope j i x)
    (r := fun i => ‖P.coeff j i‖ * P.envelope j i x)
    (fun i _ => P.envelope_nonneg j i x)
    (fun i _ => mul_nonneg (sq_nonneg _) (P.envelope_nonneg j i x))
    (fun i _ => by ring_nf; exact le_rfl)
  exact h.trans (mul_le_mul_of_nonneg_right (P.envelope_overlap j x)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (P.envelope_nonneg j i x))))

theorem positiveScale_bound (P : LinePacketFamily N κ ι) (j : Fin N) (x : ℝ) :
    0 ≤ P.positiveScale j x ∧ P.positiveScale j x ≤ (4 * Real.pi) ^ 2 := by
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (P.envelope_nonneg j i x)), ?_⟩
  apply le_trans _ (P.envelope_overlap j x)
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_right (P.coeff_norm j i) (P.envelope_nonneg j i x)).trans_eq (one_mul _)

theorem box_coefficient_energy (P : LinePacketFamily N κ ι) (u r B : ℝ) (hr : 0 < r)
    (_hB : 0 ≤ B) (hbudget : P.HasLocalBudget B) (b : ℤ × ℤ) :
    (∫ x in Icc (u-r) (u+r), ∑ j,
      ∑ i : ShortBoxFiber P.length (centerBoxIndex P.centerX P.centerZ u P.lineY r P.width) r b j,
        ‖P.coeff j i‖ ^ 2 * P.envelope j i x) ≤
      (65536 * Real.pi) * (B*r) * boxVariationWeight b ^ 2 := by
  let index := centerBoxIndex P.centerX P.centerZ u P.lineY r P.width
  have hint (j : Fin N) (i : ShortBoxFiber P.length index r b j) :
      IntegrableOn (fun x => ‖P.coeff j i‖ ^ 2 * P.envelope j i x) (Icc (u-r) (u+r)) :=
    ((P.envelope_integrable j i).const_mul _).restrict
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hint j i))]
  have hpoint (j : Fin N) (i : ShortBoxFiber P.length index r b j) :
      (∫ x in Icc (u-r) (u+r), ‖P.coeff j i‖ ^ 2 * P.envelope j i x) ≤
        (65536 * Real.pi) * boxVariationWeight b ^ 2 * (P.length j * ‖P.coeff j i‖ ^ 2) := by
    rw [integral_const_mul]
    have hx : |P.centerX j i - (u+r*b.1)| ≤ r := by
      have h := packetBoxIndex_horizontal u P.lineY r P.width (P.centerX j i) (P.centerZ j i) hr
      change _ ≤ r at h
      rw [show packetBoxIndex u P.lineY r P.width (P.centerX j i) (P.centerZ j i) = b from i.property.2] at h
      exact h
    have hz : |P.centerZ j i - (P.lineY+P.width*b.2)| ≤ P.width := by
      have h := packetBoxIndex_vertical u P.lineY r P.width (P.centerX j i) (P.centerZ j i) P.width_pos
      rw [show packetBoxIndex u P.lineY r P.width (P.centerX j i) (P.centerZ j i) = b from i.property.2] at h
      exact h
    have h := mul_le_mul_of_nonneg_left
      (local_tileEnvelope (P.centerX j i) (P.centerZ j i) u P.lineY (P.length j) r P.width b
        (P.length_pos j) hr P.width_pos i.property.1 hx hz) (sq_nonneg ‖P.coeff j i‖)
    convert h using 1
    · rfl
    · ring
  calc
    _ ≤ ∑ j, ∑ i : ShortBoxFiber P.length index r b j,
        (65536 * Real.pi) * boxVariationWeight b ^ 2 * (P.length j * ‖P.coeff j i‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      rw [integral_finsetSum _ (fun i _ => hint j i)]
      exact Finset.sum_le_sum (fun i _ => hpoint j i)
    _ = (65536 * Real.pi) * boxVariationWeight b ^ 2 *
        (∑ j, P.length j * ∑ i : ShortBoxFiber P.length index r b j, ‖P.coeff j i‖ ^ 2) := by
      simp only [Finset.mul_sum]
    _ ≤ (65536 * Real.pi) * boxVariationWeight b ^ 2 * (B*r) :=
      mul_le_mul_of_nonneg_left (hbudget u r hr b) (by positivity)
    _ = _ := by ring

end LipschitzHilbert.LinePacketFamily

end

end OAI
