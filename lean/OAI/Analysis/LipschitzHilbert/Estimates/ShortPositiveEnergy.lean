import OAI.Analysis.LipschitzHilbert.Packets.PositivePacketSquare

namespace OAI

/-! Summation of the positive coefficient energy over actual short-scale
center boxes. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.LinePacketFamily

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

theorem short_coefficient_energy (P : LinePacketFamily N κ ι) (u r B : ℝ)
    (hr : 0 < r) (hB : 0 ≤ B) (hbudget : P.HasLocalBudget B) :
    (∫ x in Icc (u-r) (u+r), ∑ j, if P.length j ≤ r then P.coefficientEnergy j x else 0) ≤
      (65536 * Real.pi) * (B*r) * (4 * Real.pi) ^ 4 := by
  let index := centerBoxIndex P.centerX P.centerZ u P.lineY r P.width
  let boxes := allPacketBoxes index
  let E := fun b x => ∑ j, ∑ i : ShortBoxFiber P.length index r b j,
    ‖P.coeff j i‖ ^ 2 * P.envelope j i x
  have heq (x : ℝ) : (∑ j, if P.length j ≤ r then P.coefficientEnergy j x else 0) =
      ∑ b ∈ boxes, E b x := by
    simp only [coefficientEnergy]
    simp_rw [short_sum_eq_boxes P.length index r (fun j i => ‖P.coeff j i‖ ^ 2 * P.envelope j i x)]
    exact Finset.sum_comm
  have hi (b : ℤ × ℤ) : IntegrableOn (E b) (Icc (u-r) (u+r)) :=
    integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ =>
      ((P.envelope_integrable j i).const_mul _).restrict))
  have hweight : (∑ b ∈ boxes, boxVariationWeight b ^ 2) ≤ (4 * Real.pi) ^ 4 := by
    have hw := boxVariationWeight_sum (fun b : {b // b ∈ boxes} => b.val) Subtype.val_injective
    have hsum := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := fun b : {b // b ∈ boxes} => boxVariationWeight b)
      (fun b _ => (boxVariationWeight_pos b).le)
    have hn : 0 ≤ ∑ b : {b // b ∈ boxes}, boxVariationWeight b :=
      Finset.sum_nonneg (fun b _ => (boxVariationWeight_pos b).le)
    have hpow := pow_le_pow_left₀ hn hw 2
    have h := hsum.trans hpow
    rw [Finset.sum_subtype boxes (fun _ => Iff.rfl) (fun b => boxVariationWeight b ^ 2)]
    convert h using 1
    ring
  simp_rw [heq]
  rw [integral_finsetSum _ (fun b _ => hi b)]
  calc
    _ ≤ ∑ b ∈ boxes, (65536 * Real.pi) * (B*r) * boxVariationWeight b ^ 2 :=
      Finset.sum_le_sum (fun b _ => P.box_coefficient_energy u r B hr hB hbudget b)
    _ = (65536 * Real.pi) * (B*r) * ∑ b ∈ boxes, boxVariationWeight b ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)

end LipschitzHilbert.LinePacketFamily

end

end OAI
