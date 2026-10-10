import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.LatticeDescendantGeometry

namespace OAI

/-!
# Mass bounds for lattice descendants

Each descendant cell is contained in a ball with controlled radius. Global
upper growth therefore bounds its mass by a constant times the corresponding
power of its radius, both in extended and real-valued form.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem SupportCellDescendant.measure_upper {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (G : ℝ) (hg : GlobalUpperGrowth n G μ) :
    μ i.cell ≤ ENNReal.ofReal (G * (3 * i.radius) ^ n) := by
  have hr := i.radius_pos
  have hs := (supportLatticeCell_bounds μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩).2
  have hb : closedBall i.center (2 * i.radius) ⊆ ball i.center (3 * i.radius) :=
    closedBall_subset_ball (by linarith [i.radius_pos])
  exact (measure_mono ((sdiff_subset.trans hs).trans hb)).trans
    (hg.2 i.center (3 * i.radius) (by positivity))

theorem SupportCellDescendant.real_measure_upper {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (G : ℝ) (hg : GlobalUpperGrowth n G μ) :
    μ.real i.cell ≤ (G * 3 ^ n) * i.radius ^ n := by
  have hG := hg.1
  have hr := i.radius_pos
  have hb := ENNReal.toReal_le_of_le_ofReal
    (by positivity : 0 ≤ G * (3 * i.radius) ^ n) (i.measure_upper G hg)
  simpa only [mul_pow, mul_assoc, Measure.real] using! hb

theorem cleanSupportCell_real_measure_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    (latticeRadius R k / 8) ^ n / C ≤ μ.real (cleanSupportCell μ R hR k z) ∧
      μ.real (cleanSupportCell μ R hR k z) ≤ (G * 3 ^ n) * latticeRadius R k ^ n := by
  have hr := latticeRadius_pos R hR k
  have hb := cleanSupportCell_measure_bounds μ C G hC hG hg hlower R hR k hcore z
  have hf : μ (cleanSupportCell μ R hR k z) ≠ ∞ := (hb.2.trans_lt ENNReal.ofReal_lt_top).ne
  constructor
  · simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (latticeRadius R k / 8) ^ n / C),
      Measure.real] using! ENNReal.toReal_mono hf hb.1
  · have hu := ENNReal.toReal_le_of_le_ofReal
      (by positivity : 0 ≤ G * (3 * latticeRadius R k) ^ n) hb.2
    simpa only [mul_pow, mul_assoc, Measure.real] using! hu

def latticeMassPackingConstant (n : ℕ) (C G B : ℝ) : ℝ :=
  G * 3 ^ n * B * 2 ^ n * C * 8 ^ n

theorem latticeMassPackingConstant_pos (n : ℕ) (C G B : ℝ)
    (hC : 0 < C) (hG : 0 < G) (hB : 0 < B) : 0 < latticeMassPackingConstant n C G B := by
  unfold latticeMassPackingConstant
  positivity

theorem cell_mass_packing_of_radius_packing {ι : Type*} {n d : ℕ}
    (μ : Measure (Ambient d)) (C G B : ℝ) (hC : 0 < C) (hG : 0 < G) (hB : 0 ≤ B)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (f : ι → SupportCellDescendant μ R hR k z) (s : Finset ι)
    (hpack : ∑ i ∈ s, (f i).radius ^ n ≤ B * (2 * latticeRadius R k) ^ n) :
    ∑ i ∈ s, μ.real (f i).cell ≤
      latticeMassPackingConstant n C G B * μ.real (cleanSupportCell μ R hR k z) := by
  have hl := (cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR k hcore z).1
  have hK : 0 ≤ latticeMassPackingConstant n C G B := by
    unfold latticeMassPackingConstant
    positivity
  have hid : (G * 3 ^ n) * (B * (2 * latticeRadius R k) ^ n) =
      latticeMassPackingConstant n C G B * ((latticeRadius R k / 8) ^ n / C) := by
    unfold latticeMassPackingConstant
    simp only [mul_pow, div_pow]
    field_simp
  calc
    _ ≤ ∑ i ∈ s, (G * 3 ^ n) * (f i).radius ^ n :=
      Finset.sum_le_sum (fun i _ => (f i).real_measure_upper G hg)
    _ = (G * 3 ^ n) * ∑ i ∈ s, (f i).radius ^ n := (Finset.mul_sum ..).symm
    _ ≤ (G * 3 ^ n) * (B * (2 * latticeRadius R k) ^ n) :=
      mul_le_mul_of_nonneg_left hpack (by positivity)
    _ = _ := hid
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hK

end

end RieszRectifiability

end OAI
