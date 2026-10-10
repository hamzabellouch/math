import OAI.Geometry.CylinderCovering.Caps.CapsDefinitions
import OAI.Geometry.CylinderCovering.Radial.CapCoverage

namespace OAI

open Set
noncomputable section
namespace CylinderCovering.HalfHeightCaps

theorem covered_of_padding {δ : ℝ} {R b : ℝ → ℝ}
    (hδ : 0 < δ)
    (hcap : ∀ r ∈ Icc (-1 : ℝ) 1,
      2 * R r = 1 + (δ / 2) ^ 2 * (RadialCaps.H r + b r))
    (hb : ∀ r ∈ Icc (-1 : ℝ) 1, 0 ≤ b r)
    (hpadding : ∀ p ∈ Icc (-1 : ℝ) 1, ∀ q ∈ Icc (-1 : ℝ) 1,
      9 * (δ / 2) ≤ b p + b q) : Covered δ R := by
  intro X Y Z hX hY
  have hx : |2 * Y| ≤ 1 + (2 * Z - 1) := by
    rw [abs_mul]
    norm_num
    linarith only [hY]
  have hy : |2 * X| ≤ 1 - (2 * Z - 1) := by
    rw [abs_mul]
    norm_num
    linarith only [hX]
  have h := RadialCapCoverage.padding_coverage (eps := δ / 2)
    (R := fun r => 2 * R r) (b := b) (by positivity) hcap hb hpadding hx hy
  rcases h with ⟨q, ρ, hq, hρ, hR, heq, ht⟩ | ⟨p, σ, hp, hσ, hR, heq, ht⟩
  · right
    refine ⟨q, ρ / 2, hq, by positivity, by linarith only [hR], ?_, ?_⟩
    · unfold alpha
      unfold RadialCaps.G at heq
      nlinarith only [heq]
    · unfold beta
      nlinarith only [ht]
  · left
    refine ⟨p, σ / 2, hp, by positivity, by linarith only [hR], ?_, ?_⟩
    · unfold alpha
      unfold RadialCaps.G at heq
      nlinarith only [heq]
    · unfold beta
      nlinarith only [ht]

theorem cubic_dictionary (δ r : ℝ) :
    2 * cubicCap δ r = RadialCaps.cubicCap 64 (δ / 2) r := by
  unfold cubicCap F RadialCaps.cubicCap RadialCaps.H
  ring

theorem cubic_covers {δ : ℝ} (hδ : 0 < δ) : Covered δ (cubicCap δ) := by
  apply covered_of_padding (b := fun _ => 32 * δ) hδ
  · intro r hr
    unfold cubicCap F RadialCaps.H
    ring
  · intro r hr
    positivity
  · intro p hp q hq
    linarith only [hδ]

theorem fractional_covers {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1) :
    Covered δ (fractionalCap δ) := by
  have hs : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hs1 : Real.sqrt δ ≤ 1 := by nlinarith [Real.sq_sqrt hδ.le]
  have hδs : δ ≤ Real.sqrt δ := by nlinarith [Real.sq_sqrt hδ.le]
  apply covered_of_padding (b := fun _ => 8 * Real.sqrt δ) hδ
  · intro r hr
    unfold fractionalCap F RadialCaps.H
    rw [RadialCapCoverage.fractional_power δ hδ]
    ring
  · intro r hr
    positivity
  · intro p hp q hq
    nlinarith only [hδs, hs]

theorem fractional_dictionary {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    2 * fractionalCap δ r = RadialCaps.fractionalCap (8 * Real.sqrt 2) (δ / 2) r := by
  unfold fractionalCap RadialCaps.fractionalCap F RadialCaps.H
  rw [RadialCapCoverage.fractional_power δ hδ,
    RadialCapCoverage.fractional_power (δ / 2) (by positivity), Real.sqrt_div hδ.le]
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  nlinarith only [hs2]

theorem halfheight_coverage : CoverageStatement := by
  refine ⟨fun δ hδ => cubic_covers hδ, ⟨1, by norm_num, ?_⟩,
    cubic_dictionary, ?_⟩
  · exact fun δ hδ hs => fractional_covers hδ hs
  · exact fun δ r hδ => fractional_dictionary hδ r

theorem compensation : CompensationStatement := by
  intro δ X Y Z r s u v hY hZ hX hZv
  unfold alpha beta at *
  linear_combination δ * X * hY - δ * Y * hX - hZ - hZv

theorem physical_covers_of_covered {δ : ℝ} {R : ℝ → ℝ} (h : Covered δ R) :
    physicalTetrahedron ⊆ firstPhysicalSweep δ R ∪ secondPhysicalSweep δ R := by
  rintro z ⟨X, Y, Z, hX, hY, rfl⟩
  have hX1 : |X| ≤ 1 := by linarith only [hX, hY, abs_nonneg Y]
  have hY1 : |Y| ≤ 1 := by linarith only [hX, hY, abs_nonneg X]
  rcases h X Y Z hX hY with ⟨r, u, hr, hu, hR, hYr, hZr⟩ |
    ⟨s, v, hs, hv, hR, hXs, hZs⟩
  · left
    refine ⟨r, abs_le.mp hr, u, ⟨hu, hR⟩, X, hX1, ?_⟩
    rw [← hYr, ← hZr]
  · right
    refine ⟨s, abs_le.mp hs, v, ⟨hv, hR⟩, Y, hY1, ?_⟩
    have hZs' : Z = 1 - v + δ * Y * beta s := by linarith only [hZs]
    rw [← hXs, ← hZs']

theorem halfheight_physical_coverage : PhysicalCoverageStatement := by
  constructor
  · exact fun δ hδ => physical_covers_of_covered (cubic_covers hδ)
  · exact fun δ hδ hs => physical_covers_of_covered (fractional_covers hδ hs)

theorem fractional_defect (a X Y : ℝ) :
    X ^ 2 * (a / 2 + X ^ 2 / (2 * a)) + Y ^ 2 * (a / 2 + Y ^ 2 / (2 * a)) -
      (a / 2 + X ^ 2 / (2 * a)) * Y ^ 2 -
      (a / 2 + Y ^ 2 / (2 * a)) * X ^ 2 = (X ^ 2 - Y ^ 2) ^ 2 / (2 * a) := by
  ring

end CylinderCovering.HalfHeightCaps

end

end OAI
