import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.PlaneBoxGrowth
import OAI.Analysis.RieszRectifiability.Surfaces.NativeSurfaceArea
import OAI.Analysis.RieszRectifiability.Foundations.GlobalLowerDiameter

namespace OAI

/-!
Two-sided Hausdorff measure bounds yield a single AD constant for native surface area.
Global positive-dimensional lower growth also forces infinite support diameter.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal

def nativeSurfaceADConstant (n : ℕ) (c C : ℝ≥0∞) : ℝ :=
  1 + C.toReal + (c * (ENNReal.ofReal (1 / 2 : ℝ)) ^ n).toReal⁻¹

theorem nativeSurfaceArea_uniform_bounds {n d : ℕ}
    (A : Set (Ambient d)) (c C : ℝ≥0∞) (hc : 0 < c) (hcfin : c < ⊤) (hC : C < ⊤)
    (hlower : ∀ p ∈ A, ∀ r : ℝ, 0 < r →
      c * (ENNReal.ofReal r) ^ n ≤
        (μH[(n : ℝ)] : Measure (Ambient d)) (A ∩ closedBall p r))
    (hupper : ∀ (p : Ambient d) (r : ℝ), 0 < r →
      (μH[(n : ℝ)] : Measure (Ambient d)) (A ∩ closedBall p r) ≤
        C * (ENNReal.ofReal r) ^ n) :
    1 ≤ nativeSurfaceADConstant n c C ∧
      GlobalUpperGrowth n (nativeSurfaceADConstant n c C) (nativeSurfaceArea n A) ∧
      ∀ p ∈ A, ∀ r : ℝ, 0 < r →
        ENNReal.ofReal (r ^ n / nativeSurfaceADConstant n c C) ≤
          nativeSurfaceArea n A (ball p r) := by
  let l : ℝ≥0∞ := c * (ENNReal.ofReal (1 / 2 : ℝ)) ^ n
  have hlpos : 0 < l := by dsimp only [l]; positivity
  have hlfin : l < ⊤ := ENNReal.mul_lt_top hcfin (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  have hlreal : 0 < l.toReal := ENNReal.toReal_pos_iff.mpr ⟨hlpos, hlfin⟩
  have hCnonneg : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hK1 : 1 ≤ nativeSurfaceADConstant n c C := by
    change 1 ≤ 1 + C.toReal + l.toReal⁻¹
    have : 0 ≤ l.toReal⁻¹ := (inv_pos.mpr hlreal).le
    linarith
  have hKC : C.toReal ≤ nativeSurfaceADConstant n c C := by
    change C.toReal ≤ 1 + C.toReal + l.toReal⁻¹
    have : 0 ≤ l.toReal⁻¹ := (inv_pos.mpr hlreal).le
    linarith
  have hKinv : l.toReal⁻¹ ≤ nativeSurfaceADConstant n c C := by
    change l.toReal⁻¹ ≤ 1 + C.toReal + l.toReal⁻¹
    linarith
  refine ⟨hK1, (nativeSurfaceArea_global_upper_growth A C hC hupper).mono_constant hKC, ?_⟩
  intro p hp r hr
  have hKpos : 0 < nativeSurfaceADConstant n c C := zero_lt_one.trans_le hK1
  have hprod : 1 ≤ l.toReal * nativeSurfaceADConstant n c C := by
    have h := mul_le_mul_of_nonneg_left hKinv hlreal.le
    simpa only [mul_inv_cancel₀ hlreal.ne'] using! h
  have hdiv : r ^ n / nativeSurfaceADConstant n c C ≤ l.toReal * r ^ n := by
    apply (div_le_iff₀ hKpos).mpr
    calc
      r ^ n = 1 * r ^ n := (one_mul _).symm
      _ ≤ (l.toReal * nativeSurfaceADConstant n c C) * r ^ n :=
        mul_le_mul_of_nonneg_right hprod (pow_nonneg hr.le n)
      _ = (l.toReal * r ^ n) * nativeSurfaceADConstant n c C := by ring
  have h := nativeSurfaceArea_open_ball_lower A c hlower p hp r hr
  have heq : ENNReal.ofReal (l.toReal * r ^ n) = l * (ENNReal.ofReal r) ^ n := by
    rw [ENNReal.ofReal_mul hlreal.le, ENNReal.ofReal_toReal hlfin.ne, ENNReal.ofReal_pow hr.le]
  exact (ENNReal.ofReal_le_ofReal hdiv).trans (heq.symm ▸ h)

theorem nativeSurfaceArea_adRegular {n d : ℕ}
    (A : Set (Ambient d)) (hA : IsClosed A)
    (c C : ℝ≥0∞) (hc : 0 < c) (hcfin : c < ⊤) (hC : C < ⊤)
    (hlower : ∀ p ∈ A, ∀ r : ℝ, 0 < r →
      c * (ENNReal.ofReal r) ^ n ≤
        (μH[(n : ℝ)] : Measure (Ambient d)) (A ∩ closedBall p r))
    (hupper : ∀ (p : Ambient d) (r : ℝ), 0 < r →
      (μH[(n : ℝ)] : Measure (Ambient d)) (A ∩ closedBall p r) ≤
        C * (ENNReal.ofReal r) ^ n) :
    ADRegular n (nativeSurfaceArea n A) := by
  obtain ⟨hK, hg, hl⟩ := nativeSurfaceArea_uniform_bounds A c C hc hcfin hC hlower hupper
  refine ⟨nativeSurfaceADConstant n c C, hK, ?_⟩
  intro p hp r hr
  rw [nativeSurfaceArea_support A hA c hc hlower] at hp
  exact ⟨hl p hp r hr.1, hg.2 p r hr.1⟩

theorem nativeSurfaceArea_support_ediam_top {n d : ℕ} (hn : 0 < n)
    (A : Set (Ambient d)) (hA : IsClosed A) (hne : A.Nonempty)
    (c C : ℝ≥0∞) (hc : 0 < c) (hcfin : c < ⊤) (hC : C < ⊤)
    (hlower : ∀ p ∈ A, ∀ r : ℝ, 0 < r →
      c * (ENNReal.ofReal r) ^ n ≤
        (μH[(n : ℝ)] : Measure (Ambient d)) (A ∩ closedBall p r))
    (hupper : ∀ (p : Ambient d) (r : ℝ), 0 < r →
      (μH[(n : ℝ)] : Measure (Ambient d)) (A ∩ closedBall p r) ≤
        C * (ENNReal.ofReal r) ^ n) :
    ediam (nativeSurfaceArea n A).support = ⊤ := by
  let : (nativeSurfaceArea n A).Regular := nativeSurfaceArea_regular A C hC hupper
  have hs := nativeSurfaceArea_support A hA c hc hlower
  obtain ⟨hK, _, hl⟩ := nativeSurfaceArea_uniform_bounds A c C hc hcfin hC hlower hupper
  have hKpos : 0 < nativeSurfaceADConstant n c C := zero_lt_one.trans_le hK
  have hnz : nativeSurfaceArea n A ≠ 0 := by
    intro hz
    obtain ⟨p, hp⟩ := hne
    have h := hl p hp 1 (by norm_num)
    rw [hz] at h
    have hpos : 0 < ENNReal.ofReal ((1 : ℝ) ^ n / nativeSurfaceADConstant n c C) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    exact (not_le_of_gt hpos) (by simpa using! h)
  exact global_lower_growth_support_ediam_top n hn (nativeSurfaceArea n A) hnz
    (nativeSurfaceADConstant n c C) hKpos (fun p hp r hr => hl p (hs ▸ hp) r hr)

end

end RieszRectifiability

end OAI
