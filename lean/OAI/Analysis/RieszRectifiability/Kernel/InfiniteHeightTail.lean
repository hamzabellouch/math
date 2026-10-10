import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.EnergyFromTruncations
import OAI.Analysis.RieszRectifiability.Kernel.ShiftedHeightTail

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem finiteShellRegion_measurable {d : ℕ} (a : Ambient d) (R : ℝ) (N : ℕ) :
    MeasurableSet (finiteShellRegion a R N) :=
  MeasurableSet.iUnion (fun k => MeasurableSet.iUnion (fun _ => dyadicAnnulus_measurable a R k))

theorem finiteShellRegion_monotone {d : ℕ} (a : Ambient d) (R : ℝ) :
    Monotone (finiteShellRegion a R) := by
  intro N M hNM y hy
  obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hy
  exact mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le hNM), hyk⟩

theorem infinite_shell_weighted_height_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (w : Ambient d → ℝ) (hwm : Measurable w)
    (hw : ∀ k, MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hsecond : ∀ k, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B * δ / R) / (1 - b / 2) := by
  classical
  let f := fun y => |w y| * inverseDistancePow (m + 2) a y
  let g := (closedExterior a R).indicator f
  have hm : Measurable g :=
    (hwm.abs.mul (inverseDistancePow_measurable (m + 2) a)).indicator (closedExterior_measurable a R)
  have hpos : ∀ y, 0 ≤ g y := fun _ => indicator_nonneg (fun _ _ =>
    mul_nonneg (abs_nonneg _) (inverseDistancePow_nonneg _ _ _)) _
  have hsub : ∀ N, finiteShellRegion a R N ⊆ closedExterior a R := by
    intro N y hy
    rw [finiteShellRegion_eq a R hR N] at hy
    exact hy.1
  have heq : ∀ N, EqOn f g (finiteShellRegion a R N) := by
    intro N y hy
    exact (indicator_of_mem (hsub N hy) f).symm
  have hcover : support g ⊆ ⋃ N, finiteShellRegion a R N := by
    intro y hy
    have hyext : y ∈ closedExterior a R := by
      by_contra h
      exact hy (indicator_of_notMem h f)
    obtain ⟨k, hk⟩ := mem_iUnion.mp (closedExterior_subset_iUnion_dyadicAnnulus a R hR hyext)
    exact mem_iUnion.mpr ⟨k + 1, mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), hk⟩⟩
  have hlocal := fun N => finite_shell_weighted_height_bound m C B μ hg hCB a R hR N w
    (fun k _ => hw k) δ b hδ hb0 hb2 (fun k _ => hsecond k)
  have hI : ∀ N, IntegrableOn g (finiteShellRegion a R N) μ :=
    fun N => (hlocal N).1.congr_fun (heq N) (finiteShellRegion_measurable a R N)
  have hbound : ∀ N, (∫ y in finiteShellRegion a R N, g y ∂μ) ≤ (B * δ / R) / (1 - b / 2) := by
    intro N
    have hi : (∫ y in finiteShellRegion a R N, g y ∂μ) = ∫ y in finiteShellRegion a R N, f y ∂μ :=
      setIntegral_congr_fun (finiteShellRegion_measurable a R N) (fun y hy => (heq N hy).symm)
    rw [hi]
    exact (hlocal N).2
  obtain ⟨hgI, hgB⟩ := nonnegative_integrable_of_exhaustion μ g hm hpos (finiteShellRegion a R)
    (finiteShellRegion_measurable a R) (finiteShellRegion_monotone a R) hcover hI
    ((B * δ / R) / (1 - b / 2)) hbound
  refine ⟨(integrable_indicator_iff (closedExterior_measurable a R)).mp hgI, ?_⟩
  simpa only [g, integral_indicator (closedExterior_measurable a R)] using! hgB

theorem infinite_weighted_height_tail_shifted {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (w : Ambient d → ℝ) (hwm : Measurable w)
    (hw : ∀ k, MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hsecond : ∀ k, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) (ℓ : ℕ) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a (R * 2 ^ ℓ)) μ ∧
      (∫ y in closedExterior a (R * 2 ^ ℓ), |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        ((B * δ / R) / (1 - b / 2)) * (b / 2) ^ ℓ := by
  have hw' : ∀ k, MemLp w 2 (μ.restrict (dyadicAnnulus a (R * 2 ^ ℓ) k)) := by
    intro k
    rw [dyadicAnnulus_shift]
    exact hw (ℓ + k)
  have hs' : ∀ k, (∫ y in dyadicAnnulus a (R * 2 ^ ℓ) k, w y ^ 2 ∂μ) ≤
      (B * ((R * 2 ^ ℓ) * 2 ^ k) ^ m) * ((δ * b ^ ℓ) * ((R * 2 ^ ℓ) * 2 ^ k) * b ^ k) ^ 2 := by
    intro k
    rw [dyadicAnnulus_shift]
    convert! hsecond (ℓ + k) using 1
    simp only [pow_add, mul_pow]
    ring
  obtain ⟨hi, hb⟩ := infinite_shell_weighted_height_bound m C B μ hg hCB a (R * 2 ^ ℓ)
    (by positivity) w hwm hw' (δ * b ^ ℓ) b (by positivity) hb0 hb2 hs'
  refine ⟨hi, hb.trans_eq ?_⟩
  have hden : 0 < 1 - b / 2 := by linarith
  rw [div_pow]
  field_simp

end

end RieszRectifiability

end OAI
