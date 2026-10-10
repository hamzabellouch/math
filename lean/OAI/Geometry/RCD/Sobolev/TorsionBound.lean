import OAI.Geometry.RCD.Sobolev.TorsionSuperlevel
import OAI.Geometry.RCD.Sobolev.StampacchiaBound

namespace OAI

/-!
# Uniform height of the Dirichlet torsion solution

The constant is chosen before the domain and the solution. Only the
Dirichlet Sobolev constant, its exponent, and an upper volume bound enter.
-/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A uniform torsion bound from the displayed Dirichlet Sobolev inequality. -/
theorem exists_uniform_torsion_bound {d C V : ℝ} (hd : 1 < d)
    (hC : 0 ≤ C) (hV : 0 ≤ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ω : Set X), μ Ω ≠ ∞ → μ.real Ω ≤ V →
      ∀ u : SobolevSpace.dirichlet μ hQ Ω,
      (∀ φ : SobolevSpace.dirichlet μ hQ Ω,
        energyForm μ hQ u.val φ.val = ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ) →
      (∀ φ : SobolevSpace.dirichlet μ hQ Ω,
        (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
          C * energyForm μ hQ φ.val φ.val) →
      ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.toLp μ hQ u.val x ≤ K := by
  obtain ⟨K, hK, hExt⟩ := exists_extinction_level (R := C ^ (2 * d)) (M := V + 1)
    (p := 2 * d) (Real.rpow_nonneg hC _) (by linarith) (by linarith)
  refine ⟨K, hK, ?_⟩
  intro Ω hΩfin hvol u hsolve hsob
  let ν := μ.restrict Ω
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hΩfin.lt_top⟩
  let U := fun x => SobolevSpace.toLp μ hQ u.val x
  let Y := fun t : ℝ => ν.real {x | t < U x}
  have hY (t : ℝ) : 0 ≤ Y t := measureReal_nonneg
  have hY0 : Y 0 ≤ V + 1 := by
    have hm : Y 0 ≤ ν.real univ := measureReal_mono (subset_univ _) (measure_ne_top _ _)
    have hv : ν.real univ = μ.real Ω := by simp only [ν, measureReal_restrict_apply_univ]
    rw [hv] at hm
    linarith
  have hmono (k l : ℝ) (_hk : 0 ≤ k) (hkl : k ≤ l) : Y l ≤ Y k := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro x hx
    exact hkl.trans_lt hx
  have hstep (k l : ℝ) (hk : 0 ≤ k) (hkl : k < l) :
      Y l ≤ C ^ (2 * d) * Y k ^ (2 * d - 1) / (l - k) ^ (2 * d) := by
    have hm : Y l ≤ ν.real {x | l ≤ U x} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro x hx
      exact (show l < U x from hx).le
    exact hm.trans (torsion_superlevel_le μ hQ Ω hΩfin u hsolve hd hC hsob hk hkl)
  have hz : Y K = 0 := hExt Y (fun t _ => hY t) hY0 hmono hstep
  have hz' : ν {x | K < U x} = 0 := by
    have hfin := measure_ne_top ν {x | K < U x}
    exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right hfin
  apply ae_iff.mpr
  simpa only [not_le] using hz'

end RegularPointCoordinates

end

end OAI
