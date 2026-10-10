import OAI.NumberTheory.JointDickman.Analysis.MellinDyadicLowFrequency

namespace OAI

/-! # Marginal means control both integer dyadic blocks uniformly -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

theorem centered_weighted_bin_dyadic_low {J : ℕ} (hJ : 0<J)
    (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1) (μ : ℂ) (hμ : ‖μ‖≤1)
    (hmean : ∀ D : ℝ, 0<D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (E : Finset ℕ) (hE : ∀ p∈E, p.Prime) (w : ℕ → ℝ)
    (hw : ∀ p∈E, 0≤w p ∧ w p≤1)
    {a b U ε : ℝ} (ha : 0<a) (hb : 0<b) (hU : 0<U) (hε : 0<ε) :
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ, a*x≤N → (N:ℝ)≤b*x →
      (∫ t in -U..U, ‖angularMellinPolynomial (Ioc N (2*N))
        (centeredWeightedBinCoefficient J ζ μ E w x) t‖^2) ≤ ε := by
  let δ := Real.sqrt (ε/(2*U))
  have hδ : 0<δ := Real.sqrt_pos.mpr (by positivity)
  have hpref : ∀ D : ℝ, 0<D → Tendsto
      (fun x : ℝ => (∑ n ∈ Ioc 0 ⌊D*x⌋₊,
        centeredWeightedBinCoefficient J ζ μ E w x n)/(x:ℂ)) atTop (𝓝 0) := by
    intro D hD
    have hh := (weightedCenteredBinPrefix_tendsto hJ ζ μ hmean hE w hD).const_mul (D:ℂ)
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    dsimp only [weightedCenteredBinPrefix,centeredWeightedBinCoefficient,ArithmeticFunction.coe_mk]
    have hDc : (D:ℂ)≠0 := by exact_mod_cast hD.ne'
    have hxc : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
    field_simp
  have hlo := angularMellin_uniform_dyadic_low
    (fun x n => centeredWeightedBinCoefficient J ζ μ E w x n) (by norm_num : (0:ℝ)≤2)
    (centeredWeightedBinCoefficient_norm ζ hζ hμ w hw)
    (fun x => (centeredWeightedBinCoefficient J ζ μ E w x).map_zero)
    hpref ha hb hU.le hδ
  filter_upwards [hlo] with x hx
  intro N hN hN'
  have hh := angularMellin_bounded_energy_le (Ioc N (2*N))
    (centeredWeightedBinCoefficient J ζ μ E w x) hU.le hδ.le (hx N hN hN')
  apply hh.trans_eq
  dsimp [δ]
  rw [Real.sq_sqrt (by positivity)]
  field_simp

end JointDickman

end OAI
