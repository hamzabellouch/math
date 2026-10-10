import OAI.Geometry.RCD.Heat.HeatPowerTailDomination

namespace OAI

/-! # Compactly supported exponential tilts of Sobolev densities -/

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

 theorem bounded_exp_lipschitz {g : X → ℝ} {C : ℝ≥0} (hg : LipschitzWith C g)
    {M : ℝ} (hM : ∀ x, g x ≤ M) :
    LipschitzWith (⟨Real.exp M,(Real.exp_pos _).le⟩*C) (fun x => Real.exp (g x)) := by
  have he : LipschitzOnWith ⟨Real.exp M,(Real.exp_pos _).le⟩ Real.exp (Iic M) := by
    apply (convex_Iic M).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    intro x hx
    change |Real.exp x| ≤ Real.exp M
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hx
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (he.dist_le_mul (g x) (hM x) (g y) (hM y)).trans
    (by
      change Real.exp M*dist (g x) (g y) ≤ (Real.exp M*(C:ℝ))*dist x y
      simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hg.dist_le_mul x y) (Real.exp_pos M).le)

 theorem compact_exp_sub_one {g : X → ℝ} (hg : HasCompactSupport g) (t : ℝ) :
    HasCompactSupport (fun x => Real.exp (t*g x)-1) := by
  apply HasCompactSupport.of_support_subset_isCompact hg
  intro x hx
  by_contra hno
  have hzero : g x=0 := image_eq_zero_of_notMem_tsupport hno
  exact hx (by simp only [hzero,mul_zero,Real.exp_zero,sub_self])

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.exists_exp_mul (ρ : SobolevSpace μ hQ)
    {g : X → ℝ} {C M : ℝ≥0} (hg : LipschitzWith C g) (hgs : HasCompactSupport g)
    (hgb : ∀ x, |g x| ≤ M) (t : ℝ) :
    ∃ σ : SobolevSpace μ hQ,
      SobolevSpace.toLp μ hQ σ =ᵐ[μ] fun x => Real.exp (t*g x)*SobolevSpace.toLp μ hQ ρ x := by
  let B : ℝ≥0 := ⟨Real.exp (|t| *M),(Real.exp_pos _).le⟩
  have hb (x : X) : |Real.exp (t*g x)| ≤ B := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by rw [abs_mul]; gcongr; exact hgb x))
  have hl := bounded_exp_lipschitz (M := |t| *(M:ℝ)) (lipschitzWith_const_mul_real hg t)
    (fun x => (le_abs_self (t*g x)).trans (by rw [abs_mul]; gcongr; exact hgb x))
  let V := boundedMultiplier μ (fun x => Real.exp (t*g x)) hl.continuous.measurable B hb
  have hV := boundedMultiplier_coe μ (fun x => Real.exp (t*g x)) hl.continuous.measurable B hb
  let σ := ρ.mulLipschitz μ hQ hl 1 (compact_exp_sub_one hgs t) hb
    (fun x => (Real.exp_pos _).le) V hV
  refine ⟨σ,?_⟩
  filter_upwards [lpMultiplier_coe μ V (SobolevSpace.toLp μ hQ ρ),hV] with x hx hv
  exact hx.trans (by rw [hv])

end RegularPointCoordinates

end

end OAI
