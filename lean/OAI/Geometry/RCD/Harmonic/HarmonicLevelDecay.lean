import OAI.Geometry.RCD.Harmonic.HarmonicLevelStep
import OAI.Geometry.RCD.Coordinates.NormalizedLevelAlgebra

namespace OAI

/-! # Vanishing harmonic upper-level energies on shrinking balls -/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Small normalized L² mass forces geometric decay of the upper-level
energies, with constants independent of the ball. -/
theorem NoncollapsedRCD.harmonic_level_energies_tendsto_zero {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ u : SobolevSpace (hausdorff n X) hX.quadratic,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball x R) u →
      (∫ y in ball x R, (SobolevSpace.toLp (hausdorff n X) hX.quadratic u y)^2
        ∂hausdorff n X) ≤ δ*(hausdorff n X).real (ball x R) →
      Tendsto (fun i : ℕ => ∫ y in closedBall x (R/2+R/(4*2^i)),
        (max (SobolevSpace.toLp (hausdorff n X) hX.quadratic u y-(1-(2^i:ℝ)⁻¹)) 0)^2
          ∂hausdorff n X) atTop (𝓝 0) := by
  obtain ⟨p,C,hp,hC,hstep⟩ := hX.harmonic_level_step hn
  have hp0 : 0 < p := by linarith
  let α := 1-2/p
  have hα : 0 < α := by
    have hh : 2/p < 1 := (div_lt_one hp0).mpr hp
    dsimp only [α]
    linarith
  let C₀ := C*641*(4:ℝ)^α
  let b := (4:ℝ)^(1+α)
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  obtain ⟨δ,hδ,hdecay⟩ := exists_superlinear_decay_threshold hC₀ hb hα
  refine ⟨δ,hδ,?_⟩
  intro x R hR hcurv u hu hsmall
  let μ := hausdorff n X
  let V := μ.real (ball x R)
  let U := SobolevSpace.toLp μ hX.quadratic u
  let J (i : ℕ) := ∫ y in closedBall x (R/2+R/(4*2^i)),
    (max (U y-(1-(2^i:ℝ)⁻¹)) 0)^2 ∂μ
  let Y (i : ℕ) := J i/V
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport x R hR).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hJ (i : ℕ) : 0 ≤ J i := integral_nonneg fun _ => sq_nonneg _
  have hY (i : ℕ) : 0 ≤ Y i := div_nonneg (hJ i) hV.le
  have hstart : Y 0 ≤ δ := by
    have hJ0 : J 0 ≤ ∫ y in ball x R, (U y)^2 ∂μ := by
      have hsub : closedBall x (R/2+R/(4*2^0)) ⊆ ball x R :=
        closedBall_subset_ball (dyadic_inner_radii hR 0).2.2
      have hfirst : J 0 ≤ ∫ y in closedBall x (R/2+R/(4*2^0)), (U y)^2 ∂μ := by
        dsimp only [J]
        simp only [pow_zero,inv_one,sub_self,sub_zero]
        have hi0 : Integrable (fun y => (max (U y) 0)^2) μ := by
          simpa only [Function.comp_apply,upperLevelPart,sub_zero] using
            ((upperLevelPart_lipschitz 0).comp_memLp (upperLevelPart_zero (by norm_num))
              (Lp.memLp U)).integrable_sq
        apply integral_mono_ae hi0.integrableOn (Lp.memLp U).integrable_sq.integrableOn
        exact Eventually.of_forall fun y => by
          change (max (U y) 0)^2 ≤ (U y)^2
          by_cases hh : 0 ≤ U y
          · rw [max_eq_left hh]
          · rw [max_eq_right (le_of_not_ge hh),zero_pow (by decide)]
            exact sq_nonneg _
      exact hfirst.trans (setIntegral_mono_set (Lp.memLp U).integrable_sq.integrableOn
        (Eventually.of_forall fun y => sq_nonneg _) (Eventually.of_forall hsub))
    exact (div_le_iff₀ hV).mpr (hJ0.trans hsmall)
  have hrec (i : ℕ) : Y (i+1) ≤ C₀*b^i*(Y i)^(1+α) := by
    have hr := dyadic_inner_radii hR i
    have hk := dyadic_level_gap_bounds hR i
    have hh := hstep x R hR hcurv u hu
      (R/2+R/(4*2^(i+1))) (R/2+R/(4*2^i))
      (1-(2^i:ℝ)⁻¹) (1-(2^(i+1):ℝ)⁻¹) hr.1 hr.2.1 hr.2.2 hk.1 hk.2.1
    change J (i+1) ≤ C*V^(2/p-1)*
      (10*R^2*(((R/2+R/(4*2^i))-(R/2+R/(4*2^(i+1))))⁻¹)^2+1)*
      J i*(J i/((1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹))^2)^(1-2/p) at hh
    have hgap : J i/((1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹))^2 = (4*4^i)*J i := by
      rw [div_eq_mul_inv,← inv_pow,hk.2.2.1]
      ring
    have hexp : 2/p-1 = -α := by dsimp only [α]; ring
    rw [hgap,hexp] at hh
    have hbnd : J (i+1) ≤ C*V^(-α)*(641*4^i)*J i*((4*4^i)*J i)^α := by
      apply hh.trans
      gcongr
      exact hk.2.2.2
    have hnorm := div_le_div_of_nonneg_right hbnd hV.le
    rw [normalized_level_identity hV (hJ i) (by norm_num : (0:ℝ)<4)
      (by norm_num : (0:ℝ)<4) hα i] at hnorm
    exact hnorm
  have hlim := hdecay Y hY hstart hrec
  have hJlim := hlim.mul_const V
  have heq (i : ℕ) : Y i*V = J i := div_mul_cancel₀ _ hV.ne'
  simpa only [heq,zero_mul] using hJlim

end RegularPointCoordinates

end

end OAI
