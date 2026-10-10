import OAI.Probability.SLE.Angle.AngleEigenSource
import OAI.Probability.SLE.FiniteStoppedLaw

namespace OAI

/-! Exact exponential eigenfunction moments under the finite centered law,
using angular localization and dominated convergence. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Polynomial
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}
  (hB : IsBrownianReal B P) (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
  (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω=0)
  {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
  (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))

include hB hBm hBc hB0 hκ hκ8 γ G F hw

lemma stoppedGreen_eigen_moment (z : ℂ) (hz : z∈upperHalfPlane)
    (u : ℝ) (hu : 0≤u) (n : ℕ) :
    (∫ ω, stoppedGreen κ (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) z u*
      (angleEigenPolynomial κ n).eval (Real.cos ((G ω (radiusLevelTime (γ ω) (G ω) z u).toNNReal z-
        (Real.sqrt κ*B (radiusLevelTime (γ ω) (G ω) z u).toNNReal ω:ℝ)).arg)) ∂P)=
    initialGreen κ z*Real.exp (-u*anglePolynomialEigenvalue κ n)*
      (angleEigenPolynomial κ n).eval (Real.cos z.arg) := by
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let A := logAngleSq κ (initialLogCoordinates z) 0
  have hA : 0<A := logAngleSq_pos _ _ _
  let ε (j : ℕ) := A/((j:ℝ)+1)
  have hε (j : ℕ) : 0<ε j := by dsimp [ε]; positivity
  have hεA (j : ℕ) : ε j≤A :=
    div_le_self hA.le (by have hj := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A
  let a (j : ℕ) : AngularLocalization B hm κ z u (ε j) :=
    (exists_angularLocalization hB hm hBm hBc hB0 κ hκ hκ8 z u (ε j) hu (hε j) (hεA j)).some
  let ev := anglePolynomialEigenvalue κ n
  let f (j : ℕ) (ω : Ω) := logPolynomialDensity κ (codimension κ+ev)
    (greenExponent κ) (angleEigenPolynomial κ n) ((a j).solution.Q ((a j).τ ω) ω) (B ((a j).τ ω) ω)
  let w (ω : Ω) := stoppedGreen κ (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) z u*
    (angleEigenPolynomial κ n).eval (Real.cos ((G ω (radiusLevelTime (γ ω) (G ω) z u).toNNReal z-
      (Real.sqrt κ*B (radiusLevelTime (γ ω) (G ω) z u).toNNReal ω:ℝ)).arg))
  let K := Real.exp (ev*(u-Real.log 2-Real.log z.im))
  let C := Real.exp ((codimension κ+ev)*(u-Real.log 2-Real.log z.im))*((n:ℝ)+1)^(n+1)
  have hf (j : ℕ) : Integrable (f j) P ∧
      (∫ ω, f j ω ∂P)=Real.exp (-ev*(Real.log 2+Real.log z.im))*initialGreen κ z*
        (angleEigenPolynomial κ n).eval (Real.cos z.arg) := by
    exact ⟨((a j).mean_eigen hB hBm hBc hB0 hκ hκ8 n).1,
      ((a j).mean_eigen hB hBm hBc hB0 hκ hκ8 n).2.trans
        (logPolynomialDensity_initial κ ev _ z hz)⟩
  have hb (j : ℕ) : ∀ᵐ ω ∂P, ‖f j ω‖≤C := Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using
      logEigenDensity_bound hκ hκ8 n (Real.log z.im) u _ _ ((a j).inside ω ((a j).τ ω) le_rfl).1
  have hl : ∀ᵐ ω ∂P, Tendsto (fun j => f j ω) atTop (𝓝 (K*w ω)) := by
    filter_upwards [hw] with ω hω
    simpa only [f,w,K,ev,mul_assoc] using
      localization_eigen_tendsto a hεlim hBc hκ hκ8 hz ω (γ ω) (G ω) (F ω) hω n
  have hi := tendsto_integral_of_dominated_convergence (fun _ : Ω => C)
    (fun j => (hf j).1.aestronglyMeasurable) (integrable_const C) hb hl
  have he : (∫ ω, K*w ω ∂P)=Real.exp (-ev*(Real.log 2+Real.log z.im))*initialGreen κ z*
      (angleEigenPolynomial κ n).eval (Real.cos z.arg) := by
    apply tendsto_nhds_unique hi
    exact tendsto_const_nhds.congr' (Eventually.of_forall fun j => (hf j).2.symm)
  rw [integral_const_mul] at he
  change (∫ ω, w ω ∂P)=_
  apply (mul_left_cancel₀ (Real.exp_ne_zero (ev*(u-Real.log 2-Real.log z.im))))
  change K*(∫ ω, w ω ∂P)=_
  rw [he]
  have hexp : K*Real.exp (-u*ev)=Real.exp (-ev*(Real.log 2+Real.log z.im)) := by
    dsimp only [K]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

lemma finiteCenteredLaw_eigen_moment (z : ℂ) (hz : z∈upperHalfPlane)
    (u : ℝ) (hu : 0≤u) (n : ℕ) :
    (∫ ω, (angleEigenPolynomial κ n).eval (Real.cos
      ((G ω (radiusLevelTime (γ ω) (G ω) z u).toNNReal z-
        (Real.sqrt κ*B (radiusLevelTime (γ ω) (G ω) z u).toNNReal ω:ℝ)).arg))
      ∂finiteCenteredLaw P κ B γ G z u)=
    Real.exp (-u*anglePolynomialEigenvalue κ n)*(angleEigenPolynomial κ n).eval (Real.cos z.arg) := by
  obtain ⟨hgi,_⟩ := finite_stopped_green_of_witness hB κ hκ hκ8 γ G F hw z hz u hu
  have hnon : ∀ᵐ ω ∂P, 0≤ stoppedGreen κ (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) z u/
      initialGreen κ z := by
    filter_upwards [hw] with ω hω
    exact div_nonneg (stoppedGreen_nonneg hω κ z u) (initialGreen_pos κ z hz).le
  rw [finiteCenteredLaw,integral_withDensity_eq_integral_toReal_smul₀
    (hgi.div_const _).aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have he : (fun ω => (ENNReal.ofReal
      (stoppedGreen κ (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) z u/initialGreen κ z)).toReal •
      (angleEigenPolynomial κ n).eval (Real.cos ((G ω (radiusLevelTime (γ ω) (G ω) z u).toNNReal z-
        (Real.sqrt κ*B (radiusLevelTime (γ ω) (G ω) z u).toNNReal ω:ℝ)).arg))) =ᵐ[P]
    fun ω => (stoppedGreen κ (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) z u*
      (angleEigenPolynomial κ n).eval (Real.cos ((G ω (radiusLevelTime (γ ω) (G ω) z u).toNNReal z-
        (Real.sqrt κ*B (radiusLevelTime (γ ω) (G ω) z u).toNNReal ω:ℝ)).arg)))/initialGreen κ z := by
    filter_upwards [hnon] with ω hω
    rw [ENNReal.toReal_ofReal hω,smul_eq_mul]
    ring
  rw [integral_congr_ae he,integral_div,
    stoppedGreen_eigen_moment hB hBm hBc hB0 hκ hκ8 γ G F hw z hz u hu n]
  field_simp [(initialGreen_pos κ z hz).ne']

end SLEExactGauge

end

end OAI
