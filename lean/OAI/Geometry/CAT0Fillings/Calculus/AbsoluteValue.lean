import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Minimizers.CriticalEnergy
import OAI.Geometry.CAT0Fillings.Calculus.ClosedLevel

namespace OAI

section

open Set Filter
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

noncomputable def absApprox (ε t : ℝ) : ℝ := Real.sqrt (t^2+ε^2)
noncomputable def absApproxDeriv (ε t : ℝ) : ℝ := t / Real.sqrt (t^2+ε^2)

lemma absApprox_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (absApprox ε) (absApproxDeriv ε t) t := by
  have hh : 0 < t^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  have hd := (((hasDerivAt_id t).pow 2).add_const (ε^2)).sqrt hh.ne'
  convert hd using 1
  · rfl
  · dsimp [absApproxDeriv]
    norm_num
    ring

lemma absApproxDeriv_bound {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |absApproxDeriv ε t| ≤ 1 := by
  have hh : 0 < t^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  dsimp [absApproxDeriv]
  rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_one (Real.sqrt_pos.mpr hh)).mpr
  rw [←Real.sqrt_sq_eq_abs t]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

lemma absApprox_lipschitz {ε : ℝ} (hε : 0 < ε) : LipschitzWith 1 (absApprox ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (absApprox_hasDerivAt hε t).differentiableAt)
  intro t
  rw [←NNReal.coe_le_coe,coe_nnnorm,NNReal.coe_one,(absApprox_hasDerivAt hε t).deriv,Real.norm_eq_abs]
  exact absApproxDeriv_bound hε t

lemma continuous_absApproxDeriv {ε : ℝ} (hε : 0 < ε) : Continuous (absApproxDeriv ε) := by
  change Continuous (fun t : ℝ => t / Real.sqrt (t^2+ε^2))
  apply continuous_id.div (Real.continuous_sqrt.comp (continuous_id.pow 2 |>.add continuous_const))
  intro t
  exact (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε))).ne'

lemma absApprox_error {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : abs (absApprox ε t-|t|) ≤ ε := by
  have hl : |t| ≤ absApprox ε t := by
    rw [←Real.sqrt_sq_eq_abs t]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  have hu : absApprox ε t ≤ |t|+ε := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [add_sq,sq_abs]
    nlinarith [abs_nonneg t]
  linarith

lemma absApproxDeriv_tendsto {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hepos : ∀ j, 0 < e j) (t : ℝ) :
    Tendsto (fun j => absApproxDeriv (e j) t) atTop (𝓝 (t / |t|)) := by
  by_cases ht : t = 0
  · subst t
    rw [zero_div]
    apply tendsto_const_nhds.congr
    intro index
    dsimp [absApproxDeriv]
    rw [zero_pow (by decide : 2 ≠ 0),zero_add,Real.sqrt_sq (hepos index).le,zero_div]
  have hab : 0 < |t| := abs_pos.mpr ht
  have hh := (tendsto_const_nhds (x := t) (f := (atTop : Filter ℕ))).div ((tendsto_const_nhds.add (he.pow 2)).sqrt)
    (show Real.sqrt (t^2+(0:ℝ)^2) ≠ 0 by simpa only [zero_pow (by decide : 2 ≠ 0),add_zero,Real.sqrt_sq_eq_abs] using hab.ne')
  simp only [zero_pow (by decide : 2 ≠ 0),add_zero,Real.sqrt_sq_eq_abs] at hh
  exact hh

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus AnalyticMinimizer

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_abs (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => |(q.inclusion P) x|) ∧
      ‖q.inclusion Q‖ = ‖q.inclusion P‖ ∧
      ‖q.closedGradient Q‖ ≤ ‖q.closedGradient P‖ := by
  let e (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have hepos (j : ℕ) : 0 < e j := by dsimp [e]; positivity
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb (t : ℝ) : abs (t/|t|) ≤ 1 := by
    rw [abs_div,abs_abs]
    by_cases ht : t = 0
    · simp [ht]
    · rw [div_self (abs_pos.mpr ht).ne']
  obtain ⟨Q,hQ,hG⟩ := q.closed_chain_uniform (F := abs) (D := fun t => t/|t|)
    (show LipschitzWith 1 abs from LipschitzWith.of_dist_le_mul (fun x y => by simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y)) (measurable_id.div measurable_id.abs) (by norm_num : (0:ℝ) ≤ 1) hb
    (fun j => absApprox (e j)) (fun j => absApproxDeriv (e j)) (fun _ => 1)
    (fun j => absApprox_lipschitz (hepos j)) (fun j => absApprox_hasDerivAt (hepos j))
    (fun j => continuous_absApproxDeriv (hepos j)) (fun j => absApproxDeriv_bound (hepos j))
    (absApproxDeriv_tendsto he hepos) e he (fun j => absApprox_error (hepos j).le) P
  refine ⟨Q,hQ,?_,?_⟩
  · apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
    · filter_upwards [hQ] with x hx
      simp only [hx,Real.norm_eq_abs,abs_abs,le_refl]
    · filter_upwards [hQ] with x hx
      simp only [hx,Real.norm_eq_abs,abs_abs,le_refl]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hG] with w hw
    rw [hw,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)).trans_eq (one_mul _)

lemma nonnegative_minimizer {p A B : ℝ} (hA : 0 ≤ A) (u : q.Sobolev)
    (hu : criticalNorm q.inclusion p u = 1)
    (hmin : ∀ w, energy q.inclusion q.closedGradient A B u * (criticalNorm q.inclusion p w)^2 ≤
      energy q.inclusion q.closedGradient A B w) :
    ∃ v : q.Sobolev,
      (∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ (q.inclusion v) x) ∧
      criticalNorm q.inclusion p v = 1 ∧
      energy q.inclusion q.closedGradient A B v = energy q.inclusion q.closedGradient A B u ∧
      ∀ w, energy q.inclusion q.closedGradient A B v * (criticalNorm q.inclusion p w)^2 ≤
        energy q.inclusion q.closedGradient A B w := by
  obtain ⟨v,hv,hv2,hvg⟩ := q.closed_abs u
  have hvp : criticalNorm q.inclusion p v = 1 := by
    rw [criticalNorm,lpNorm_congr_ae hv _,lpNorm_fun_abs (Lp.aestronglyMeasurable _)]
    exact hu
  have hle : energy q.inclusion q.closedGradient A B v ≤ energy q.inclusion q.closedGradient A B u := by
    dsimp [energy]
    rw [hv2]
    exact add_le_add (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hvg) hA) le_rfl
  have hge := hmin v
  rw [hvp,one_pow,mul_one] at hge
  have heq := le_antisymm hle hge
  refine ⟨v,?_,hvp,heq,?_⟩
  · filter_upwards [hv] with x hx
    rw [hx]
    exact abs_nonneg _
  · simpa only [heq] using hmin

end CAT0Fillings.ChartGeometry
end

end OAI
