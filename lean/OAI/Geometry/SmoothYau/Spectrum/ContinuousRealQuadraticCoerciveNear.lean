import Mathlib
import OAI.Geometry.SmoothYau.Estimates.PhaseFormMatrix

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples
section LocalContinuationAt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma continuousAt_real_quadratic_coercive_near {T : Type*} [TopologicalSpace T]
    (A : T → Matrix ι ι ℝ) (t : T) (hA : ContinuousAt A t)
    (μ : ℝ) (hμ : 0 < μ)
    (hb : ∀ v, μ * squareSum v ≤ realQuadratic (A t) v) :
    ∀ᶠ s in 𝓝 t, ∀ v, (μ / 2) * squareSum v ≤ realQuadratic (A s) v := by
  let variation : T → ℝ := fun s => ∑ i, ∑ j, |A t i j - A s i j|
  have hc : ContinuousAt variation t := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (continuousAt_const.sub ((continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp hA))).abs
  have hzero : variation t = 0 := by simp [variation]
  have he : ∀ᶠ s in 𝓝 t, variation s < μ / 2 :=
    hc.tendsto.eventually_lt_const (by rw [hzero]; positivity)
  filter_upwards [he] with s hs v
  have hab := realQuadratic_abs_bound ((fun i j => A t i j) - (fun i j => A s i j)) v
  rw [realQuadratic_sub] at hab
  change |realQuadratic (A t) v - realQuadratic (A s) v| ≤
    variation s * squareSum v at hab
  have hh := (le_abs_self (realQuadratic (A t) v - realQuadratic (A s) v)).trans hab
  have hv := mul_le_mul_of_nonneg_right hs.le (squareSum_nonneg v)
  linarith [hb v]

theorem phase_matrix_continuation_at {T : Type*} [TopologicalSpace T]
    (H : T → Matrix ι ι ℝ) (z : T → ι → ℂ) (t : T)
    (hH : ContinuousAt H t) (hz : ContinuousAt z t)
    (Q : Matrix ι ι ℂ) (hQ : Qᵀ = Q) (hQz : Q *ᵥ z t = 0)
    (hgap : ∀ v : ι → ℝ, v ≠ 0 →
      0 < realQuadratic (H t - Q.map Complex.re) v) :
    ∃ κ > 0, ∃ C > 0, ∀ᶠ s in 𝓝 t,
      (continuedPhaseMatrix Q (z s))ᵀ = continuedPhaseMatrix Q (z s) ∧
      (z s ⬝ᵥ z s = -1 → continuedPhaseMatrix Q (z s) *ᵥ z s = 0) ∧
      ‖continuedPhaseMatrix Q (z s)‖ ≤ C ∧
      ∀ v, 4 * κ * squareSum v ≤
        realQuadratic (H s - (continuedPhaseMatrix Q (z s)).map Complex.re) v := by
  let A : T → Matrix ι ι ℝ := fun s =>
    H s - (continuedPhaseMatrix Q (z s)).map Complex.re
  have hA : ContinuousAt A t := by
    apply hH.sub
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact Complex.continuous_re.continuousAt.comp
      ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp
        ((continuous_continuedPhaseMatrix Q).continuousAt.comp hz)))
  have hAt : A t = H t - Q.map Complex.re := by
    dsimp only [A]
    rw [continuedPhaseMatrix_eq Q hQ _ hQz]
  obtain ⟨μ, hμ, hb⟩ := strict_real_quadratic_coercive _ hgap
  have hlower := continuousAt_real_quadratic_coercive_near A t hA μ hμ (by
    rw [hAt]; exact hb)
  have hcont := ((continuous_continuedPhaseMatrix Q).continuousAt.comp hz).norm
  have hbound : ∀ᶠ s in 𝓝 t, ‖continuedPhaseMatrix Q (z s)‖ < ‖Q‖ + 1 :=
    hcont.tendsto.eventually_lt_const (by
      dsimp only [Function.comp_def]
      rw [continuedPhaseMatrix_eq Q hQ _ hQz]; linarith)
  refine ⟨μ / 8, by positivity, ‖Q‖ + 1, by positivity, ?_⟩
  filter_upwards [hlower, hbound] with s hs hB
  refine ⟨continuedPhaseMatrix_transpose Q hQ _,
    continuedPhaseMatrix_annihilates Q _, hB.le, ?_⟩
  intro v
  convert hs v using 1
  ring
end LocalContinuationAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def transverseProjection (ν b : E) : E := b - inner ℝ ν b • ν

def normalizedTransverse (a ν b : E) : E :=
  (Real.sqrt (1 + ‖a‖^2) / ‖transverseProjection ν b‖) • transverseProjection ν b

lemma transverseProjection_eq {ν b : E} (hb : inner ℝ ν b = 0) :
    transverseProjection ν b = b := by simp [transverseProjection, hb]

lemma transverseProjection_orthogonal {ν : E} (hν : ‖ν‖ = 1) (b : E) :
    inner ℝ ν (transverseProjection ν b) = 0 := by
  have hn : inner ℝ ν ν = 1 := by rw [real_inner_self_eq_norm_sq, hν]; norm_num
  simp [transverseProjection, inner_sub_right, inner_smul_right, hν]

@[fun_prop] lemma continuous_transverseProjection :
    Continuous (fun p : E × E => transverseProjection p.1 p.2) := by
  unfold transverseProjection
  fun_prop

lemma normalizedTransverse_eq {a ν b : E} (hb : inner ℝ ν b = 0)
    (hn : ‖b‖^2 = 1 + ‖a‖^2) : normalizedTransverse a ν b = b := by
  have hbn : 0 < ‖b‖ := by nlinarith [norm_nonneg b, sq_nonneg ‖a‖]
  rw [normalizedTransverse, transverseProjection_eq hb, ← hn, Real.sqrt_sq_eq_abs,
    abs_of_pos hbn, div_self hbn.ne', one_smul]

lemma normalizedTransverse_orthogonal {ν : E} (hν : ‖ν‖ = 1) (a b : E) :
    inner ℝ ν (normalizedTransverse a ν b) = 0 := by
  simp [normalizedTransverse, inner_smul_right, transverseProjection_orthogonal hν]

lemma normalizedTransverse_norm_sq (a ν b : E) (hb : transverseProjection ν b ≠ 0) :
    ‖normalizedTransverse a ν b‖^2 = 1 + ‖a‖^2 := by
  have hn := norm_pos_iff.mpr hb
  rw [normalizedTransverse, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)),
    div_mul_cancel₀ _ hn.ne', Real.sq_sqrt (by positivity)]

lemma continuousAt_normalizedTransverse {T : Type*} [TopologicalSpace T]
    (a ν : T → E) (b : E) (t : T) (ha : ContinuousAt a t) (hν : ContinuousAt ν t)
    (hb : transverseProjection (ν t) b ≠ 0) :
    ContinuousAt (fun s => normalizedTransverse (a s) (ν s) b) t := by
  have hp : ContinuousAt (fun s => transverseProjection (ν s) b) t :=
    continuous_transverseProjection.continuousAt.comp (hν.prodMk continuousAt_const)
  exact ((continuousAt_const.add (ha.norm.pow 2)).sqrt.div hp.norm
    (norm_ne_zero_iff.mpr hb)).smul hp
end YauCounterexamples

end

end OAI
