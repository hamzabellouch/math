import Mathlib
import OAI.Probability.SKSupport.Backward.Backward
import OAI.Probability.SKSupport.Foundations.SoftAbs

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def cascade (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, x => f x
  | n+1, k, x => logSemigroup (c k) h (cascade c h f n (k+1)) x

lemma cascade_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (n k : ℕ) : LipschitzWith K (cascade c h f n k) := by
  induction n generalizing k with
  | zero => exact hf
  | succ n IH => exact logSemigroup_lipschitz (IH (k+1)) (c k).coe_nonneg h

lemma cascade_regular {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (n k : ℕ) : RegularDatum (cascade c h f n k) := by
  induction n generalizing k with
  | zero => exact hf
  | succ n IH =>
    exact regularDatum_logSemigroup (IH (k+1)) (cascade_lipschitz hLip c h n (k+1)) (c k).coe_nonneg h

lemma cascade_terminal_stability {f g : ℝ → ℝ} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith J g) {δ : ℝ}
    (hδ : ∀ z, |f z-g z| ≤ δ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (n k : ℕ) (x : ℝ) :
    |cascade c h f n k x-cascade c h g n k x| ≤ δ := by
  induction n generalizing k x with
  | zero => exact hδ x
  | succ n IH =>
    exact logSemigroup_terminal_stability (cascade_lipschitz hf c h n (k+1))
      (cascade_lipschitz hg c h n (k+1)) (c k).coe_nonneg (IH (k+1)) h x

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

def cascadeAt (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N k : ℕ) : ℝ → ℝ :=
  cascade c h f (N-k) k

def cellHeat (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N k : ℕ) : ℝ → ℝ → ℝ :=
  backward (c k) ((min (k+1) N:ℕ)*h) (cascadeAt c h f N (k+1))

def cellRate (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N k : ℕ) : ℝ → ℝ → ℝ :=
  backwardRate (c k) ((min (k+1) N:ℕ)*h) (cascadeAt c h f N (k+1))

lemma cellHeat_verificationData {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N k : ℕ) :
    VerificationData (cellHeat c h f N k) (cellRate c h f N k)
      (c k) ((min (k+1) N:ℕ)*h) :=
  backward_verificationData (cascade_regular hf hLip c h _ _)
    (cascade_lipschitz hLip c h _ _) (c k).coe_nonneg _

lemma cellHeat_left {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N k : ℕ) (hk : k ≤ N) :
    cellHeat c h f N k ((k:ℝ)*(h:ℝ)) = cascadeAt c h f N k := by
  by_cases he : k = N
  · subst k
    funext x
    simpa [cellHeat, cascadeAt, cascade, Nat.min_eq_right (Nat.le_succ N)] using
      backward_terminal (c N) ((N:ℝ)*(h:ℝ)) f x
  · have hk' : k < N := lt_of_le_of_ne hk he
    have hN : N-k = (N-(k+1))+1 := by omega
    funext x
    unfold cellHeat cascadeAt backward
    rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
    have ht : ((k+1:ℕ):ℝ)*(h:ℝ)-(k:ℝ)*(h:ℝ) = (h:ℝ) := by push_cast; ring
    rw [ht, hN, cascade]
    exact varianceLogHeat_eq_logSemigroup
      (cascade_regular hf hLip c h _ _).smooth.continuous.measurable (c k) h x

lemma cellHeat_right (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N k : ℕ) (hk : k < N) :
    cellHeat c h f N k (((k+1:ℕ):ℝ)*(h:ℝ)) = cascadeAt c h f N (k+1) := by
  funext x
  dsimp only [cellHeat]
  rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
  exact backward_terminal _ _ _ _

lemma cellHeat_seam {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N k : ℕ) (hk : k < N) :
    cellHeat c h f N k (((k+1:ℕ):ℝ)*(h:ℝ)) =
      cellHeat c h f N (k+1) (((k+1:ℕ):ℝ)*(h:ℝ)) := by
  rw [cellHeat_right c h f N k hk, cellHeat_left hf hLip c h N (k+1) (by omega)]

end ZeroTemperatureSK.Heat

namespace ZeroTemperatureSK.Heat

lemma hasFDerivAt_scaled_joint {g : ℝ → ℝ} (hgc : ContDiff ℝ 1 g)
    (hg : ExponentialBound g) (hg' : ExponentialBound (deriv g)) (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => scaled q.2 g q.1)
      (scaled p.2 (deriv g) p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
       (∫ y, y*deriv g (p.1+p.2*y) ∂gaussianReal 0 1) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  obtain ⟨A,K,hA⟩ := hg'
  let L : ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun y =>
    ContinuousLinearMap.fst ℝ ℝ ℝ+y • ContinuousLinearMap.snd ℝ ℝ ℝ
  let D : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun q y => deriv g (q.1+q.2*y) • L y
  let R : ℝ := (A:ℝ)*Real.exp ((K:ℝ)*(|p.1|+1))
  let k : ℝ := (K:ℝ)*(|p.2|+1)
  have hgi : Integrable (fun y => deriv g (p.1+p.2*y)) (gaussianReal 0 1) :=
    integrable_scaled_of_expBound hgc.continuous_deriv_one.measurable ⟨A,K,hA⟩ _ _
  have hygi : Integrable (fun y => y*deriv g (p.1+p.2*y)) (gaussianReal 0 1) :=
    integrable_mul_scaled_of_expBound hgc.continuous_deriv_one.measurable ⟨A,K,hA⟩ _ _
  have hDi : Integrable (D p) (gaussianReal 0 1) := by
    have hv := (hgi.smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
      (hygi.smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))
    apply hv.congr
    filter_upwards [] with y
    simp only [D,L,smul_add,smul_smul,Pi.add_apply]
    congr 2; ring
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q : ℝ × ℝ => fun y : ℝ => g (q.1+q.2*y)) (F' := D)
    (bound := fun y : ℝ => R*(1+|y|)*Real.exp (k*|y|))
    (Metric.ball_mem_nhds p (show (0:ℝ)<1 by norm_num))
    (Filter.Eventually.of_forall (fun q => by fun_prop))
    (integrable_scaled_of_expBound hgc.continuous.measurable hg p.2 p.1)
    hDi.aestronglyMeasurable
    (by
      filter_upwards [] with y q hq
      have hx : |q.1| ≤ |p.1|+1 := by
        have hdq := (max_lt_iff.mp (show max (dist q.1 p.1) (dist q.2 p.2) < 1 from hq)).1
        rw [Real.dist_eq] at hdq
        have ht := abs_add_le (q.1-p.1) p.1
        rw [sub_add_cancel] at ht
        linarith
      have ha : |q.2| ≤ |p.2|+1 := by
        have hdq := (max_lt_iff.mp (show max (dist q.1 p.1) (dist q.2 p.2) < 1 from hq)).2
        rw [Real.dist_eq] at hdq
        have ht := abs_add_le (q.2-p.2) p.2
        rw [sub_add_cancel] at ht
        linarith
      have hL : ‖L y‖ ≤ 1+|y| := by
        apply (norm_add_le _ _).trans
        simp only [norm_smul, Real.norm_eq_abs]
        have hf : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
        have hs : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
        nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg y)]
      dsimp only [D]
      rw [norm_smul, Real.norm_eq_abs]
      have hb : |deriv g (q.1+q.2*y)| ≤ R*Real.exp (k*|y|) := by
        apply (exponentialBound_scaled hA q.1 q.2 y (|p.2|+1) ha).trans
        dsimp only [R,k]
        gcongr
      calc
        _ ≤ (R*Real.exp (k*|y|))*(1+|y|) := mul_le_mul hb hL (norm_nonneg _) (by positivity)
        _ = _ := by ring)
    (by
      have hi := ((integrable_exp_abs k 0 1).add (integrable_abs_mul_exp_abs k)).const_mul R
      convert hi using 1
      funext y; dsimp only [Pi.add_apply]; ring)
    (by
      filter_upwards [] with y q hq
      have hl : HasFDerivAt (fun q : ℝ × ℝ => q.1+q.2*y) (L y) q := by
        convert ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).add
          ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).mul_const y)) using 1
      convert (hgc.differentiable (by norm_num) (q.1+q.2*y)).hasDerivAt.comp_hasFDerivAt q hl using 1
      rfl
      )
  have heq : (∫ y, D p y ∂gaussianReal 0 1) =
      scaled p.2 (deriv g) p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
       (∫ y, y*deriv g (p.1+p.2*y) ∂gaussianReal 0 1) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro z
    rw [ContinuousLinearMap.integral_apply hDi]
    dsimp only [D,L]
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    have he : (fun y => deriv g (p.1+p.2*y)*(z.1+y*z.2)) =
        fun y => deriv g (p.1+p.2*y)*z.1+(y*deriv g (p.1+p.2*y))*z.2 := by funext y; ring
    rw [he, integral_add (hgi.mul_const _) (hygi.mul_const _), integral_mul_const, integral_mul_const]
    rfl
  rw [heq] at hd
  exact hd

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
