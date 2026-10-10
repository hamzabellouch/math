import OAI.Probability.SLE.Stochastic.WienerGridIndependence
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! Nondegenerate independent Gaussian increments give positive
probability to every based finite grid tube. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma gaussianReal_ball_pos (a c : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (r : ℝ) (hr : 0 < r) : 0 < gaussianReal a v (ball c r) := by
  by_contra h
  have hz : gaussianReal a v (ball c r)=0 := le_antisymm (le_of_not_gt h) bot_le
  have hz' := gaussianReal_absolutelyContinuous' a hv hz
  exact (measure_ball_pos volume c hr).ne' hz'

lemma nat_path_error_le (x y : ℕ → ℝ) (m : ℕ) (δ : ℝ)
    (hzero : x 0=y 0)
    (hinc : ∀ k < m, |(x (k+1)-x k)-(y (k+1)-y k)| ≤ δ) :
    ∀ k ≤ m, |x k-y k| ≤ (k:ℝ)*δ := by
  intro k
  induction k with
  | zero => intro _; simp [hzero]
  | succ k ih =>
    intro hk
    have hk' : k < m := by omega
    calc
      |x (k+1)-y (k+1)| = |(x k-y k)+((x (k+1)-x k)-(y (k+1)-y k))| := by congr 1; ring
      _ ≤ |x k-y k|+|(x (k+1)-x k)-(y (k+1)-y k)| := abs_add_le _ _
      _ ≤ (k:ℝ)*δ+δ := add_le_add (ih (by omega)) (hinc k hk')
      _ = ((k+1:ℕ):ℝ)*δ := by push_cast; ring

lemma wienerGridTime_strictMono (n : ℕ) : StrictMono (wienerGridTime n) := by
  intro i j hij
  apply NNReal.coe_lt_coe.mp
  change (i:ℝ)/(n+1) < (j:ℝ)/(n+1)
  exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hij)

theorem wienerGrid_tube_pos (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (n : ℕ) (f : ℕ → ℝ) (hf : f 0=0) (ε : ℝ) (hε : 0 < ε) :
    0 < W {b | ∀ i : Fin (n+3), |b (wienerGridTime n i)-f i| < ε} := by
  classical
  have : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let m := n+2
  let δ : ℝ := ε/(m+1:ℝ)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let X : Fin m → Target.Driver → ℝ := fun i b =>
    b (wienerGridTime n (i+1))-b (wienerGridTime n i)
  let c : Fin m → ℝ := fun i => f (i+1)-f i
  have hind : iIndepFun X W := by
    exact hW.hasIndepIncrements m (fun i => wienerGridTime n i)
      ((wienerGridTime_strictMono n).monotone.comp (fun _ _ h => h))
  have hpos (i : Fin m) : 0 < W (X i ⁻¹' ball (c i) δ) := by
    have ht : wienerGridTime n i < wienerGridTime n (i+1) :=
      wienerGridTime_strictMono n (by omega)
    have hv : nndist (wienerGridTime n (i+1):ℝ) (wienerGridTime n i:ℝ) ≠ 0 := by
      intro h
      exact (ne_of_gt (show (wienerGridTime n i:ℝ)<wienerGridTime n (i+1) from ht))
        (eq_of_nndist_eq_zero h)
    have hLaw := hW.hasLaw_sub (wienerGridTime n (i+1)) (wienerGridTime n i)
    have he := hLaw.measure_eq (isOpen_ball.measurableSet : MeasurableSet (ball (c i) δ))
    exact he ▸ gaussianReal_ball_pos 0 (c i) _ hv δ hδ
  have hprod := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i => ball (c i) δ) (fun _ _ => isOpen_ball.measurableSet)
  have hall : 0 < W (⋂ i : Fin m, X i ⁻¹' ball (c i) δ) := by
    have he : W (⋂ i : Fin m, X i ⁻¹' ball (c i) δ) = ∏ i, W (X i ⁻¹' ball (c i) δ) := by
      simpa only [Finset.mem_univ,iInter_true] using hprod
    rw [he]
    exact bot_lt_iff_ne_bot.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => (hpos i).ne'))
  refine hall.trans_le (measure_mono ?_)
  intro b hb i
  have hb' : ∀ k < m,
      |(b (wienerGridTime n (k+1))-b (wienerGridTime n k))-(f (k+1)-f k)| ≤ δ := by
    intro k hk
    have h := mem_iInter.mp hb ⟨k,hk⟩
    exact (show |X ⟨k,hk⟩ b-c ⟨k,hk⟩| < δ from by simpa only [mem_preimage,mem_ball,Real.dist_eq] using h).le
  have he := nat_path_error_le (fun k => b (wienerGridTime n k)) f m δ
    (by simp [wienerGridTime,hf]) hb' i (by have := i.isLt; omega)
  refine he.trans_lt ?_
  calc
    (i:ℝ)*δ ≤ (m:ℝ)*δ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show (i:ℕ) ≤ m from by have := i.isLt; omega)) hδ.le
    _ < ε := by dsimp [δ]; rw [← mul_div_assoc,div_lt_iff₀ (by positivity)]; nlinarith

end SLEExactGauge

end

end OAI
