import Mathlib

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.FinitePicard
open scoped NNReal BigOperators

variable {I E X : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoMetricSpace X]

def correction (w : I → I → ℝ) (φ : I → E → E) (z : I → E) : I → E :=
  fun i => ∑j,w i j • φ j (z j)

def step (w : I → I → ℝ) (φ : I → E → E) (a z : I → E) : I → E :=
  a+correction w φ z

lemma correction_lipschitz (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hw : ∀i,∑j,|w i j|≤A) (hφ : ∀i,LipschitzWith K (φ i)) :
    LipschitzWith (A*K) (correction w φ) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro z v
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  simp only [correction,dist_eq_norm,←Finset.sum_sub_distrib,←smul_sub]
  calc
    _ ≤ ∑j,‖w i j • (φ j (z j)-φ j (v j))‖ := norm_sum_le _ _
    _ ≤ ∑j,|w i j| *((K:ℝ)*dist z v) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [dist_eq_norm] using ((hφ j).dist_le_mul (z j) (v j)).trans
        (mul_le_mul_of_nonneg_left (dist_le_pi_dist z v j) (by positivity))
    _ = (∑j,|w i j|)*((K:ℝ)*dist z v) := by rw [Finset.sum_mul]
    _ ≤ (A:ℝ)*((K:ℝ)*dist z v) := mul_le_mul_of_nonneg_right (hw i) (by positivity)
    _ = _ := by simp only [NNReal.coe_mul,dist_eq_norm]; ring

lemma step_lipschitz (w : I → I → ℝ) (φ : I → E → E) (a : I → E) {A K : ℝ≥0}
    (hw : ∀i,∑j,|w i j|≤A) (hφ : ∀i,LipschitzWith K (φ i)) :
    LipschitzWith (A*K) (step w φ a) := by
  apply LipschitzWith.of_dist_le_mul
  intro z v
  simpa only [step,dist_add_left] using (correction_lipschitz w φ hw hφ).dist_le_mul z v

theorem iterate_defect {Y : Type*} [PseudoMetricSpace Y] {q : ℝ≥0}
    {G : Y → Y} (hG : LipschitzWith q G) (hq : (q:ℝ)≤1/2)
    (a e : Y) {D : ℝ} (hD : 0≤D) (he : dist (G e) e≤D) (n : ℕ) :
    dist (G^[n] a) e≤2*D+(q:ℝ)^n*dist a e := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply,pow_zero,one_mul]; linarith
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ dist (G (G^[n] a)) (G e)+dist (G e) e := dist_triangle _ _ _
      _ ≤ (q:ℝ)*dist (G^[n] a) e+D := add_le_add (hG.dist_le_mul _ _) he
      _ ≤ (q:ℝ)*(2*D+(q:ℝ)^n*dist a e)+D := add_le_add (mul_le_mul_of_nonneg_left ih q.coe_nonneg) le_rfl
      _ ≤ 2*D+(q:ℝ)^(n+1)*dist a e := by
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right hq hD]

def nodes (w : I → I → ℝ) (φ : I → E → E) (a : X → I → E) : ℕ → X → I → E
  | 0 => a
  | n+1 => fun x => step w φ (a x) (nodes w φ a n x)

omit [PseudoMetricSpace X] in
lemma nodes_eq_iterate (w : I → I → ℝ) (φ : I → E → E) (a : X → I → E)
    (n : ℕ) (x : X) : nodes w φ a n x=(step w φ (a x))^[n] (a x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nodes,ih,Function.iterate_succ_apply']

theorem nodes_lipschitz (w : I → I → ℝ) (φ : I → E → E) (a : X → I → E)
    {A K B : ℝ≥0} (hw : ∀i,∑j,|w i j|≤A) (hφ : ∀i,LipschitzWith K (φ i))
    (ha : LipschitzWith B a) (hq : (A*K:ℝ≥0)≤1/2) (n : ℕ) :
    LipschitzWith (2*B) (nodes w φ a n) := by
  induction n with
  | zero => exact ha.weaken (by nlinarith)
  | succ n ih =>
    change LipschitzWith (2*B) (fun x => a x+correction w φ (nodes w φ a n x))
    apply (ha.add ((correction_lipschitz w φ hw hφ).comp ih)).weaken
    nlinarith

theorem nodes_correction_lipschitz (w : I → I → ℝ) (φ : I → E → E) (a : X → I → E)
    {A K B : ℝ≥0} (hw : ∀i,∑j,|w i j|≤A) (hφ : ∀i,LipschitzWith K (φ i))
    (ha : LipschitzWith B a) (hq : (A*K:ℝ≥0)≤1/2) (n : ℕ) :
    LipschitzWith (A*K*(2*B)) (fun x => nodes w φ a (n+1) x-a x) := by
  convert (correction_lipschitz w φ hw hφ).comp (nodes_lipschitz w φ a hw hφ ha hq n) using 1
  funext x
  simp only [nodes,step,add_sub_cancel_left,Function.comp_apply]
end LogConcaveSampling.FinitePicard

end

end

end

end OAI
