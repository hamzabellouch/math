import Mathlib

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff
namespace ParabolicInterpolation
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def difference : (n : ℕ) → (V → E) → (Fin n → V) → V → E
  | 0,f,_,x => f x
  | n+1,f,v,x => difference n f (Fin.tail v) (x+v 0)-difference n f (Fin.tail v) x

def average : (n : ℕ) → (V → E) → (Fin n → V) → V → E
  | 0,f,_,x => f x
  | n+1,f,v,x => average n (fun y => ∫ t in (0:ℝ)..1, f (y+t • v 0)) (Fin.tail v) x
omit [CompleteSpace E] in
lemma continuous_average (n : ℕ) (f : V → E) (hf : Continuous f) (v : Fin n → V) :
    Continuous (average n f v) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih =>
    apply ih
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hf.comp (by fun_prop)
omit [CompleteSpace E] in
lemma average_sub (n : ℕ) (f g : V → E) (hf : Continuous f) (hg : Continuous g)
    (v : Fin n → V) (x : V) :
    average n (fun y => f y-g y) v x=average n f v x-average n g v x := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    change average n (fun y => ∫ t in (0:ℝ)..1, f (y+t • v 0)-g (y+t • v 0)) _ x=_
    have he (y : V) : (∫ t in (0:ℝ)..1, f (y+t • v 0)-g (y+t • v 0))=
        (∫ t in (0:ℝ)..1, f (y+t • v 0))-(∫ t in (0:ℝ)..1, g (y+t • v 0)) := by
      apply intervalIntegral.integral_sub
      · exact (hf.comp (by fun_prop)).intervalIntegrable _ _
      · exact (hg.comp (by fun_prop)).intervalIntegrable _ _
    simp only [he]
    apply ih
    · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact hf.comp (by fun_prop)
    · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact hg.comp (by fun_prop)
lemma average_const (n : ℕ) (c : E) (v : Fin n → V) (x : V) :
    average n (fun _ => c) v x=c := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [average] using ih (Fin.tail v)
omit [CompleteSpace E] in
lemma average_translate (n : ℕ) (f : V → E) (v : Fin n → V) (x z : V) :
    average n (fun y => f (y+z)) v x=average n f v (x+z) := by
  induction n generalizing f x with
  | zero => rfl
  | succ n ih =>
    simp only [average]
    have he : (fun y => ∫ t in (0:ℝ)..1, f (y+t • v 0+z))=
        fun y => (fun w => ∫ t in (0:ℝ)..1, f (w+t • v 0)) (y+z) := by
      funext y
      congr 1
      funext t
      congr 1
      abel
    rw [he]
    exact ih (fun y : V => ∫ t in (0:ℝ)..1, f (y+t • v 0)) (Fin.tail v) x
lemma average_jet_eq_difference (n : ℕ) (f : V → E) (hf : ContDiff ℝ n f)
    (v : Fin n → V) (x : V) :
    average n (fun y => iteratedFDeriv ℝ n f y v) v x=difference n f v x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    let g : V → E := fun y => iteratedFDeriv ℝ n f y (Fin.tail v)
    have hgd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
      hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
    have hgc : Continuous g := hgd.continuous.eval_const _
    have he (y : V) : (∫ t in (0:ℝ)..1, iteratedFDeriv ℝ (n+1) f (y+t • v 0) v)=g (y+v 0)-g y := by
      have hd (t : ℝ) : HasDerivAt (fun t => g (y+t • v 0))
          (iteratedFDeriv ℝ (n+1) f (y+t • v 0) v) t := by
        rw [(hgd (y+t • v 0)).iteratedFDeriv_succ_apply_left']
        have hg : DifferentiableAt ℝ g (y+t • v 0) :=
          (hgd _).continuousMultilinear_apply_const _
        convert hg.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const (v 0) |>.const_add y) using 1
        all_goals simp [Function.comp_def,g]
      have hc0 : Continuous (fun z : V => iteratedFDeriv ℝ (n+1) f z v) :=
        (hf.continuous_iteratedFDeriv le_rfl).eval_const v
      have hc1 : Continuous (fun t : ℝ => y+t • v 0) := by fun_prop
      have hc : Continuous (fun t : ℝ => iteratedFDeriv ℝ (n+1) f (y+t • v 0) v) := hc0.comp hc1
      simpa [g] using intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hd t) (hc.intervalIntegrable 0 1)
    change average n (fun y => ∫ t in (0:ℝ)..1, iteratedFDeriv ℝ (n+1) f (y+t • v 0) v) _ x=_
    simp only [he]
    rw [average_sub n (fun y => g (y+v 0)) g (hgc.comp (continuous_id.add continuous_const)) hgc,average_translate]
    rw [ih (hf.of_le (by exact_mod_cast Nat.le_succ n)),ih (hf.of_le (by exact_mod_cast Nat.le_succ n))]
    rfl
omit [CompleteSpace E] in
lemma norm_average_le (n : ℕ) (f : V → E) (v : Fin n → V) (x : V) (C : ℝ)
    (_hC : 0≤C) (hf : ∀ y, ‖y-x‖≤∑ i, ‖v i‖ → ‖f y‖≤C) :
    ‖average n f v x‖≤C := by
  induction n generalizing f with
  | zero => exact hf x (by simp)
  | succ n ih =>
    apply ih
    intro y hy
    have hi : ‖∫ t in (0:ℝ)..1, f (y+t • v 0)‖≤C*|1-0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => by
      apply hf
      have ht' : t∈Icc (0:ℝ) 1 := by
        simp only [uIoc_of_le zero_le_one] at ht
        exact ⟨ht.1.le,ht.2⟩
      calc
        ‖y+t • v 0-x‖=‖(y-x)+t • v 0‖ := by congr 1; abel
        _≤‖y-x‖+‖t • v 0‖ := norm_add_le _ _
        _≤(∑ i, ‖Fin.tail v i‖)+‖v 0‖ := by
          gcongr
          rw [norm_smul,Real.norm_of_nonneg ht'.1]
          exact mul_le_of_le_one_left (norm_nonneg _) ht'.2
        _=∑ i, ‖v i‖ := by rw [Fin.sum_univ_succ]; simp [Fin.tail]; ring)
    simpa using hi
omit [NormedSpace ℝ V] [NormedSpace ℝ E] [CompleteSpace E] in
lemma norm_difference_le (n : ℕ) (f : V → E) (v : Fin n → V) (x : V) (U : ℝ)
    (_hU : 0≤U) (hf : ∀ y, ‖y-x‖≤∑ i, ‖v i‖ → ‖f y‖≤U) :
    ‖difference n f v x‖≤2^n*U := by
  induction n generalizing x with
  | zero => simpa [difference] using hf x (by simp)
  | succ n ih =>
    have hsum : (∑ i : Fin n, ‖Fin.tail v i‖)+‖v 0‖=∑ i, ‖v i‖ := by
      rw [Fin.sum_univ_succ]; simp [Fin.tail]; ring
    have h1 := ih (Fin.tail v) (x+v 0) (fun y hy => hf y (by
      calc
        ‖y-x‖=‖(y-(x+v 0))+v 0‖ := by congr 1; abel
        _≤‖y-(x+v 0)‖+‖v 0‖ := norm_add_le _ _
        _≤(∑ i : Fin n, ‖Fin.tail v i‖)+‖v 0‖ := add_le_add hy le_rfl
        _=_ := hsum))
    have h2 := ih (Fin.tail v) x (fun y hy => hf y (by
      rw [←hsum]; exact hy.trans (le_add_of_nonneg_right (norm_nonneg _))))
    exact (norm_sub_le _ _).trans (by change _≤2^(n+1)*U; rw [pow_succ]; linarith)
end ParabolicInterpolation

end

end OAI
