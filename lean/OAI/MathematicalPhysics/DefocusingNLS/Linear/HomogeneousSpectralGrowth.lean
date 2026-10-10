import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialODEGrowthRegularity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularField
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Star

namespace OAI

/-! # Coarse derivative growth for the coupled profile and spectral state

The six scalar coordinates form a polynomial differential system with the
single explicit coefficient `exp(2t)`. This records coarse derivative
growth, independent of the order of any comparison polynomial.
-/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

inductive HomogeneousSpectralExpr where
  | constant : ℂ → HomogeneousSpectralExpr
  | exponential : HomogeneousSpectralExpr
  | coordinate : Fin 6 → HomogeneousSpectralExpr
  | add : HomogeneousSpectralExpr → HomogeneousSpectralExpr → HomogeneousSpectralExpr
  | mul : HomogeneousSpectralExpr → HomogeneousSpectralExpr → HomogeneousSpectralExpr
  | conjugate : HomogeneousSpectralExpr → HomogeneousSpectralExpr

namespace HomogeneousSpectralExpr

noncomputable def eval (F : ℝ → Fin 6 → ℂ) (t : ℝ) : HomogeneousSpectralExpr → ℂ
  | constant c => c
  | exponential => (Real.exp (2 * t) : ℂ)
  | coordinate i => F t i
  | add a b => eval F t a + eval F t b
  | mul a b => eval F t a * eval F t b
  | conjugate a => star (eval F t a)

def pow (a : HomogeneousSpectralExpr) : ℕ → HomogeneousSpectralExpr
  | 0 => constant 1
  | n + 1 => mul (pow a n) a

theorem eval_pow (F : ℝ → Fin 6 → ℂ) (t : ℝ) (a : HomogeneousSpectralExpr) (n : ℕ) :
    eval F t (pow a n) = eval F t a ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow, eval, ih, pow_succ]

noncomputable def differentiate (D : Fin 6 → HomogeneousSpectralExpr) :
    HomogeneousSpectralExpr → HomogeneousSpectralExpr
  | constant _ => constant 0
  | exponential => mul (constant 2) exponential
  | coordinate i => D i
  | add a b => add (differentiate D a) (differentiate D b)
  | mul a b => add (mul (differentiate D a) b) (mul a (differentiate D b))
  | conjugate a => conjugate (differentiate D a)

theorem hasDerivAt_eval (D : Fin 6 → HomogeneousSpectralExpr)
    (F : ℝ → Fin 6 → ℂ) (t : ℝ)
    (hF : ∀ i, HasDerivAt (fun s => F s i) (eval F t (D i)) t)
    (a : HomogeneousSpectralExpr) :
    HasDerivAt (fun s => eval F s a) (eval F t (differentiate D a)) t := by
  induction a with
  | constant c => exact hasDerivAt_const t c
  | exponential =>
      convert (((hasDerivAt_id t).const_mul 2).exp).ofReal_comp using 1 <;>
        simp only [eval, differentiate, Complex.ofReal_mul, Complex.ofReal_ofNat, id_eq, mul_one]
      ring
  | coordinate i => exact hF i
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | conjugate a ha => exact ha.star

theorem iteratedDeriv_eval (D : Fin 6 → HomogeneousSpectralExpr)
    (F : ℝ → Fin 6 → ℂ) (L : ℝ)
    (hF : ∀ t, L < t → ∀ i, HasDerivAt (fun s => F s i) (eval F t (D i)) t)
    (a : HomogeneousSpectralExpr) (k : ℕ) : ∀ t, L < t →
      iteratedDeriv k (fun s => eval F s a) t = eval F t ((differentiate D)^[k] a) := by
  induction k with
  | zero => intro t ht; rfl
  | succ k ih =>
      intro t ht
      have he : iteratedDeriv k (fun s => eval F s a) =ᶠ[𝓝 t]
          (fun s => eval F s ((differentiate D)^[k] a)) := by
        filter_upwards [eventually_gt_nhds ht] with s hs
        exact ih s hs
      rw [iteratedDeriv_succ, he.deriv_eq]
      simpa only [Function.iterate_succ_apply'] using
        (hasDerivAt_eval D F t (hF t ht) ((differentiate D)^[k] a)).deriv

theorem eval_exponential_bound (a : HomogeneousSpectralExpr)
    (F : ℝ → Fin 6 → ℂ) (M U : ℝ) (hM : 0 ≤ M)
    (hF : ∀ t, U ≤ t → ∀ i, ‖F t i‖ ≤ M) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ t, U ≤ t → 0 ≤ t →
      ‖eval F t a‖ ≤ B * Real.exp (C * t) := by
  induction a with
  | constant c =>
      refine ⟨0, ‖c‖, le_rfl, norm_nonneg _, ?_⟩
      intro t ht ht0
      simp only [eval, zero_mul, Real.exp_zero, mul_one, le_refl]
  | exponential =>
      refine ⟨2, 1, by norm_num, by norm_num, ?_⟩
      intro t ht ht0
      simp only [eval, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), one_mul, le_refl]
  | coordinate i =>
      refine ⟨0, M, le_rfl, hM, ?_⟩
      intro t ht ht0
      simpa only [eval, zero_mul, Real.exp_zero, mul_one] using hF t ht i
  | add a b ha hb =>
      obtain ⟨Ca, Ba, hCa, hBa, hba⟩ := ha
      obtain ⟨Cb, Bb, hCb, hBb, hbb⟩ := hb
      refine ⟨Ca + Cb, Ba + Bb, add_nonneg hCa hCb, add_nonneg hBa hBb, ?_⟩
      intro t ht ht0
      have hea : Real.exp (Ca * t) ≤ Real.exp ((Ca + Cb) * t) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have heb : Real.exp (Cb * t) ≤ Real.exp ((Ca + Cb) * t) :=
        Real.exp_le_exp.mpr (by nlinarith)
      calc
        ‖eval F t (add a b)‖ ≤ ‖eval F t a‖ + ‖eval F t b‖ := norm_add_le _ _
        _ ≤ Ba * Real.exp (Ca * t) + Bb * Real.exp (Cb * t) :=
          add_le_add (hba t ht ht0) (hbb t ht ht0)
        _ ≤ Ba * Real.exp ((Ca + Cb) * t) + Bb * Real.exp ((Ca + Cb) * t) :=
          add_le_add (mul_le_mul_of_nonneg_left hea hBa) (mul_le_mul_of_nonneg_left heb hBb)
        _ = _ := by ring
  | mul a b ha hb =>
      obtain ⟨Ca, Ba, hCa, hBa, hba⟩ := ha
      obtain ⟨Cb, Bb, hCb, hBb, hbb⟩ := hb
      refine ⟨Ca + Cb, Ba * Bb, add_nonneg hCa hCb, mul_nonneg hBa hBb, ?_⟩
      intro t ht ht0
      calc
        ‖eval F t (mul a b)‖ = ‖eval F t a‖ * ‖eval F t b‖ := norm_mul _ _
        _ ≤ (Ba * Real.exp (Ca * t)) * (Bb * Real.exp (Cb * t)) :=
          mul_le_mul (hba t ht ht0) (hbb t ht ht0) (norm_nonneg _)
            (mul_nonneg hBa (Real.exp_pos _).le)
        _ = (Ba * Bb) * (Real.exp (Ca * t) * Real.exp (Cb * t)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
  | conjugate a ha =>
      obtain ⟨C, B, hC, hB, hb⟩ := ha
      refine ⟨C, B, hC, hB, ?_⟩
      intro t ht ht0
      simpa only [eval, norm_star] using hb t ht ht0

theorem derivatives_exponential_bound (D : Fin 6 → HomogeneousSpectralExpr)
    (F : ℝ → Fin 6 → ℂ) (L U M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ t, L < t → ∀ i, HasDerivAt (fun s => F s i) (eval F t (D i)) t)
    (hB : ∀ t, U ≤ t → ∀ i, ‖F t i‖ ≤ M) (i : Fin 6) (k : ℕ) :
    ∃ C B T : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ L < T ∧ ∀ t, T ≤ t →
      ‖iteratedDeriv k (fun s => F s i) t‖ ≤ B * Real.exp (C * t) := by
  obtain ⟨C, B, hC, hB0, hb⟩ := eval_exponential_bound
    ((differentiate D)^[k] (coordinate i)) F M U hM hB
  let T := max U (max 0 (L + 1))
  have hLT : L < T := lt_of_lt_of_le (by linarith : L < L + 1)
    ((le_max_right 0 _).trans (le_max_right U _))
  refine ⟨C, B, T, hC, hB0, hLT, ?_⟩
  intro t ht
  rw [show iteratedDeriv k (fun s => F s i) t =
      eval F t ((differentiate D)^[k] (coordinate i)) from
    iteratedDeriv_eval D F L hF (coordinate i) k t (hLT.trans_le ht)]
  exact hb t ((le_max_left U _).trans ht)
    (((le_max_left 0 _).trans (le_max_right U _)).trans ht)

end HomogeneousSpectralExpr

end DefocusingNLS

end OAI
