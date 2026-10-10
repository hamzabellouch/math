import OAI.Analysis.FreeGroupFactor.PolynomialFlow

namespace OAI

noncomputable section

universe uA uι

open Set Metric
open scoped NNReal Topology BigOperators ContDiff

open scoped BigOperators ContDiff
namespace FreeGroupFactorMain
namespace NCPolynomial

inductive Expr (ι : Type uι) where
  | scalar : ℂ → Expr ι
  | gen : ι → Expr ι
  | add : Expr ι → Expr ι → Expr ι
  | mul : Expr ι → Expr ι → Expr ι

def degree {ι : Type uι} : Expr ι → ℕ
  | .scalar _ => 0
  | .gen _ => 1
  | .add p q => max (degree p) (degree q)
  | .mul p q => degree p + degree q

def mass {ι : Type uι} : Expr ι → ℝ
  | .scalar c => ‖c‖
  | .gen _ => 1
  | .add p q => mass p + mass q
  | .mul p q => mass p * mass q

def eval {ι : Type uι} {A : Type uA} [Semiring A] [Algebra ℂ A] (X : ι → A) : Expr ι → A
  | .scalar c => algebraMap ℂ A c
  | .gen i => X i
  | .add p q => eval X p + eval X q
  | .mul p q => eval X p * eval X q

def delta {ι : Type uι} (V : ι → Expr ι) : Expr ι → Expr ι
  | .scalar _ => .scalar 0
  | .gen i => V i
  | .add p q => .add (delta V p) (delta V q)
  | .mul p q => .add (.mul (delta V p) q) (.mul p (delta V q))

 theorem mass_nonneg {ι : Type uι} (p : Expr ι) : 0 ≤ mass p := by
  induction p with
  | scalar c => exact norm_nonneg _
  | gen i => exact zero_le_one
  | add p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq => exact mul_nonneg hp hq

 theorem degree_delta {ι : Type uι} (V : ι → Expr ι) (J : ℕ)
    (hV : ∀ i, degree (V i) ≤ J + 1) (p : Expr ι) :
    degree (delta V p) ≤ degree p + J := by
  induction p with
  | scalar c => simp [delta, degree]
  | gen i => simpa [delta, degree, Nat.add_comm] using hV i
  | add p q hp hq =>
    simp only [delta, degree]
    omega
  | mul p q hp hq =>
    simp only [delta, degree]
    omega

 theorem mass_delta {ι : Type uι} (V : ι → Expr ι) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ i, mass (V i) ≤ B) (p : Expr ι) :
    mass (delta V p) ≤ mass p * (degree p : ℝ) * B := by
  induction p with
  | scalar c => simp [delta, mass, degree]
  | gen i => simpa [delta, mass, degree] using hV i
  | add p q hp hq =>
    simp only [delta, mass, degree]
    have hl : (degree p : ℝ) ≤ (max (degree p) (degree q) : ℕ) := by exact_mod_cast le_max_left _ _
    have hr : (degree q : ℝ) ≤ (max (degree p) (degree q) : ℕ) := by exact_mod_cast le_max_right _ _
    calc
      mass (delta V p) + mass (delta V q) ≤
          mass p * (degree p : ℝ) * B + mass q * (degree q : ℝ) * B := add_le_add hp hq
      _ ≤ mass p * (max (degree p) (degree q) : ℕ) * B +
          mass q * (max (degree p) (degree q) : ℕ) * B := by
        gcongr
        · exact mass_nonneg p
        · exact mass_nonneg q
      _ = _ := by ring
  | mul p q hp hq =>
    simp only [delta, mass, degree, Nat.cast_add]
    calc
      mass (delta V p) * mass q + mass p * mass (delta V q) ≤
          (mass p * (degree p : ℝ) * B) * mass q +
          mass p * (mass q * (degree q : ℝ) * B) := by
        exact add_le_add (mul_le_mul_of_nonneg_right hp (mass_nonneg q))
          (mul_le_mul_of_nonneg_left hq (mass_nonneg p))
      _ = _ := by ring

 theorem degree_iterate {ι : Type uι} (V : ι → Expr ι) (J : ℕ)
    (hV : ∀ i, degree (V i) ≤ J + 1) (p : Expr ι) (r : ℕ) :
    degree ((delta V)^[r] p) ≤ degree p + r * J := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact (degree_delta V J hV _).trans (by simpa [Nat.add_mul, Nat.add_assoc] using Nat.add_le_add_right ih J)

 theorem mass_iterate {ι : Type uι} (V : ι → Expr ι) (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ i, degree (V i) ≤ J + 1) (hmass : ∀ i, mass (V i) ≤ B)
    (p : Expr ι) (r : ℕ) :
    mass ((delta V)^[r] p) ≤
      mass p * (B * ((degree p : ℝ) + J)) ^ r * (r.factorial : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    have hd : (degree ((delta V)^[r] p) : ℝ) ≤ ((degree p : ℝ) + J) * (r + 1) := by
      have := degree_iterate V J hdeg p r
      have hh : (degree ((delta V)^[r] p) : ℝ) ≤ (degree p : ℝ) + r * J := by exact_mod_cast this
      nlinarith [Nat.cast_nonneg (α := ℝ) (degree p)]
    calc
      mass (delta V ((delta V)^[r] p)) ≤
          mass ((delta V)^[r] p) * (degree ((delta V)^[r] p) : ℝ) * B :=
        mass_delta V B hB hmass _
      _ ≤ (mass p * (B * ((degree p : ℝ) + J)) ^ r * (r.factorial : ℝ)) *
          (((degree p : ℝ) + J) * (r + 1)) * B := by
        gcongr
        exact mul_nonneg (mul_nonneg (mass_nonneg p) (pow_nonneg (mul_nonneg hB (by positivity)) _)) (by positivity)
      _ = _ := by simp [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]; ring

 theorem norm_eval {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A]
    (X : ι → A) (R : ℝ) (hR : 1 ≤ R) (hX : ∀ i, ‖X i‖ ≤ R) (p : Expr ι) :
    ‖eval X p‖ ≤ mass p * R ^ degree p := by
  induction p with
  | scalar c => simp [eval, mass, degree, norm_algebraMap']
  | gen i => simpa [eval, mass, degree] using hX i
  | add p q hp hq =>
    simp only [eval, mass, degree]
    calc
      ‖eval X p + eval X q‖ ≤ ‖eval X p‖ + ‖eval X q‖ := norm_add_le _ _
      _ ≤ mass p * R ^ degree p + mass q * R ^ degree q := add_le_add hp hq
      _ ≤ mass p * R ^ max (degree p) (degree q) +
          mass q * R ^ max (degree p) (degree q) := by
        gcongr
        · exact mass_nonneg p
        · exact le_max_left _ _
        · exact mass_nonneg q
        · exact le_max_right _ _
      _ = _ := by ring
  | mul p q hp hq =>
    simp only [eval, mass, degree, pow_add]
    calc
      ‖eval X p * eval X q‖ ≤ ‖eval X p‖ * ‖eval X q‖ := norm_mul_le _ _
      _ ≤ (mass p * R ^ degree p) * (mass q * R ^ degree q) := by
        exact mul_le_mul hp hq (norm_nonneg _) (mul_nonneg (mass_nonneg _) (pow_nonneg (by linarith) _))
      _ = _ := by ring

 theorem hasDerivAt_eval {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    (X : ℝ → ι → A) (V : ι → Expr ι) (t : ℝ)
    (hX : ∀ i, HasDerivAt (fun s => X s i) (eval (X t) (V i)) t) (p : Expr ι) :
    HasDerivAt (fun s => eval (X s) p) (eval (X t) (delta V p)) t := by
  induction p with
  | scalar c => simpa [eval, delta] using hasDerivAt_const t (algebraMap ℂ A c)
  | gen i => exact hX i
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq

 theorem eval_delta {ι : Type uι} {A : Type uA} [Ring A] [Algebra ℂ A]
    (X : ι → A) (V : ι → Expr ι) (D : A →ₗ[ℂ] A)
    (h1 : D 1 = 0) (hmul : ∀ a b, D (a * b) = D a * b + a * D b)
    (hX : ∀ i, D (X i) = eval X (V i)) (p : Expr ι) :
    D (eval X p) = eval X (delta V p) := by
  induction p with
  | scalar c =>
    simp only [eval, delta, map_zero]
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
  | gen i => exact hX i
  | add p q hp hq => simpa only [eval, delta, map_add] using congrArg₂ (· + ·) hp hq
  | mul p q hp hq => simp only [eval, delta, hmul, hp, hq]

theorem norm_eval_iterate {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    [NormOneClass A] (X : ι → A) (R : ℝ) (hR : 1 ≤ R) (hX : ∀ i, ‖X i‖ ≤ R)
    (V : ι → Expr ι) (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ i, degree (V i) ≤ J + 1) (hmass : ∀ i, mass (V i) ≤ B)
    (p : Expr ι) (r : ℕ) :
    ‖eval X ((delta V)^[r] p)‖ ≤
      (mass p * R ^ degree p) * (B * ((degree p : ℝ) + J) * R ^ J) ^ r *
        (r.factorial : ℝ) := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  calc
    ‖eval X ((delta V)^[r] p)‖ ≤ mass ((delta V)^[r] p) * R ^ degree ((delta V)^[r] p) :=
      norm_eval X R hR hX _
    _ ≤ (mass p * (B * ((degree p : ℝ) + J)) ^ r * (r.factorial : ℝ)) *
        R ^ (degree p + r * J) := by
      apply mul_le_mul (mass_iterate V J B hB hdeg hmass p r)
      · exact pow_le_pow_right₀ hR (degree_iterate V J hdeg p r)
      · exact pow_nonneg hR0 _
      · exact mul_nonneg (mul_nonneg (mass_nonneg p) (pow_nonneg (mul_nonneg hB (by positivity)) _)) (by positivity)
    _ = _ := by simp only [pow_add, mul_pow, ← pow_mul]; rw [Nat.mul_comm r J]; ring

theorem smooth_eval {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    (X : ℝ → ι → A) (hX : ∀ i, ContDiff ℝ ∞ (fun t => X t i)) (p : Expr ι) :
    ContDiff ℝ ∞ (fun t => eval (X t) p) := by
  induction p with
  | scalar c => exact contDiff_const
  | gen i => exact hX i
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq

theorem iteratedDeriv_eval {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    (X : ℝ → ι → A) (V : ι → Expr ι)
    (hX : ∀ t i, HasDerivAt (fun s => X s i) (eval (X t) (V i)) t)
    (p : Expr ι) (r : ℕ) :
    iteratedDeriv r (fun t => eval (X t) p) = fun t => eval (X t) ((delta V)^[r] p) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(hasDerivAt_eval X V t (hX t) _).deriv, Function.iterate_succ_apply']

end NCPolynomial
end FreeGroupFactorMain

end

end OAI
