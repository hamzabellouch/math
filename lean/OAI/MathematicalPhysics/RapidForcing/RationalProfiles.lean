import OAI.MathematicalPhysics.RapidForcing.EffectiveProfiles

namespace OAI

section

open scoped BigOperators Topology
open Filter
namespace RapidForcing.EffectiveProfile

structure Ball where
  center : ℚ
  radius : ℚ
  deriving DecidableEq

def Ball.exact (q : ℚ) : Ball := ⟨q, 0⟩
def Ball.add (a b : Ball) : Ball := ⟨a.center + b.center, a.radius + b.radius⟩
def Ball.mul (a b : Ball) : Ball :=
  ⟨a.center * b.center,
    |a.center| * b.radius + |b.center| * a.radius + a.radius * b.radius⟩

def Ball.pow (a : Ball) : ℕ → Ball
  | 0 => Ball.exact 1
  | n + 1 => (a.pow n).mul a

def Ball.denInv (a : Ball) : Ball :=
  ⟨(max (1 / 16) a.center)⁻¹, 256 * a.radius⟩

def Ball.Covers (a : Ball) (x : ℝ) : Prop := |(a.center : ℝ) - x| ≤ (a.radius : ℝ)

lemma Ball.Covers.radius_nonneg {a : Ball} {x : ℝ} (h : a.Covers x) : 0 ≤ a.radius := by
  exact_mod_cast (abs_nonneg _).trans h

lemma Ball.covers_exact (q : ℚ) : (Ball.exact q).Covers q := by
  simp [Ball.exact, Covers]

lemma Ball.Covers.add {a b : Ball} {x y : ℝ} (ha : a.Covers x) (hb : b.Covers y) :
    (a.add b).Covers (x + y) := by
  dsimp [Covers, Ball.add] at *
  push_cast
  calc
    |(a.center : ℝ) + b.center - (x + y)| = |(a.center - x) + (b.center - y)| := by congr 1; ring
    _ ≤ |(a.center : ℝ) - x| + |(b.center : ℝ) - y| := abs_add_le _ _
    _ ≤ _ := add_le_add ha hb

lemma Ball.Covers.mul {a b : Ball} {x y : ℝ} (ha : a.Covers x) (hb : b.Covers y) :
    (a.mul b).Covers (x * y) := by
  have he1 : (0 : ℝ) ≤ a.radius := by exact_mod_cast ha.radius_nonneg
  have he2 : (0 : ℝ) ≤ b.radius := by exact_mod_cast hb.radius_nonneg
  change |((a.center * b.center : ℚ) : ℝ) - x * y| ≤ _
  simp only [Ball.mul, Rat.cast_mul, Rat.cast_add, Rat.cast_abs]
  calc
    |(a.center : ℝ) * b.center - x*y| =
      |(a.center : ℝ) * (b.center - y) + (b.center : ℝ) * (a.center - x) -
        (a.center - x) * (b.center - y)| := by congr 1; ring
    _ ≤ |(a.center : ℝ) * (b.center - y)| + |(b.center : ℝ) * (a.center - x)| +
        |((a.center : ℝ) - x) * (b.center - y)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [abs_mul]
      gcongr
      · exact hb
      · exact ha
      · exact ha
      · exact hb

lemma Ball.Covers.pow {a : Ball} {x : ℝ} (ha : a.Covers x) (n : ℕ) :
    (a.pow n).Covers (x ^ n) := by
  induction n with
  | zero => simpa [Ball.pow] using Ball.covers_exact 1
  | succ n ih => simpa only [Ball.pow, pow_succ] using ih.mul ha

lemma clamp_dist (c x : ℝ) (hx : (1 / 16 : ℝ) ≤ x) :
    |max (1 / 16) c - x| ≤ |c - x| := by
  by_cases hc : (1 / 16 : ℝ) ≤ c
  · rw [max_eq_right hc]
  · rw [max_eq_left (le_of_not_ge hc), abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith

lemma Ball.Covers.denInv {a : Ball} {x : ℝ} (ha : a.Covers x) (hx : (1 / 16 : ℝ) ≤ x) :
    a.denInv.Covers x⁻¹ := by
  have hz : (1 / 16 : ℝ) ≤ max (1 / 16) (a.center : ℝ) := le_max_left _ _
  have hp : 0 < max (1 / 16) (a.center : ℝ) := lt_of_lt_of_le (by norm_num) hz
  have hxp : 0 < x := by linarith
  have hprod : (1 / 256 : ℝ) ≤ max (1 / 16) (a.center : ℝ) * x := by nlinarith
  change |(((max (1 / 16) a.center)⁻¹ : ℚ) : ℝ) - x⁻¹| ≤ _
  simp only [Ball.denInv, Rat.cast_inv, Rat.cast_max, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, Rat.cast_mul]
  rw [inv_sub_inv hp.ne' hxp.ne', abs_div, abs_mul, abs_of_pos hp, abs_of_pos hxp,
    (div_le_iff₀ (mul_pos hp hxp))]
  calc
    |x - max (1 / 16) (a.center : ℝ)| = |max (1 / 16) (a.center : ℝ) - x| := abs_sub_comm _ _
    _ ≤ |(a.center : ℝ) - x| := clamp_dist _ _ hx
    _ ≤ (a.radius : ℝ) := ha
    _ ≤ 256 * (a.radius : ℝ) * (max (1 / 16) (a.center : ℝ) * x) := by
      have hnon : (0 : ℝ) ≤ a.radius := by exact_mod_cast ha.radius_nonneg
      nlinarith

def Encloses (b : ℕ → Ball) (x : ℝ) : Prop :=
  (∀ k, (b k).Covers x) ∧ Tendsto (fun k => ((b k).radius : ℝ)) atTop (𝓝 0)

lemma Encloses.centers {b : ℕ → Ball} {x : ℝ} (h : Encloses b x) :
    Tendsto (fun k => ((b k).center : ℝ)) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => by simpa only [Real.norm_eq_abs, Ball.Covers] using h.1 k) h.2

lemma encloses_exact (q : ℚ) : Encloses (fun _ => Ball.exact q) q :=
  ⟨fun _ => Ball.covers_exact _, by simp [Ball.exact]⟩

lemma Encloses.add {a b : ℕ → Ball} {x y : ℝ} (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (fun k => (a k).add (b k)) (x + y) :=
  ⟨fun k => (ha.1 k).add (hb.1 k), by simpa only [Ball.add, Rat.cast_add, add_zero] using ha.2.add hb.2⟩

lemma Encloses.mul {a b : ℕ → Ball} {x y : ℝ} (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (fun k => (a k).mul (b k)) (x * y) := by
  refine ⟨fun k => (ha.1 k).mul (hb.1 k), ?_⟩
  simpa only [Ball.mul, Rat.cast_add, Rat.cast_mul, Rat.cast_abs, mul_zero, add_zero]
    using ((ha.centers.abs.mul hb.2).add (hb.centers.abs.mul ha.2)).add (ha.2.mul hb.2)

lemma Encloses.pow {a : ℕ → Ball} {x : ℝ} (ha : Encloses a x) (n : ℕ) :
    Encloses (fun k => (a k).pow n) (x ^ n) := by
  induction n with
  | zero => simpa [Ball.pow] using encloses_exact 1
  | succ n ih => simpa [Ball.pow, pow_succ] using ih.mul ha

lemma Encloses.denInv {a : ℕ → Ball} {x : ℝ} (ha : Encloses a x) (hx : (1 / 16 : ℝ) ≤ x) :
    Encloses (fun k => (a k).denInv) x⁻¹ :=
  ⟨fun k => (ha.1 k).denInv hx, by simpa [Ball.denInv] using ha.2.const_mul 256⟩

def expTerms (q : ℚ) (k : ℕ) : ℕ := k + ⌈2 * |q|⌉₊ + 1

def expBall (q : ℚ) (k : ℕ) : Ball :=
  let n := expTerms q k
  ⟨∑ j ∈ Finset.range n, q ^ j / (j.factorial : ℚ),
    |q| ^ n / (n.factorial : ℚ) * 2⟩

lemma expTerms_large (q : ℚ) (k : ℕ) : |(q : ℝ)| / (expTerms q k + 1) ≤ 1 / 2 := by
  have h : 2 * |(q : ℝ)| ≤ (⌈2 * |q|⌉₊ : ℝ) := by
    exact_mod_cast (Nat.le_ceil (2 * |q|))
  have hp : (0 : ℝ) < expTerms q k + 1 := by positivity
  apply (div_le_iff₀ hp).2
  dsimp [expTerms]
  push_cast
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  linarith

lemma expBall_covers (q : ℚ) (k : ℕ) : (expBall q k).Covers (Real.exp q) := by
  have h := @Complex.exp_bound' (q : ℂ) (expTerms q k) (by
    simpa only [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, Nat.cast_succ]
      using expTerms_large q k)
  have heq : (Complex.exp (q : ℂ) - ∑ j ∈ Finset.range (expTerms q k),
      (q : ℂ) ^ j / (j.factorial : ℂ)) =
      ((Real.exp (q : ℝ) - ∑ j ∈ Finset.range (expTerms q k),
        (q : ℝ) ^ j / (j.factorial : ℝ)) : ℝ) := by
    simp
  rw [heq, Complex.norm_real, Real.norm_eq_abs] at h
  simpa [Ball.Covers, expBall, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
    ← Complex.ofReal_ratCast, Rat.norm_cast_real] using h

lemma expBall_encloses (q : ℚ) : Encloses (expBall q) (Real.exp q) := by
  refine ⟨expBall_covers q, ?_⟩
  have hN : Tendsto (expTerms q) atTop atTop := by
    exact (tendsto_add_atTop_nat (⌈2 * |q|⌉₊ + 1)).congr (fun n => by simp [expTerms, Nat.add_assoc])
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop |(q : ℝ)|).comp hN
  simpa [expBall] using h.mul_const 2

def monoBall (n : ℕ) (q : ℚ) (k : ℕ) : Ball :=
  if q ≤ 0 then Ball.exact 0 else
    (Ball.exact (q⁻¹ ^ n)).mul (expBall (-q⁻¹) k)

def glueBall : GluePoly → ℚ → ℕ → Ball
  | [], _, _ => Ball.exact 0
  | (a, n) :: p, q, k => ((Ball.exact a).mul (monoBall n q k)).add (glueBall p q k)

lemma monoBall_encloses (n : ℕ) (q : ℚ) : Encloses (monoBall n q) (monoGlue n q) := by
  by_cases hq : q ≤ 0
  · have hx : (q : ℝ) ≤ 0 := by exact_mod_cast hq
    unfold monoBall
    simpa [hq, monoGlue, expNegInvGlue.zero_of_nonpos hx] using encloses_exact 0
  · have hx : ¬ (q : ℝ) ≤ 0 := by exact_mod_cast hq
    unfold monoBall
    simpa [hq, monoGlue, expNegInvGlue, hx] using
      (encloses_exact (q⁻¹ ^ n)).mul (expBall_encloses (-q⁻¹))

lemma glueBall_encloses (p : GluePoly) (q : ℚ) : Encloses (glueBall p q) (glue p q) := by
  induction p with
  | nil => simpa [glueBall, glue] using encloses_exact 0
  | cons a p ih =>
    rcases a with ⟨a, n⟩
    exact ((encloses_exact a).mul (monoBall_encloses n q)).add ih

def Expr.numeric : Expr → ℚ → ℕ → Ball
  | .const a, _, _ => Ball.exact a
  | .left p, q, k => glueBall p q k
  | .right p, q, k => glueBall p (1 - q) k
  | .invDen n, q, k =>
    ((glueBall [(1, 0)] q k).add (glueBall [(1, 0)] (1 - q) k)).denInv.pow n
  | .add a b, q, k => (a.numeric q k).add (b.numeric q k)
  | .mul a b, q, k => (a.numeric q k).mul (b.numeric q k)

lemma Expr.numeric_encloses (e : Expr) (q : ℚ) : Encloses (e.numeric q) (e.value q) := by
  induction e with
  | const a => exact encloses_exact a
  | left p => exact glueBall_encloses p q
  | right p => simpa [Expr.value, Expr.numeric] using glueBall_encloses p (1 - q)
  | invDen n =>
    have hd : Encloses (fun k => (glueBall [(1, 0)] q k).add (glueBall [(1, 0)] (1 - q) k))
        (expNegInvGlue q + expNegInvGlue (1 - q)) := by
      simpa only [glue_one, Rat.cast_sub, Rat.cast_one] using
        (glueBall_encloses [(1, 0)] q).add (glueBall_encloses [(1, 0)] (1 - q))
    exact (hd.denInv (denominator_lower q)).pow n
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb

def Expr.numericError (e : Expr) (q : ℚ) (k : ℕ) (inputError : ℚ) : ℚ :=
  (e.numeric q k).radius + e.diff.bound * inputError

lemma Expr.numeric_error_le (e : Expr) (q : ℚ) (k : ℕ) (r : ℚ) (x : ℝ)
    (hx : |(q : ℝ) - x| ≤ (r : ℝ)) :
    |((e.numeric q k).center : ℝ) - e.value x| ≤ (e.numericError q k r : ℝ) := by
  have he := (e.numeric_encloses q).1 k
  have hd : |e.value q - e.value x| ≤ (e.diff.bound : ℝ) * |(q : ℝ) - x| := by
    exact e.lipschitz.dist_le_mul (q : ℝ) x
  calc
    _ ≤ |((e.numeric q k).center : ℝ) - e.value q| + |e.value q - e.value x| := abs_sub_le _ _ _
    _ ≤ (e.numeric q k).radius + (e.diff.bound : ℝ) * (r : ℝ) :=
      add_le_add he (hd.trans (mul_le_mul_of_nonneg_left hx (by exact_mod_cast e.diff.bound_nonneg)))
    _ = _ := by simp [numericError]

end RapidForcing.EffectiveProfile

end

end OAI
