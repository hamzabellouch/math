import Mathlib
import OAI.Analysis.BoxTransport.Computation

namespace OAI

/-! Smooth expression calculus and effective mixed derivatives. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

abbrev Expr := Code

def node (m : ℕ) (e : Expr) : Expr := .prec (Denumerable.ofNat Expr m) e

def cst (q : QCode) : Expr := node (3 * Encodable.encode q) .zero

def invE (b : ℕ) (e : Expr) : Expr := node (3 * b + 1) e

def flatE (m : ℕ) (e : Expr) : Expr := node (3 * m + 2) e

def varE : Axis → Expr
  | none => .zero
  | some j => if j = 0 then .succ else if j = 1 then .left else .right

noncomputable def unaryValue (m : ℕ) (x : ℝ) : ℝ :=
  if m % 3 = 0 then Qval (Denumerable.ofNat QCode (m / 3))
  else if m % 3 = 1 then x⁻¹ else flatTerm (m / 3) x

noncomputable def value : Expr → SpaceTime → ℝ
  | .zero, p => p.1
  | .succ, p => p.2 0
  | .left, p => p.2 1
  | .right, p => p.2 2
  | .pair e f, p => value e p + value f p
  | .comp e f, p => value e p * value f p
  | .prec m e, p => unaryValue (Encodable.encode m) (value e p)
  | .rfind' e, p => -value e p

def Valid : Expr → Prop
  | .zero | .succ | .left | .right => True
  | .pair e f | .comp e f => Valid e ∧ Valid f
  | .prec m e => Valid e ∧ (Encodable.encode m % 3 = 1 →
      ∀ p, ((Encodable.encode m / 3 : ℕ) + 1 : ℝ)⁻¹ ≤ |value e p|)
  | .rfind' e => Valid e

@[simp] theorem value_node (m : ℕ) (e : Expr) (p : SpaceTime) :
    value (node m e) p = unaryValue m (value e p) := by simp [value, node]
@[simp] theorem value_cst (q : QCode) (p : SpaceTime) : value (cst q) p = (Qval q : ℝ) := by
  rw [cst, value_node]
  rw [unaryValue, ite_eq_left (by omega), Nat.mul_div_right _ (by omega), Denumerable.ofNat_encode]
@[simp] theorem value_invE (b : ℕ) (e : Expr) (p : SpaceTime) : value (invE b e) p = (value e p)⁻¹ := by
  simp [invE, unaryValue]
@[simp] theorem value_flatE (m : ℕ) (e : Expr) (p : SpaceTime) : value (flatE m e) p = flatTerm m (value e p) := by
  simp [flatE, unaryValue, Nat.mul_add_div (by omega : 0 < 3)]
@[simp] theorem valid_node (m : ℕ) (e : Expr) : Valid (node m e) ↔
    Valid e ∧ (m % 3 = 1 → ∀ p, ((m / 3 : ℕ) + 1 : ℝ)⁻¹ ≤ |value e p|) := by
  simp [Valid, node]
@[simp] theorem valid_cst (q : QCode) : Valid (cst q) := by simp [cst, Valid]
@[simp] theorem valid_flatE (m : ℕ) (e : Expr) : Valid (flatE m e) ↔ Valid e := by
  simp [flatE]
@[simp] theorem valid_invE (b : ℕ) (e : Expr) : Valid (invE b e) ↔
    Valid e ∧ ∀ p, ((b : ℝ) + 1)⁻¹ ≤ |value e p| := by simp [invE, Nat.mul_add_div (by omega : 0 < 3)]

@[simp] theorem value_varE (j : Axis) (p : SpaceTime) :
    value (varE j) p = match j with | none => p.1 | some i => p.2 i := by
  cases j with
  | none => rfl
  | some i => fin_cases i <;> simp [varE, value]
@[simp] theorem valid_varE (j : Axis) : Valid (varE j) := by
  cases j with
  | none => trivial
  | some i => fin_cases i <;> simp [varE, Valid]

theorem nonzero_of_inverse_bound {b : ℕ} {x : ℝ} (h : ((b : ℝ) + 1)⁻¹ ≤ |x|) : x ≠ 0 := by
  have hp : (0 : ℝ) < ((b : ℝ) + 1)⁻¹ := by positivity
  exact abs_pos.mp (hp.trans_le h)

theorem smooth_value {e : Expr} (he : Valid e) : ContDiff ℝ ∞ (value e) := by
  induction e with
  | zero => exact contDiff_fst
  | succ => exact (contDiff_apply ℝ ℝ (0 : Fin 3)).comp contDiff_snd
  | left => exact (contDiff_apply ℝ ℝ (1 : Fin 3)).comp contDiff_snd
  | right => exact (contDiff_apply ℝ ℝ (2 : Fin 3)).comp contDiff_snd
  | pair e f ih₁ ih₂ => exact (ih₁ he.1).add (ih₂ he.2)
  | comp e f ih₁ ih₂ => exact (ih₁ he.1).mul (ih₂ he.2)
  | rfind' e ih => exact (ih he).neg
  | prec m e _ ih =>
    change ContDiff ℝ ∞ (fun p => unaryValue (Encodable.encode m) (value e p))
    unfold unaryValue
    split_ifs with h₀ h₁
    · exact contDiff_const
    · exact (ih he.1).inv (fun p => nonzero_of_inverse_bound (he.2 h₁ p))
    · exact (contDiff_flatTerm _).comp (ih he.1)

def diffUnary (n : ℕ) (e de : Expr) : Expr :=
  if n % 3 = 0 then cst qZero
  else if n % 3 = 1 then .rfind' (.comp (.comp (invE (n / 3) e) (invE (n / 3) e)) de)
  else .comp (.pair (flatE (n / 3 + 2) e)
    (.rfind' (.comp (cst (qNat (n / 3))) (flatE (n / 3 + 1) e)))) de

def diff (j : Axis) : Expr → Expr
  | .zero => cst (if j = none then qOne else qZero)
  | .succ => cst (if j = some 0 then qOne else qZero)
  | .left => cst (if j = some 1 then qOne else qZero)
  | .right => cst (if j = some 2 then qOne else qZero)
  | .pair e f => .pair (diff j e) (diff j f)
  | .comp e f => .pair (.comp (diff j e) f) (.comp e (diff j f))
  | .prec m e => diffUnary (Encodable.encode m) e (diff j e)
  | .rfind' e => .rfind' (diff j e)

theorem valid_diff {e : Expr} (he : Valid e) (j : Axis) : Valid (diff j e) := by
  induction e with
  | zero | succ | left | right => exact valid_cst _
  | pair e f ih₁ ih₂ => exact ⟨ih₁ he.1, ih₂ he.2⟩
  | comp e f ih₁ ih₂ => exact ⟨⟨ih₁ he.1, he.2⟩, he.1, ih₂ he.2⟩
  | rfind' e ih => exact ih he
  | prec m e _ ih =>
    dsimp [diff, diffUnary]
    split_ifs with h₀ h₁
    · exact valid_cst _
    · have hi : Valid (invE (Encodable.encode m / 3) e) := (valid_invE _ _).2 ⟨he.1, he.2 h₁⟩
      exact ⟨⟨hi, hi⟩, ih he.1⟩
    · exact ⟨⟨(valid_flatE _ _).2 he.1, valid_cst _, (valid_flatE _ _).2 he.1⟩, ih he.1⟩

theorem value_diff {e : Expr} (he : Valid e) (j : Axis) (p : SpaceTime) :
    value (diff j e) p = fderiv ℝ (value e) p (coordinateDirection j) := by
  induction e with
  | zero =>
    cases j with
    | none => simp [diff, value, coordinateDirection, fderiv_fst]
    | some i => simp [diff, value, coordinateDirection, fderiv_fst]
  | succ =>
    have hd : fderiv ℝ (value Code.succ) p =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).comp
          (ContinuousLinearMap.snd ℝ ℝ Space) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).comp
        (ContinuousLinearMap.snd ℝ ℝ Space)).hasFDerivAt.fderiv
    rw [hd]
    cases j with
    | none => simp [diff, coordinateDirection]
    | some i => fin_cases i <;> simp [diff, coordinateDirection, coordinateVector]
  | left =>
    have hd : fderiv ℝ (value Code.left) p =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).comp
          (ContinuousLinearMap.snd ℝ ℝ Space) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).comp
        (ContinuousLinearMap.snd ℝ ℝ Space)).hasFDerivAt.fderiv
    rw [hd]
    cases j with
    | none => simp [diff, coordinateDirection]
    | some i => fin_cases i <;> simp [diff, coordinateDirection, coordinateVector]
  | right =>
    have hd : fderiv ℝ (value Code.right) p =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).comp
          (ContinuousLinearMap.snd ℝ ℝ Space) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).comp
        (ContinuousLinearMap.snd ℝ ℝ Space)).hasFDerivAt.fderiv
    rw [hd]
    cases j with
    | none => simp [diff, coordinateDirection]
    | some i => fin_cases i <;> simp [diff, coordinateDirection, coordinateVector]
  | pair e f ih₁ ih₂ =>
    have he' := (smooth_value he.1).differentiable (by simp)
    have hf' := (smooth_value he.2).differentiable (by simp)
    rw [diff, value, ih₁ he.1, ih₂ he.2]
    exact (congrArg (fun L : SpaceTime →L[ℝ] ℝ => L (coordinateDirection j))
      ((he' p).hasFDerivAt.add (hf' p).hasFDerivAt).fderiv).symm
  | comp e f ih₁ ih₂ =>
    have he' := (smooth_value he.1).differentiable (by simp)
    have hf' := (smooth_value he.2).differentiable (by simp)
    simp only [diff, value, ih₁ he.1, ih₂ he.2]
    have hd := ((he' p).hasFDerivAt.mul (hf' p).hasFDerivAt).fderiv
    change fderiv ℝ (fun p => value e p * value f p) p = _ at hd
    rw [hd]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  | rfind' e ih =>
    have he' := (smooth_value (e := e) he).differentiable (by simp)
    simp only [diff, value, ih he]
    have hd := (he' p).hasFDerivAt.neg.fderiv
    change fderiv ℝ (fun p => -value e p) p = _ at hd
    rw [hd]
    rfl
  | prec m e _ ih =>
    have he' := (smooth_value he.1).differentiable (by simp)
    change value (diffUnary (Encodable.encode m) e (diff j e)) p =
      fderiv ℝ (fun p => unaryValue (Encodable.encode m) (value e p)) p _
    unfold diffUnary unaryValue
    split_ifs with h₀ h₁
    · simp
    · have hn := nonzero_of_inverse_bound (he.2 h₁ p)
      simp only [value, value_invE, ih he.1]
      have hd := ((hasDerivAt_inv hn).comp_hasFDerivAt p (he' p).hasFDerivAt).fderiv
      change fderiv ℝ (fun p => (value e p)⁻¹) p = _ at hd
      rw [hd]
      simp [pow_two, mul_assoc]
    · simp only [value, value_cst, Qval_nat, Rat.cast_natCast, value_flatE, ih he.1]
      have hd := ((hasDerivAt_flatTerm (Encodable.encode m / 3) (value e p)).comp_hasFDerivAt p (he' p).hasFDerivAt).fderiv
      change fderiv ℝ (fun p => flatTerm (Encodable.encode m / 3) (value e p)) p = _ at hd
      rw [hd]
      simp only [smul_apply, smul_eq_mul]
      ring

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

def qGuardInv (b : ℕ) (q : QCode) : QCode :=
  if qLe (qInv (qNat (2 * (b + 1)))) (qAbs q) then qInv q else qZero

theorem qGuardInv_error (b : ℕ) (q : QCode) {x : ℝ}
    (hx : ((b : ℝ) + 1)⁻¹ ≤ |x|) :
    |x⁻¹ - (Qval (qGuardInv b q) : ℝ)| ≤ 2 * ((b : ℝ) + 1) ^ 2 * |x - (Qval q : ℝ)| := by
  let D : ℝ := (b : ℝ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hx0 := nonzero_of_inverse_bound hx
  have hxmul : 1 ≤ |x| * D := (inv_le_iff_one_le_mul₀ hD).mp hx
  have hinvx : |x⁻¹| ≤ D := by
    rw [abs_inv, inv_le_iff_one_le_mul₀ (abs_pos.mpr hx0)]
    nlinarith
  unfold qGuardInv
  split_ifs with hq
  · have hq' : (2 * D)⁻¹ ≤ |(Qval q : ℝ)| := by
      have h := (qLe_iff _ _).1 hq
      simp only [Qval_inv, Qval_nat, Qval_abs] at h
      have hc := (Rat.cast_le (K := ℝ)).2 h
      simpa [D] using hc
    have hq0 : (Qval q : ℝ) ≠ 0 := abs_pos.mp ((by positivity : (0 : ℝ) < (2 * D)⁻¹).trans_le hq')
    have hinvq : |(Qval q : ℝ)⁻¹| ≤ 2 * D := by
      rw [abs_inv, inv_le_iff_one_le_mul₀ (abs_pos.mpr hq0)]
      have h := (inv_le_iff_one_le_mul₀ (by positivity : 0 < 2 * D)).mp hq'
      nlinarith
    simp only [Qval_inv, Rat.cast_inv]
    have hi : x⁻¹ - (Qval q : ℝ)⁻¹ = x⁻¹ * (Qval q : ℝ)⁻¹ * ((Qval q : ℝ) - x) := by
      field_simp
    rw [hi, abs_mul, abs_mul, abs_sub_comm (Qval q : ℝ) x]
    calc
      |x⁻¹| * |(Qval q : ℝ)⁻¹| * |x - (Qval q : ℝ)| ≤ D * (2 * D) * |x - (Qval q : ℝ)| := by
        gcongr
      _ = _ := by dsimp [D]; ring
  · have hq' : |(Qval q : ℝ)| < (2 * D)⁻¹ := by
      have h := lt_of_not_ge ((qLe_iff _ _).not.mp hq)
      simp only [Qval_inv, Qval_nat, Qval_abs] at h
      have hc := (Rat.cast_lt (K := ℝ)).2 h
      simpa [D] using hc
    have hdist : (2 * D)⁻¹ ≤ |x - (Qval q : ℝ)| := by
      have ht := abs_add_le (x - (Qval q : ℝ)) (Qval q : ℝ)
      have hid : (2 * D)⁻¹ + (2 * D)⁻¹ = D⁻¹ := by field_simp; ring
      dsimp [D] at hx ⊢ hq' hid
      rw [sub_add_cancel] at ht
      linarith
    simp only [Qval_zero, Rat.cast_zero, sub_zero]
    have hmul := mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ 2 * D ^ 2)
    have hid : 2 * D ^ 2 * (2 * D)⁻¹ = D := by field_simp
    rw [hid] at hmul
    exact hinvx.trans hmul

def unaryBound (m : ℕ) (_radius : ℕ) : ℕ :=
  if m % 3 = 0 then qBound (Denumerable.ofNat QCode (m / 3))
  else if m % 3 = 1 then m / 3 + 1 else (m / 3).factorial

def boundE (R : ℕ) : Expr → ℕ
  | .zero | .succ | .left | .right => R
  | .pair e f => boundE R e + boundE R f
  | .comp e f => boundE R e * boundE R f
  | .prec m _ => unaryBound (Encodable.encode m) R
  | .rfind' e => boundE R e

def unaryAmp (m A : ℕ) : ℕ :=
  if m % 3 = 0 then 0
  else if m % 3 = 1 then 2 * (m / 3 + 1) ^ 2 * A
  else flatLipschitzBound (m / 3) * A + 1

def ampE (R : ℕ) : Expr → ℕ
  | .zero | .succ | .left | .right => 0
  | .pair e f => ampE R e + ampE R f
  | .comp e f => (boundE R e + ampE R e) * ampE R f + boundE R f * ampE R e
  | .prec m e => unaryAmp (Encodable.encode m) (ampE R e)
  | .rfind' e => ampE R e

theorem coord_le_norm (j : Axis) (p : SpaceTime) :
    |value (varE j) p| ≤ ‖p‖ := by
  cases j with
  | none => exact norm_fst_le p
  | some j =>
    simpa using (norm_le_pi_norm p.2 j).trans (norm_snd_le p)

theorem value_bound {e : Expr} (he : Valid e) (R : ℕ) {p : SpaceTime} (hp : ‖p‖ ≤ R) :
    |value e p| ≤ boundE R e := by
  induction e with
  | zero => exact (coord_le_norm none p).trans hp
  | succ => exact (coord_le_norm (some 0) p).trans hp
  | left => exact (coord_le_norm (some 1) p).trans hp
  | right => exact (coord_le_norm (some 2) p).trans hp
  | pair e f ih₁ ih₂ =>
    exact (abs_add_le _ _).trans (by exact_mod_cast add_le_add (ih₁ he.1) (ih₂ he.2))
  | comp e f ih₁ ih₂ =>
    simpa only [value, boundE, Nat.cast_mul, abs_mul] using
      mul_le_mul (ih₁ he.1) (ih₂ he.2) (abs_nonneg _) (Nat.cast_nonneg _)
  | rfind' e ih => simpa only [value, abs_neg, boundE] using ih he
  | prec m e _ ih =>
    simp only [value, unaryValue, boundE, unaryBound]
    split_ifs with h₀ h₁
    · exact_mod_cast Qval_bound (Denumerable.ofNat QCode (Encodable.encode m / 3))
    · have hb := he.2 h₁ p
      have hne := nonzero_of_inverse_bound hb
      rw [abs_inv, inv_le_iff_one_le_mul₀ (abs_pos.mpr hne)]
      have h := (inv_le_iff_one_le_mul₀ (by positivity : 0 < ((Encodable.encode m / 3 : ℕ) : ℝ) + 1)).mp hb
      push_cast
      nlinarith
    · exact flatTerm_bound _ _

noncomputable def unaryEval (m : ℕ) (q : QCode) (N : ℕ) : QCode :=
  if m % 3 = 0 then Denumerable.ofNat QCode (m / 3)
  else if m % 3 = 1 then qGuardInv (m / 3) q else qFlat (m / 3, q, N)

noncomputable def evalE (q : RationalPointCode) (N : ℕ) : Expr → QCode
  | .zero => q.1
  | .succ => q.2.1
  | .left => q.2.2.1
  | .right => q.2.2.2
  | .pair e f => qAdd (evalE q N e) (evalE q N f)
  | .comp e f => qMul (evalE q N e) (evalE q N f)
  | .prec m e => unaryEval (Encodable.encode m) (evalE q N e) N
  | .rfind' e => qNeg (evalE q N e)

theorem mul_approx {x y a b ε B C A D : ℝ}
    (_hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hA : 0 ≤ A) (_hD : 0 ≤ D)
    (hx : |x| ≤ B) (hy : |y| ≤ C) (ha : |x - a| ≤ A * ε) (hb : |y - b| ≤ D * ε) :
    |x * y - a * b| ≤ ((B + A) * D + C * A) * ε := by
  have haa : |a| ≤ B + A := by
    calc
      |a| = |(a - x) + x| := by rw [sub_add_cancel]
      _ ≤ |a - x| + |x| := abs_add_le _ _
      _ ≤ A * ε + B := by rw [abs_sub_comm]; gcongr
      _ ≤ B + A := by nlinarith
  have hid : x * y - a * b = a * (y - b) + y * (x - a) := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul]
  have hBn : 0 ≤ B + A := (abs_nonneg a).trans haa
  have hCn : 0 ≤ C := (abs_nonneg y).trans hy
  calc
    |a| * |y - b| + |y| * |x - a| ≤ (B + A) * (D * ε) + C * (A * ε) := by
      gcongr
    _ = _ := by ring

theorem evalE_error {e : Expr} (he : Valid e) (q : RationalPointCode) (N R : ℕ)
    (hR : ‖codeSpaceTime q‖ ≤ R) :
    |value e (codeSpaceTime q) - (Qval (evalE q N e) : ℝ)| ≤
      (ampE R e : ℝ) * ((N : ℝ) + 1)⁻¹ := by
  have hε : (0 : ℝ) ≤ ((N : ℝ) + 1)⁻¹ := by positivity
  have hε₁ : ((N : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  induction e with
  | zero => simp [value, evalE, codeSpaceTime, ampE, Qval, rationalValue]
  | succ => simp [value, evalE, codeSpaceTime, ampE, Qval, rationalValue]
  | left => simp [value, evalE, codeSpaceTime, ampE, Qval, rationalValue]
  | right => simp [value, evalE, codeSpaceTime, ampE, Qval, rationalValue]
  | pair e f ih₁ ih₂ =>
    simp only [value, evalE, Qval_add, Rat.cast_add, ampE, Nat.cast_add]
    have hee := ih₁ he.1
    have hff := ih₂ he.2
    have hid : value e (codeSpaceTime q) + value f (codeSpaceTime q) -
        ((Qval (evalE q N e) : ℝ) + (Qval (evalE q N f) : ℝ)) =
        (value e (codeSpaceTime q) - (Qval (evalE q N e) : ℝ)) +
        (value f (codeSpaceTime q) - (Qval (evalE q N f) : ℝ)) := by ring
    rw [hid, add_mul]
    exact (abs_add_le _ _).trans (add_le_add hee hff)
  | comp e f ih₁ ih₂ =>
    simp only [value, evalE, Qval_mul, Rat.cast_mul, ampE, Nat.cast_add, Nat.cast_mul]
    exact mul_approx hε hε₁ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (value_bound he.1 R hR) (value_bound he.2 R hR) (ih₁ he.1) (ih₂ he.2)
  | rfind' e ih => simpa only [value, evalE, Qval_neg, Rat.cast_neg, neg_sub_neg, abs_sub_comm, ampE] using ih he
  | prec m e _ ih =>
    have hchild := ih he.1
    simp only [value, evalE, unaryValue, unaryEval, ampE, unaryAmp]
    split_ifs with h₀ h₁
    · simp
    · have hg := qGuardInv_error (Encodable.encode m / 3) (evalE q N e) (he.2 h₁ (codeSpaceTime q))
      apply hg.trans
      push_cast
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hchild
        (by positivity : 0 ≤ 2 * ((Encodable.encode m / 3 : ℕ) + 1 : ℝ) ^ 2)
    · have hl := (flatTerm_lipschitz (Encodable.encode m / 3)).dist_le_mul
        (value e (codeSpaceTime q)) (Qval (evalE q N e))
      simp only [Real.dist_eq, NNReal.coe_natCast] at hl
      have ht := qFlat_error (Encodable.encode m / 3) (evalE q N e) N
      have hd := abs_sub_le (flatTerm (Encodable.encode m / 3) (value e (codeSpaceTime q)))
        (flatTerm (Encodable.encode m / 3) (Qval (evalE q N e)))
        (Qval (qFlat (Encodable.encode m / 3, evalE q N e, N)))
      apply hd.trans
      push_cast
      calc
        _ ≤ (flatLipschitzBound (Encodable.encode m / 3) : ℝ) *
            ((ampE R e : ℝ) * ((N : ℝ) + 1)⁻¹) + ((N : ℝ) + 1)⁻¹ := by
          gcongr
          exact hl.trans (mul_le_mul_of_nonneg_left hchild (Nat.cast_nonneg _))
        _ = _ := by ring

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

attribute [fun_prop] Primrec Computable
attribute [fun_prop] Primrec.const Primrec.id Primrec.fst Primrec.snd Primrec.comp Primrec.pair Primrec.succ Primrec.encode Primrec.ofNat
attribute [fun_prop] Computable.const Computable.id Computable.fst Computable.snd Computable.comp Computable.pair

@[fun_prop] theorem pr_add {α} [Primcodable α] {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a + g a) := Primrec.nat_add.comp hf hg
@[fun_prop] theorem pr_mul {α} [Primcodable α] {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a * g a) := Primrec.nat_mul.comp hf hg
@[fun_prop] theorem pr_sub {α} [Primcodable α] {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a - g a) := Primrec.nat_sub.comp hf hg
@[fun_prop] theorem pr_div {α} [Primcodable α] {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a / g a) := Primrec.nat_div.comp hf hg
@[fun_prop] theorem pr_mod {α} [Primcodable α] {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a % g a) := Primrec.nat_mod.comp hf hg
@[fun_prop] theorem pr_square {α} [Primcodable α] {f : α → ℕ} (hf : Primrec f) :
    Primrec (fun a => f a ^ 2) := by simpa only [pow_two] using pr_mul hf hf
@[fun_prop] theorem pr_pair {α} [Primcodable α] {f g : α → Expr} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => Code.pair (f a) (g a)) := Code.primrec₂_pair.comp hf hg
@[fun_prop] theorem pr_comp {α} [Primcodable α] {f g : α → Expr} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => Code.comp (f a) (g a)) := Code.primrec₂_comp.comp hf hg
@[fun_prop] theorem pr_prec {α} [Primcodable α] {f g : α → Expr} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => Code.prec (f a) (g a)) := Code.primrec₂_prec.comp hf hg
attribute [fun_prop] Code.primrec_rfind' primrec_qNat primrec_qBound primrec_qInv primrec_qAbs primrec_qNeg primrec_factorial

@[fun_prop] theorem pr_qAdd {α} [Primcodable α] {f g : α → QCode} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => qAdd (f a) (g a)) := primrec_qAdd.comp hf hg
@[fun_prop] theorem pr_qMul {α} [Primcodable α] {f g : α → QCode} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => qMul (f a) (g a)) := primrec_qMul.comp hf hg

@[fun_prop] theorem primrec_node : Primrec (fun p : ℕ × Expr => node p.1 p.2) := by
  unfold node; fun_prop
@[fun_prop] theorem pr_node {α} [Primcodable α] {m : α → ℕ} {e : α → Expr}
    (hm : Primrec m) (he : Primrec e) : Primrec (fun a => node (m a) (e a)) := primrec_node.comp (hm.pair he)
@[fun_prop] theorem primrec_cst : Primrec cst := by unfold cst; fun_prop
@[fun_prop] theorem pr_invE {α} [Primcodable α] {m : α → ℕ} {e : α → Expr}
    (hm : Primrec m) (he : Primrec e) : Primrec (fun a => invE (m a) (e a)) := by unfold invE; fun_prop
@[fun_prop] theorem pr_flatE {α} [Primcodable α] {m : α → ℕ} {e : α → Expr}
    (hm : Primrec m) (he : Primrec e) : Primrec (fun a => flatE (m a) (e a)) := by unfold flatE; fun_prop

@[fun_prop] theorem primrec_diffUnary :
    Primrec (fun p : ℕ × Expr × Expr => diffUnary p.1 p.2.1 p.2.2) := by
  unfold diffUnary
  apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 0))
  · fun_prop
  apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 1)) <;> fun_prop

theorem diff_eq_rec (j : Axis) (e : Expr) : diff j e =
    Code.recOn e (cst (if j = none then qOne else qZero))
      (cst (if j = some 0 then qOne else qZero))
      (cst (if j = some 1 then qOne else qZero))
      (cst (if j = some 2 then qOne else qZero))
      (fun _ _ de df => Code.pair de df)
      (fun e f de df => Code.pair (Code.comp de f) (Code.comp e df))
      (fun m e _ de => diffUnary (Encodable.encode m) e de)
      (fun _ de => Code.rfind' de) := by
  induction e <;> simp_all only [diff]

@[fun_prop] theorem primrec_diff : Primrec (fun p : Axis × Expr => diff p.1 p.2) := by
  simp_rw [diff_eq_rec]
  apply Code.primrec_recOn Primrec.snd
  · exact (show Primrec (fun j : Axis => cst (if j = none then qOne else qZero)) from Primrec.dom_finite _).comp Primrec.fst
  · exact (show Primrec (fun j : Axis => cst (if j = some 0 then qOne else qZero)) from Primrec.dom_finite _).comp Primrec.fst
  · exact (show Primrec (fun j : Axis => cst (if j = some 1 then qOne else qZero)) from Primrec.dom_finite _).comp Primrec.fst
  · exact (show Primrec (fun j : Axis => cst (if j = some 2 then qOne else qZero)) from Primrec.dom_finite _).comp Primrec.fst
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop

@[fun_prop] theorem primrec_unaryBound : Primrec (fun p : ℕ × ℕ => unaryBound p.1 p.2) := by
  unfold unaryBound
  apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 0))
  · fun_prop
  apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 1)) <;> fun_prop

theorem boundE_eq_rec (R : ℕ) (e : Expr) : boundE R e =
    Code.recOn e R R R R (fun _ _ a b => a + b) (fun _ _ a b => a * b)
      (fun m _ _ _ => unaryBound (Encodable.encode m) R) (fun _ a => a) := by
  induction e <;> simp_all only [boundE]

@[fun_prop] theorem primrec_boundE : Primrec (fun p : ℕ × Expr => boundE p.1 p.2) := by
  simp_rw [boundE_eq_rec]
  apply Code.primrec_recOn Primrec.snd <;> fun_prop

@[fun_prop] theorem primrec_unaryAmp : Primrec (fun p : ℕ × ℕ => unaryAmp p.1 p.2) := by
  unfold unaryAmp flatLipschitzBound
  apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 0))
  · fun_prop
  apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 1)) <;> fun_prop

theorem ampE_eq_rec (R : ℕ) (e : Expr) : ampE R e =
    Code.recOn e 0 0 0 0 (fun _ _ a b => a + b)
      (fun e f a b => (boundE R e + a) * b + boundE R f * a)
      (fun m _ _ a => unaryAmp (Encodable.encode m) a) (fun _ a => a) := by
  induction e <;> simp_all only [ampE]

@[fun_prop] theorem primrec_ampE : Primrec (fun p : ℕ × Expr => ampE p.1 p.2) := by
  simp_rw [ampE_eq_rec]
  apply Code.primrec_recOn Primrec.snd <;> fun_prop

@[fun_prop] theorem primrec_qGuardInv : Primrec (fun p : ℕ × QCode => qGuardInv p.1 p.2) := by
  unfold qGuardInv
  apply Primrec.ite (primrec_qLe.comp (by fun_prop) (by fun_prop)) <;> fun_prop

attribute [fun_prop] Primrec.to_comp computable_qFlat

@[fun_prop] theorem computable_unaryEval :
    Computable (fun p : ℕ × QCode × ℕ => unaryEval p.1 p.2.1 p.2.2) := by
  unfold unaryEval
  apply computable_ite (PrimrecPred.computablePred (Primrec.eq.comp (by fun_prop) (Primrec.const 0)))
  · fun_prop
  apply computable_ite (PrimrecPred.computablePred (Primrec.eq.comp (by fun_prop) (Primrec.const 1))) <;> fun_prop

theorem evalE_eq_rec (q : RationalPointCode) (N : ℕ) (e : Expr) : evalE q N e =
    Code.recOn e q.1 q.2.1 q.2.2.1 q.2.2.2
      (fun _ _ a b => qAdd a b) (fun _ _ a b => qMul a b)
      (fun m _ _ a => unaryEval (Encodable.encode m) a N) (fun _ a => qNeg a) := by
  induction e <;> simp_all only [evalE]

theorem computable_Expr_recOn {α σ}
    [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Computable c) {z : α → σ}
    (hz : Computable z) {s : α → σ} (hs : Computable s) {l : α → σ} (hl : Computable l) {r : α → σ}
    (hr : Computable r) {pr : α → Code → Code → σ → σ → σ}
    (hpr : Computable fun a : α × Code × Code × σ × σ => pr a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {co : α → Code → Code → σ → σ → σ}
    (hco : Computable fun a : α × Code × Code × σ × σ => co a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {pc : α → Code → Code → σ → σ → σ}
    (hpc : Computable fun a : α × Code × Code × σ × σ => pc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {rf : α → Code → σ → σ} (hrf : Computable fun a : α × Code × σ => rf a.1 a.2.1 a.2.2) :
    Computable (fun a : α => (Code.recOn (c a) (z a) (s a) (l a) (r a) (pr a) (co a) (pc a) (rf a) : σ)) :=
  Code.computable_recOn hc hz hs hl hr
    (pr := fun a b => pr a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpr)
    (co := fun a b => co a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hco)
    (pc := fun a b => pc a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpc)
    (rf := fun a b => rf a b.1 b.2) (.mk hrf)

@[fun_prop] theorem computable_evalE :
    Computable (fun p : RationalPointCode × ℕ × Expr => evalE p.1 p.2.1 p.2.2) := by
  simp_rw [evalE_eq_rec]
  apply computable_Expr_recOn (Computable.snd.comp Computable.snd) <;> fun_prop

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

def pointBound (q : RationalPointCode) : ℕ :=
  qBound q.1 + qBound q.2.1 + qBound q.2.2.1 + qBound q.2.2.2

@[fun_prop] theorem primrec_pointBound : Primrec pointBound := by unfold pointBound; fun_prop

theorem norm_code_le (q : RationalPointCode) : ‖codeSpaceTime q‖ ≤ pointBound q := by
  have h0 : |(Qval q.1 : ℝ)| ≤ (qBound q.1 : ℝ) := by exact_mod_cast Qval_bound q.1
  have h1 : |(Qval q.2.1 : ℝ)| ≤ (qBound q.2.1 : ℝ) := by exact_mod_cast Qval_bound q.2.1
  have h2 : |(Qval q.2.2.1 : ℝ)| ≤ (qBound q.2.2.1 : ℝ) := by exact_mod_cast Qval_bound q.2.2.1
  have h3 : |(Qval q.2.2.2 : ℝ)| ≤ (qBound q.2.2.2 : ℝ) := by exact_mod_cast Qval_bound q.2.2.2
  rw [Prod.norm_def, max_le_iff]
  constructor
  · change |(Qval q.1 : ℝ)| ≤ _
    unfold pointBound; push_cast; have := Nat.cast_nonneg (α := ℝ) (qBound q.2.1 + qBound q.2.2.1 + qBound q.2.2.2)
    push_cast at this; linarith
  · apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).2
    intro j
    fin_cases j <;> change |(Qval _ : ℝ)| ≤ _
    all_goals unfold pointBound; push_cast
    all_goals linarith [Nat.cast_nonneg (α := ℝ) (qBound q.1), Nat.cast_nonneg (α := ℝ) (qBound q.2.1),
      Nat.cast_nonneg (α := ℝ) (qBound q.2.2.1), Nat.cast_nonneg (α := ℝ) (qBound q.2.2.2)]

noncomputable def evalPrecise (e : Expr) (q : RationalPointCode) (N : ℕ) : QCode :=
  evalE q ((N + 1) * (ampE (pointBound q) e + 1)) e

@[fun_prop] theorem computable_evalPrecise :
    Computable (fun p : Expr × RationalPointCode × ℕ => evalPrecise p.1 p.2.1 p.2.2) := by
  unfold evalPrecise
  fun_prop

theorem amplification_precision (A N : ℕ) :
    (A : ℝ) * (((((N + 1) * (A + 1) : ℕ) : ℝ) + 1)⁻¹) ≤ ((N : ℝ) + 1)⁻¹ := by
  push_cast
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  have hn : (0 : ℝ) < N + 1 := by positivity
  apply (mul_le_mul_iff_right₀ hn).mp
  field_simp
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

theorem evalPrecise_error {e : Expr} (he : Valid e) (q : RationalPointCode) (N : ℕ) :
    |value e (codeSpaceTime q) - (Qval (evalPrecise e q N) : ℝ)| ≤ ((N : ℝ) + 1)⁻¹ :=
  (evalE_error he q _ _ (norm_code_le q)).trans (amplification_precision _ N)

def mixedE (ds : List Axis) (e : Expr) : Expr := ds.foldr diff e

@[simp] theorem mixedE_nil (e : Expr) : mixedE [] e = e := rfl
@[simp] theorem mixedE_cons (j : Axis) (ds : List Axis) (e : Expr) :
    mixedE (j :: ds) e = diff j (mixedE ds e) := rfl

@[fun_prop] theorem primrec_mixedE : Primrec (fun p : List Axis × Expr => mixedE p.1 p.2) := by
  unfold mixedE
  exact Primrec.list_foldr (h := fun _ p => diff p.1 p.2) Primrec.fst Primrec.snd (.mk (primrec_diff.comp Primrec.snd))

theorem valid_mixedE {e : Expr} (he : Valid e) (ds : List Axis) : Valid (mixedE ds e) := by
  induction ds with
  | nil => exact he
  | cons j ds ih => exact valid_diff ih j

theorem smooth_mixedDerivative {U : Field} (hU : ContDiff ℝ ∞ U) (ds : List Axis) :
    ContDiff ℝ ∞ (mixedDerivative ds U) := by
  induction ds with
  | nil => exact hU
  | cons j ds ih => exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem mixedDerivative_component {U : Field} (hU : ContDiff ℝ ∞ U)
    {es : Fin 3 → Expr} (he : ∀ j, Valid (es j)) (hval : ∀ p j, value (es j) p = U p j)
    (ds : List Axis) (p : SpaceTime) (j : Fin 3) :
    value (mixedE ds (es j)) p = mixedDerivative ds U p j := by
  induction ds generalizing p with
  | nil => exact hval p j
  | cons d ds ih =>
    rw [mixedE_cons, value_diff (valid_mixedE (he j) ds)]
    have hv : value (mixedE ds (es j)) = fun p => mixedDerivative ds U p j := by
      funext p
      exact ih p
    rw [hv, fderiv_apply ((smooth_mixedDerivative hU ds).differentiable (by simp) p)]
    rfl

theorem tsupport_mixedDerivative_subset (U : Field) (ds : List Axis) :
    tsupport (mixedDerivative ds U) ⊆ tsupport U := by
  induction ds with
  | nil => exact Set.Subset.rfl
  | cons j ds ih => exact (tsupport_fderiv_apply_subset ℝ (coordinateDirection j)).trans ih

theorem exists_supportRadius {U : Field} (hU : HasCompactSupport U) :
    ∃ R : ℕ, ∀ p ∈ tsupport U, ‖p‖ ≤ R := by
  obtain ⟨r, hr⟩ := hU.isCompact.isBounded.subset_closedBall (0 : SpaceTime)
  obtain ⟨R, hR⟩ := exists_nat_ge r
  refine ⟨R, fun p hp => ?_⟩
  have hp' : ‖p‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hr hp
  exact hp'.trans hR

def familyBound (R : ℕ) (es : Fin 3 → Expr) (ds : List Axis) : ℕ :=
  boundE R (mixedE ds (es 0)) + boundE R (mixedE ds (es 1)) + boundE R (mixedE ds (es 2))

@[fun_prop] theorem primrec_familyBound (R : ℕ) (es : Fin 3 → Expr) :
    Primrec (familyBound R es) := by unfold familyBound; fun_prop

theorem boundE_le_familyBound (R : ℕ) (es : Fin 3 → Expr) (ds : List Axis) (j : Fin 3) :
    boundE R (mixedE ds (es j)) ≤ familyBound R es ds := by
  fin_cases j <;> simp only [familyBound, Fin.reduceFinMk] <;> omega

theorem uniform_mixed_bound {U : Field} (hU : ContDiff ℝ ∞ U)
    {es : Fin 3 → Expr} (he : ∀ j, Valid (es j)) (hval : ∀ p j, value (es j) p = U p j)
    (R : ℕ) (hR : ∀ p ∈ tsupport U, ‖p‖ ≤ R) (ds : List Axis) (p : SpaceTime) (j : Fin 3) :
    |mixedDerivative ds U p j| ≤ familyBound R es ds := by
  by_cases hp : p ∈ tsupport U
  · rw [← mixedDerivative_component hU he hval]
    exact (value_bound (valid_mixedE (he j) ds) R (hR p hp)).trans
      (Nat.cast_le.mpr (boundE_le_familyBound R es ds j))
  · have hx : mixedDerivative ds U p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_mixedDerivative_subset U ds h))
    rw [hx]; simp only [Pi.zero_apply, abs_zero]; positivity

theorem spacetime_decomposition (p : SpaceTime) :
    p = ∑ j : Axis, value (varE j) p • coordinateDirection j := by
  simp only [Fintype.sum_option, Fin.sum_univ_three, value_varE]
  apply Prod.ext
  · simp [coordinateDirection]
  · funext j
    fin_cases j <;> simp [coordinateDirection, coordinateVector]

theorem opnorm_from_coordinates (L : SpaceTime →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hL : ∀ j : Axis, |L (coordinateDirection j)| ≤ M) : ‖L‖ ≤ 4 * M := by
  apply L.opNorm_le_bound (by positivity)
  intro p
  calc
    ‖L p‖ = ‖∑ j : Axis, value (varE j) p • L (coordinateDirection j)‖ := by
      conv_lhs => rw [spacetime_decomposition p]
      simp only [map_sum, map_smul]
    _ ≤ ∑ j : Axis, ‖value (varE j) p • L (coordinateDirection j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Axis, ‖p‖ * M := by
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (coord_le_norm j p) (hL j) (abs_nonneg _) (norm_nonneg _)
    _ = (4 * M) * ‖p‖ := by simp [Fintype.card_option]; ring

def gradientBound (R : ℕ) (es : Fin 3 → Expr) (ds : List Axis) : ℕ :=
  familyBound R es (none :: ds) + familyBound R es (some 0 :: ds) +
    familyBound R es (some 1 :: ds) + familyBound R es (some 2 :: ds)

@[fun_prop] theorem pr_list_cons {α β} [Primcodable α] [Primcodable β] {f : α → β} {g : α → List β}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a :: g a) := Primrec.list_cons.comp hf hg

@[fun_prop] theorem primrec_gradientBound (R : ℕ) (es : Fin 3 → Expr) :
    Primrec (gradientBound R es) := by unfold gradientBound; fun_prop

theorem familyBound_le_gradientBound (R : ℕ) (es : Fin 3 → Expr) (ds : List Axis) (d : Axis) :
    familyBound R es (d :: ds) ≤ gradientBound R es ds := by
  cases d with
  | none => unfold gradientBound; omega
  | some j => fin_cases j <;> simp only [gradientBound, Fin.reduceFinMk] <;> omega

theorem mixed_component_lipschitz {U : Field} (hU : ContDiff ℝ ∞ U)
    {es : Fin 3 → Expr} (he : ∀ j, Valid (es j)) (hval : ∀ p j, value (es j) p = U p j)
    (R : ℕ) (hR : ∀ p ∈ tsupport U, ‖p‖ ≤ R) (ds : List Axis) (j : Fin 3) :
    LipschitzWith (4 * gradientBound R es ds) (fun p => mixedDerivative ds U p j) := by
  have hs := smooth_mixedDerivative hU ds
  apply lipschitzWith_of_nnnorm_fderiv_le ((contDiff_pi.mp hs j).differentiable (by simp))
  intro p
  apply NNReal.coe_le_coe.mp
  simp only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat]
  apply opnorm_from_coordinates _ (Nat.cast_nonneg _)
  intro d
  rw [fderiv_apply (hs.differentiable (by simp) p)]
  change |mixedDerivative (d :: ds) U p j| ≤ _
  exact (uniform_mixed_bound hU he hval R hR (d :: ds) p j).trans
    (Nat.cast_le.mpr (familyBound_le_gradientBound R es ds d))

theorem effective_of_expressions {U : Field} (hU : ContDiff ℝ ∞ U) (hc : HasCompactSupport U)
    (es : Fin 3 → Expr) (he : ∀ j, Valid (es j)) (hval : ∀ p j, value (es j) p = U p j) :
    Effective U := by
  obtain ⟨R, hR⟩ := exists_supportRadius hc
  let ev : EvaluationRequest → RationalCode := fun r =>
    evalPrecise (mixedE r.1 (es r.2.2.2)) r.2.1 (2 * r.2.2.1 + 1)
  let md : List Axis × ℕ → ℕ := fun r =>
    ((2 * r.2 + 1) + 1) * (4 * gradientBound R es r.1 + 1)
  have hes : Primrec es := Primrec.dom_finite _
  have hev : Computable ev := by
    unfold ev
    have hs : Primrec (fun r : EvaluationRequest => es r.2.2.2) :=
      hes.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hm : Primrec (fun r : EvaluationRequest => mixedE r.1 (es r.2.2.2)) :=
      primrec_mixedE.comp (Primrec.fst.pair hs)
    have hp : Primrec (fun r : EvaluationRequest => 2 * r.2.2.1 + 1) := by fun_prop
    have hq : Primrec (fun r : EvaluationRequest => r.2.1) := Primrec.fst.comp Primrec.snd
    have hreq : Computable (fun r : EvaluationRequest => (mixedE r.1 (es r.2.2.2), r.2.1, 2 * r.2.2.1 + 1)) :=
      (hm.pair (hq.pair hp)).to_comp
    have h := computable_evalPrecise.comp hreq
    exact h
  have hmd : Computable md := by unfold md; fun_prop
  refine ⟨ev, md, familyBound R es, hev, hmd, (primrec_familyBound R es).to_comp, ?_, ?_⟩
  · intro ds q N p hp j
    have hl := (mixed_component_lipschitz hU he hval R hR ds j).dist_le_mul p (codeSpaceTime q)
    simp only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast] at hl
    have heval := evalPrecise_error (valid_mixedE (he j) ds) q (2 * N + 1)
    rw [mixedDerivative_component hU he hval ds (codeSpaceTime q) j] at heval
    change |mixedDerivative ds U p j - (Qval (evalPrecise (mixedE ds (es j)) q (2 * N + 1)) : ℝ)| ≤ _
    calc
      _ ≤ |mixedDerivative ds U p j - mixedDerivative ds U (codeSpaceTime q) j| +
          |mixedDerivative ds U (codeSpaceTime q) j - (Qval (evalPrecise (mixedE ds (es j)) q (2 * N + 1)) : ℝ)| := abs_sub_le _ _ _
      _ ≤ (4 * (gradientBound R es ds : ℝ)) * ((md (ds, N) : ℝ) + 1)⁻¹ +
          (((2 * N + 1 : ℕ) : ℝ) + 1)⁻¹ := by
        apply add_le_add _ heval
        exact hl.trans (mul_le_mul_of_nonneg_left hp (by positivity))
      _ ≤ (((2 * N + 1 : ℕ) : ℝ) + 1)⁻¹ + (((2 * N + 1 : ℕ) : ℝ) + 1)⁻¹ := by
        apply add_le_add _ le_rfl
        simpa only [md, Nat.cast_mul, Nat.cast_ofNat] using amplification_precision (4 * gradientBound R es ds) (2 * N + 1)
      _ = ((N : ℝ) + 1)⁻¹ := by push_cast; field_simp; ring
  · exact uniform_mixed_bound hU he hval R hR

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

def Representable (f : SpaceTime → ℝ) : Prop := ∃ e : Expr, Valid e ∧ value e = f

attribute [fun_prop] Representable

namespace Representable

@[fun_prop] theorem rational (q : ℚ) : Representable (fun _ => (q : ℝ)) := by
  obtain ⟨r, hr⟩ := Qval_surjective q
  exact ⟨cst r, valid_cst r, by funext p; simp [hr]⟩

@[fun_prop] theorem nat (n : ℕ) : Representable (fun _ => (n : ℝ)) := by
  simpa using rational (n : ℚ)

@[fun_prop] theorem ofNat (n : ℕ) [n.AtLeastTwo] : Representable (fun _ => (ofNat(n) : ℝ)) := nat n

@[fun_prop] theorem zero : Representable (fun _ => (0 : ℝ)) := by simpa using nat 0
@[fun_prop] theorem one : Representable (fun _ => (1 : ℝ)) := by simpa using nat 1
@[fun_prop] theorem time : Representable (fun p : SpaceTime => p.1) :=
  ⟨.zero, trivial, rfl⟩
@[fun_prop] theorem space (j : Fin 3) : Representable (fun p : SpaceTime => p.2 j) :=
  ⟨varE (some j), valid_varE _, by funext p; simp⟩

@[fun_prop] theorem add {f g : SpaceTime → ℝ} (hf : Representable f) (hg : Representable g) :
    Representable (fun p => f p + g p) := by
  obtain ⟨e, he, rfl⟩ := hf
  obtain ⟨d, hd, rfl⟩ := hg
  exact ⟨.pair e d, ⟨he, hd⟩, rfl⟩

@[fun_prop] theorem mul {f g : SpaceTime → ℝ} (hf : Representable f) (hg : Representable g) :
    Representable (fun p => f p * g p) := by
  obtain ⟨e, he, rfl⟩ := hf
  obtain ⟨d, hd, rfl⟩ := hg
  exact ⟨.comp e d, ⟨he, hd⟩, rfl⟩

@[fun_prop] theorem neg {f : SpaceTime → ℝ} (hf : Representable f) :
    Representable (fun p => -f p) := by
  obtain ⟨e, he, rfl⟩ := hf
  exact ⟨.rfind' e, he, rfl⟩

@[fun_prop] theorem sub {f g : SpaceTime → ℝ} (hf : Representable f) (hg : Representable g) :
    Representable (fun p => f p - g p) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

@[fun_prop] theorem div_rat {f : SpaceTime → ℝ} (hf : Representable f) (q : ℚ) :
    Representable (fun p => f p / (q : ℝ)) := by
  simpa only [Rat.cast_inv, div_eq_mul_inv] using hf.mul (rational q⁻¹)

@[fun_prop] theorem div_nat {f : SpaceTime → ℝ} (hf : Representable f) (n : ℕ) :
    Representable (fun p => f p / (n : ℝ)) := by simpa using hf.div_rat (n : ℚ)

@[fun_prop] theorem div_ofNat {f : SpaceTime → ℝ} (hf : Representable f) (n : ℕ) [n.AtLeastTwo] :
    Representable (fun p => f p / (ofNat(n) : ℝ)) := hf.div_nat n

@[fun_prop] theorem flat {f : SpaceTime → ℝ} (hf : Representable f) (m : ℕ) :
    Representable (fun p => flatTerm m (f p)) := by
  obtain ⟨e, he, rfl⟩ := hf
  exact ⟨flatE m e, (valid_flatE _ _).2 he, by funext p; simp⟩

@[fun_prop] theorem glue {f : SpaceTime → ℝ} (hf : Representable f) :
    Representable (fun p => expNegInvGlue (f p)) := by
  simpa only [flatTerm, pow_zero, one_mul] using hf.flat 0

lemma exists_inv_nat_le {ε : ℝ} (hε : 0 < ε) : ∃ b : ℕ, ((b : ℝ) + 1)⁻¹ ≤ ε := by
  obtain ⟨b, hb⟩ := exists_nat_gt ε⁻¹
  refine ⟨b, (inv_le_iff_one_le_mul₀ (by positivity)).2 ?_⟩
  have h := mul_lt_mul_of_pos_left hb hε
  rw [mul_inv_cancel₀ (ne_of_gt hε)] at h
  nlinarith

theorem inv {f : SpaceTime → ℝ} (hf : Representable f)
    (hsep : ∃ ε : ℝ, 0 < ε ∧ ∀ p, ε ≤ |f p|) : Representable (fun p => (f p)⁻¹) := by
  obtain ⟨e, he, rfl⟩ := hf
  obtain ⟨ε, hε, hsep⟩ := hsep
  obtain ⟨b, hb⟩ := exists_inv_nat_le hε
  exact ⟨invE b e, (valid_invE _ _).2 ⟨he, fun p => hb.trans (hsep p)⟩,
    by funext p; simp⟩

theorem div {f g : SpaceTime → ℝ} (hf : Representable f) (hg : Representable g)
    (hsep : ∃ ε : ℝ, 0 < ε ∧ ∀ p, ε ≤ |g p|) : Representable (fun p => f p / g p) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hsep)

theorem transition_denom_lower (x : ℝ) :
    expNegInvGlue (1 / 2) ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  rcases le_total (1 / 2 : ℝ) x with hx | hx
  · exact (expNegInvGlue.monotone hx).trans (le_add_of_nonneg_right (expNegInvGlue.nonneg _))
  · have hy : (1 / 2 : ℝ) ≤ 1 - x := by linarith
    exact (expNegInvGlue.monotone hy).trans (le_add_of_nonneg_left (expNegInvGlue.nonneg _))

@[fun_prop] theorem transition {f : SpaceTime → ℝ} (hf : Representable f) :
    Representable (fun p => Real.smoothTransition (f p)) := by
  apply hf.glue.div (hf.glue.add ((one.sub hf).glue))
  refine ⟨expNegInvGlue (1 / 2), expNegInvGlue.pos_of_pos (by norm_num), fun p => ?_⟩
  rw [abs_of_nonneg (add_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _))]
  exact transition_denom_lower _

@[fun_prop] theorem directional {f : SpaceTime → ℝ} (hf : Representable f) (j : Axis) :
    Representable (fun p => fderiv ℝ f p (coordinateDirection j)) := by
  obtain ⟨e, he, rfl⟩ := hf
  exact ⟨diff j e, valid_diff he j, funext (value_diff he j)⟩

theorem smooth {f : SpaceTime → ℝ} (hf : Representable f) : ContDiff ℝ ∞ f := by
  obtain ⟨e, he, rfl⟩ := hf
  exact smooth_value he

@[fun_prop] theorem sum {ι : Type*} (s : Finset ι) {f : ι → SpaceTime → ℝ}
    (hf : ∀ i ∈ s, Representable (f i)) : Representable (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using zero
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

@[fun_prop] theorem prod {ι : Type*} (s : Finset ι) {f : ι → SpaceTime → ℝ}
    (hf : ∀ i ∈ s, Representable (f i)) : Representable (fun p => ∏ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end Representable

end BoxTransport.Routing.Computation

end

end OAI
