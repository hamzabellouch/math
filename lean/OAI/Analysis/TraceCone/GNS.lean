import OAI.Analysis.TraceCone.FiniteIdeal
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The GNS representation of an extended trace

The square-integrable ideal carries the seminorm obtained by polarization of
`x ↦ τ (star x * x)`. Its Hilbert space completion supports bounded left
multiplication by the algebra.

This is the trace representation used in the paper
*The trace cone classifies Razak–Jacelon stabilizations*.
-/

noncomputable section

open Filter Topology
open scoped NNReal ENNReal

namespace TraceConeClassification
namespace ExtendedTrace
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Left multiplication preserves the actual square-integrable trace ideal. -/
def finiteSquareLeftMul (τ : ExtendedTrace A) (a : A)
    (x : τ.finiteSquareAlgebra) : τ.finiteSquareAlgebra :=
  ⟨a * x.1, τ.mul_mem_finiteSquareSet_left a x.2⟩


variable (τ : ExtendedTrace A)

@[simp] lemma traceSquare_ne_top (x : τ.finiteSquareAlgebra) :
    τ.toFun (Positive.starMul x.1) ≠ ∞ := ne_of_lt x.2

def squareValue (x : τ.finiteSquareAlgebra) : ℝ :=
  (τ (Positive.starMul x.1)).toReal

lemma squareValue_nonneg (x : τ.finiteSquareAlgebra) : 0 ≤ τ.squareValue x :=
  ENNReal.toReal_nonneg

@[simp] lemma squareValue_zero : τ.squareValue 0 = 0 := by
  simp [squareValue, Positive.starMul, show (⟨0, le_rfl⟩ : Positive A) = Positive.zero from rfl,
    τ.map_zero]

lemma squareValue_smul (c : ℂ) (x : τ.finiteSquareAlgebra) :
    τ.squareValue (c • x) = Complex.normSq c * τ.squareValue x := by
  let r : ℝ≥0 := ⟨Complex.normSq c, Complex.normSq_nonneg c⟩
  have heq : Positive.starMul ((c • x : τ.finiteSquareAlgebra).1) =
      Positive.scale r (Positive.starMul x.1) := by
    apply Subtype.ext
    dsimp [Positive.starMul, Positive.scale, r]
    simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    change (c * star c) • (star x.1 * x.1) = (Complex.normSq c : ℝ) • (star x.1 * x.1)
    rw [mul_comm c (star c)]
    change ((starRingEnd ℂ) c * c) • (star x.1 * x.1) = _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.coe_smul]
  change (τ (Positive.starMul (c • x : τ.finiteSquareAlgebra).1)).toReal = _
  rw [heq, τ.map_scale_all, ENNReal.toReal_mul, ENNReal.coe_toReal]
  rfl

lemma squareValue_real_smul (r : ℝ) (x : τ.finiteSquareAlgebra) :
    τ.squareValue (r • x) = r * r * τ.squareValue x := by
  rw [← Complex.coe_smul, τ.squareValue_smul]
  simp [Complex.normSq_ofReal]

lemma squareValue_three (x y z : τ.finiteSquareAlgebra) :
    τ.squareValue (x + y + z) + (τ.squareValue x + τ.squareValue y + τ.squareValue z) =
      τ.squareValue (x + y) + τ.squareValue (y + z) + τ.squareValue (z + x) := by
  have hs : Positive.add (Positive.starMul (x + y + z : τ.finiteSquareAlgebra).1)
        (Positive.add (Positive.add (Positive.starMul x.1) (Positive.starMul y.1))
          (Positive.starMul z.1)) =
      Positive.add (Positive.add (Positive.starMul (x + y : τ.finiteSquareAlgebra).1)
        (Positive.starMul (y + z : τ.finiteSquareAlgebra).1))
          (Positive.starMul (z + x : τ.finiteSquareAlgebra).1) := by
    apply Subtype.ext
    dsimp [Positive.add, Positive.starMul]
    simp only [star_add, add_mul, mul_add]
    abel
  have ht := congrArg (fun a => (τ a).toReal) hs
  simp only [τ.map_add] at ht
  have hx := τ.traceSquare_ne_top x
  have hy := τ.traceSquare_ne_top y
  have hz := τ.traceSquare_ne_top z
  have hxy := τ.traceSquare_ne_top (x+y)
  have hyz := τ.traceSquare_ne_top (y+z)
  have hzx := τ.traceSquare_ne_top (z+x)
  rw [ENNReal.toReal_add (τ.traceSquare_ne_top (x+y+z))
      (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hx, hy⟩, hz⟩),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hx, hy⟩) hz,
    ENNReal.toReal_add hx hy,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hxy, hyz⟩) hzx,
    ENNReal.toReal_add hxy hyz] at ht
  exact ht

lemma squareValue_polar_real_nonneg (r : ℝ) (hr : 0 ≤ r)
    (x y : τ.finiteSquareAlgebra) :
    QuadraticMap.polar τ.squareValue (r • x) y = r * QuadraticMap.polar τ.squareValue x y := by
  let rp : ℝ≥0 := ⟨r, hr⟩
  have hs : Positive.add (Positive.starMul (r • x + y : τ.finiteSquareAlgebra).1)
      (Positive.scale rp (Positive.add (Positive.starMul x.1) (Positive.starMul y.1))) =
    Positive.add (Positive.scale rp (Positive.starMul (x + y : τ.finiteSquareAlgebra).1))
      (Positive.add (Positive.starMul (r • x : τ.finiteSquareAlgebra).1)
        (Positive.starMul y.1)) := by
    apply Subtype.ext
    change star (r • x.1 + y.1) * (r • x.1 + y.1) +
      r • (star x.1 * x.1 + star y.1 * y.1) =
      r • (star (x.1 + y.1) * (x.1 + y.1)) +
        (star (r • x.1) * (r • x.1) + star y.1 * y.1)
    simp only [star_add, star_smul, star_trivial, add_mul, mul_add, smul_add,
      smul_mul_assoc, mul_smul_comm, smul_smul]
    module
  have ht := congrArg (fun a => (τ a).toReal) hs
  simp only [τ.map_add, τ.map_scale_all] at ht
  have hx := τ.traceSquare_ne_top x
  have hy := τ.traceSquare_ne_top y
  have hrx := τ.traceSquare_ne_top (r • x)
  have hrxy := τ.traceSquare_ne_top (r • x + y)
  have hxy := τ.traceSquare_ne_top (x + y)
  have hmul {v : ℝ≥0∞} (hv : v ≠ ∞) : (rp : ℝ≥0∞) * v ≠ ∞ :=
    ne_of_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_top_iff_ne_top.mpr hv))
  rw [ENNReal.toReal_add hrxy (hmul (ENNReal.add_ne_top.mpr ⟨hx,hy⟩)),
    ENNReal.toReal_add (hmul hxy) (ENNReal.add_ne_top.mpr ⟨hrx,hy⟩),
    ENNReal.toReal_add hrx hy, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add hx hy, ENNReal.coe_toReal] at ht
  change τ.squareValue (r • x + y) + r * (τ.squareValue x + τ.squareValue y) =
    r * τ.squareValue (x + y) + (τ.squareValue (r • x) + τ.squareValue y) at ht
  dsimp [QuadraticMap.polar]
  linarith

lemma squareValue_polar_add (x y z : τ.finiteSquareAlgebra) :
    QuadraticMap.polar τ.squareValue (x + y) z =
      QuadraticMap.polar τ.squareValue x z + QuadraticMap.polar τ.squareValue y z :=
  QuadraticMap.polar_add_left_iff.mpr (τ.squareValue_three x y z)

lemma squareValue_polar_zero (y : τ.finiteSquareAlgebra) :
    QuadraticMap.polar τ.squareValue 0 y = 0 := by
  simp [QuadraticMap.polar]

lemma squareValue_polar_neg (x y : τ.finiteSquareAlgebra) :
    QuadraticMap.polar τ.squareValue (-x) y = -QuadraticMap.polar τ.squareValue x y := by
  have h := τ.squareValue_polar_add (-x) x y
  rw [neg_add_cancel, τ.squareValue_polar_zero] at h
  linarith

lemma squareValue_polar_real (r : ℝ) (x y : τ.finiteSquareAlgebra) :
    QuadraticMap.polar τ.squareValue (r • x) y = r • QuadraticMap.polar τ.squareValue x y := by
  by_cases hr : 0 ≤ r
  · exact τ.squareValue_polar_real_nonneg r hr x y
  · have hp := τ.squareValue_polar_real_nonneg (-r) (le_of_lt (neg_pos.mpr (lt_of_not_ge hr))) x y
    rw [neg_smul, τ.squareValue_polar_neg] at hp
    simpa using congrArg Neg.neg hp

/-- The real quadratic form x ↦ τ(x*x), with finite values on n_τ. -/
def quadraticForm : QuadraticForm ℝ τ.finiteSquareAlgebra :=
  QuadraticMap.ofPolar τ.squareValue τ.squareValue_real_smul
    τ.squareValue_polar_add τ.squareValue_polar_real

/-- Real polarization; its bilinearity follows from the trace identities above. -/
def realInner : τ.finiteSquareAlgebra →ₗ[ℝ] τ.finiteSquareAlgebra →ₗ[ℝ] ℝ :=
  (2⁻¹ : ℝ) • τ.quadraticForm.polarBilin

lemma realInner_eq (x y : τ.finiteSquareAlgebra) :
    τ.realInner x y = (τ.squareValue (x + y) - τ.squareValue x - τ.squareValue y) / 2 := by
  change (2⁻¹ : ℝ) * (τ.squareValue (x+y) - τ.squareValue x - τ.squareValue y) = _
  ring

lemma realInner_self (x : τ.finiteSquareAlgebra) :
    τ.realInner x x = τ.squareValue x := by
  rw [τ.realInner_eq, ← two_smul ℝ x, τ.squareValue_real_smul]
  ring

lemma realInner_symm (x y : τ.finiteSquareAlgebra) : τ.realInner x y = τ.realInner y x := by
  rw [τ.realInner_eq, τ.realInner_eq, add_comm x y]
  ring

@[simp] lemma squareValue_I (x : τ.finiteSquareAlgebra) :
    τ.squareValue (Complex.I • x) = τ.squareValue x := by
  rw [τ.squareValue_smul]
  simp

lemma realInner_I_I (x y : τ.finiteSquareAlgebra) :
    τ.realInner (Complex.I • x) (Complex.I • y) = τ.realInner x y := by
  rw [τ.realInner_eq, ← smul_add, τ.squareValue_I, τ.squareValue_I,
    τ.squareValue_I, τ.realInner_eq]

lemma realInner_I_left (x y : τ.finiteSquareAlgebra) :
    τ.realInner (Complex.I • x) y = -τ.realInner x (Complex.I • y) := by
  have h := τ.realInner_I_I x (Complex.I • y)
  simpa only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, neg_neg] using congrArg Neg.neg h

lemma realInner_I_self (x : τ.finiteSquareAlgebra) :
    τ.realInner (Complex.I • x) x = 0 := by
  have h := τ.realInner_I_left x x
  rw [← τ.realInner_symm (Complex.I • x) x] at h
  linarith

lemma complex_smul_parts (c : ℂ) (x : τ.finiteSquareAlgebra) :
    c • x = c.re • x + c.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

/-- Polarization of τ(x*x), with the standard conjugate-linear first convention. -/
def complexInner (x y : τ.finiteSquareAlgebra) : ℂ :=
  (τ.realInner x y : ℂ) + Complex.I * (τ.realInner (Complex.I • x) y : ℂ)

lemma complexInner_symm (x y : τ.finiteSquareAlgebra) :
    star (τ.complexInner y x) = τ.complexInner x y := by
  apply Complex.ext <;> simp [complexInner, Complex.mul_re, Complex.mul_im,
    τ.realInner_symm y x, τ.realInner_symm (Complex.I • y) x, τ.realInner_I_left]

lemma complexInner_self (x : τ.finiteSquareAlgebra) :
    τ.complexInner x x = (τ.squareValue x : ℂ) := by
  simp [complexInner, τ.realInner_self, τ.realInner_I_self]

lemma complexInner_add_left (x y z : τ.finiteSquareAlgebra) :
    τ.complexInner (x+y) z = τ.complexInner x z + τ.complexInner y z := by
  unfold complexInner
  rw [smul_add, _root_.map_add τ.realInner x y, _root_.map_add τ.realInner (Complex.I • x) (Complex.I • y)]
  simp only [LinearMap.add_apply, Complex.ofReal_add]
  ring

lemma complexInner_smul_left (x y : τ.finiteSquareAlgebra) (c : ℂ) :
    τ.complexInner (c • x) y = star c * τ.complexInner x y := by
  have hi : Complex.I • (c • x) = c.re • (Complex.I • x) - c.im • x := by
    rw [τ.complex_smul_parts c x, smul_add, smul_comm Complex.I c.re,
      smul_comm Complex.I c.im, smul_smul, Complex.I_mul_I, neg_one_smul,
      smul_neg, sub_eq_add_neg]
  rw [complexInner, hi, τ.complex_smul_parts c x]
  rw [_root_.map_add, map_sub,
    map_smul τ.realInner c.re x, map_smul τ.realInner c.im (Complex.I • x),
    map_smul τ.realInner c.re (Complex.I • x), map_smul τ.realInner c.im x]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp [complexInner, Complex.mul_re, Complex.mul_im]
  ring

/-- Type synonym with the L² seminorm, not the original C*-norm. -/
def PreTraceGNS (τ : ExtendedTrace A) : Type u := τ.finiteSquareAlgebra

instance : AddCommGroup τ.PreTraceGNS := inferInstanceAs (AddCommGroup τ.finiteSquareAlgebra)
instance : Module ℂ τ.PreTraceGNS := inferInstanceAs (Module ℂ τ.finiteSquareAlgebra)

def toPreTraceGNS : τ.finiteSquareAlgebra ≃ₗ[ℂ] τ.PreTraceGNS := LinearEquiv.refl _ _
def ofPreTraceGNS : τ.PreTraceGNS ≃ₗ[ℂ] τ.finiteSquareAlgebra := τ.toPreTraceGNS.symm

@[instance_reducible]
def preTraceInnerCore : PreInnerProductSpace.Core ℂ τ.PreTraceGNS where
  inner x y := τ.complexInner (τ.ofPreTraceGNS x) (τ.ofPreTraceGNS y)
  conj_inner_symm x y := τ.complexInner_symm _ _
  re_inner_nonneg x := by
    rw [τ.complexInner_self]
    exact τ.squareValue_nonneg _
  add_left x y z := τ.complexInner_add_left _ _ _
  smul_left x y c := τ.complexInner_smul_left _ _ _

instance : SeminormedAddCommGroup τ.PreTraceGNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := τ.preTraceInnerCore)
instance : InnerProductSpace ℂ τ.PreTraceGNS := InnerProductSpace.ofCore τ.preTraceInnerCore

open scoped InnerProductSpace

lemma preTraceGNS_inner (x y : τ.PreTraceGNS) :
    ⟪x,y⟫_ℂ = τ.complexInner (τ.ofPreTraceGNS x) (τ.ofPreTraceGNS y) := rfl

lemma preTraceGNS_norm_sq (x : τ.PreTraceGNS) :
    ‖x‖ ^ 2 = τ.squareValue (τ.ofPreTraceGNS x) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), τ.preTraceGNS_inner, τ.complexInner_self]
  rfl

abbrev TraceGNS := UniformSpace.Completion τ.PreTraceGNS

@[simp] lemma finiteSquareLeftMul_val (a : A) (x : τ.finiteSquareAlgebra) :
    (τ.finiteSquareLeftMul a x).1 = a * x.1 := rfl

def finiteSquareLeftMulLinear (a : A) : τ.finiteSquareAlgebra →ₗ[ℂ] τ.finiteSquareAlgebra where
  toFun := τ.finiteSquareLeftMul a
  map_add' x y := by apply Subtype.ext; simp [finiteSquareLeftMul, mul_add]
  map_smul' c x := by apply Subtype.ext; simp [finiteSquareLeftMul, mul_smul_comm]

lemma leftMul_squareValue_le (a : A) (x : τ.finiteSquareAlgebra) :
    τ.squareValue (τ.finiteSquareLeftMul a x) ≤ ‖a‖ ^ 2 * τ.squareValue x := by
  have hb : star (a * x.1) * (a * x.1) ≤ ‖star a * a‖ • (star x.1 * x.1) := by
    simpa only [star_mul, mul_assoc] using
      (CStarAlgebra.star_left_conjugate_le_norm_smul (a := x.1) (b := star a * a))
  have ht : τ (Positive.starMul (a * x.1)) ≤
      τ (Positive.scale ‖star a * a‖₊ (Positive.starMul x.1)) := τ.monotone hb
  rw [τ.map_scale_all] at ht
  have hh := ENNReal.toReal_mono
    (ne_of_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top x.2)) ht
  simpa only [squareValue, finiteSquareLeftMul_val, ENNReal.toReal_mul,
    ENNReal.coe_toReal, coe_nnnorm, CStarRing.norm_star_mul_self, ← sq] using hh

lemma leftMul_realInner (a : A) (x y : τ.finiteSquareAlgebra) :
    τ.realInner (τ.finiteSquareLeftMul a x) y =
      τ.realInner x (τ.finiteSquareLeftMul (star a) y) := by
  let ax := τ.finiteSquareLeftMul a x
  let ay := τ.finiteSquareLeftMul (star a) y
  have hs : Positive.add (Positive.starMul (ax+y).1)
      (Positive.add (Positive.starMul x.1) (Positive.starMul ay.1)) =
    Positive.add (Positive.starMul (x+ay).1)
      (Positive.add (Positive.starMul ax.1) (Positive.starMul y.1)) := by
    apply Subtype.ext
    change star (a*x.1+y.1)*(a*x.1+y.1) +
      (star x.1*x.1+star (star a*y.1)*(star a*y.1)) =
      star (x.1+star a*y.1)*(x.1+star a*y.1) +
        (star (a*x.1)*(a*x.1)+star y.1*y.1)
    simp only [star_add, star_mul, star_star]
    noncomm_ring
  have ht := congrArg (fun p => (τ p).toReal) hs
  simp only [τ.map_add] at ht
  rw [ENNReal.toReal_add (τ.traceSquare_ne_top (ax+y))
      (ENNReal.add_ne_top.mpr ⟨τ.traceSquare_ne_top x,τ.traceSquare_ne_top ay⟩),
    ENNReal.toReal_add (τ.traceSquare_ne_top x) (τ.traceSquare_ne_top ay),
    ENNReal.toReal_add (τ.traceSquare_ne_top (x+ay))
      (ENNReal.add_ne_top.mpr ⟨τ.traceSquare_ne_top ax,τ.traceSquare_ne_top y⟩),
    ENNReal.toReal_add (τ.traceSquare_ne_top ax) (τ.traceSquare_ne_top y)] at ht
  change τ.squareValue (ax+y) + (τ.squareValue x+τ.squareValue ay) =
    τ.squareValue (x+ay) + (τ.squareValue ax+τ.squareValue y) at ht
  rw [τ.realInner_eq, τ.realInner_eq]
  change (τ.squareValue (ax+y)-τ.squareValue ax-τ.squareValue y)/2 =
    (τ.squareValue (x+ay)-τ.squareValue x-τ.squareValue ay)/2
  linarith

lemma leftMul_complexInner (a : A) (x y : τ.finiteSquareAlgebra) :
    τ.complexInner (τ.finiteSquareLeftMul a x) y =
      τ.complexInner x (τ.finiteSquareLeftMul (star a) y) := by
  have hi : Complex.I • τ.finiteSquareLeftMul a x =
      τ.finiteSquareLeftMul a (Complex.I • x) := by
    apply Subtype.ext
    simp [finiteSquareLeftMul, mul_smul_comm]
  simp only [complexInner, hi, τ.leftMul_realInner]

/-- Bounded left multiplication with the L² norm, proved from positivity. -/
def leftMulPreTrace (a : A) : τ.PreTraceGNS →L[ℂ] τ.PreTraceGNS :=
  (τ.toPreTraceGNS.toLinearMap ∘ₗ τ.finiteSquareLeftMulLinear a ∘ₗ
    τ.ofPreTraceGNS.toLinearMap).mkContinuous ‖a‖ fun x => by
      rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow,
        τ.preTraceGNS_norm_sq, τ.preTraceGNS_norm_sq]
      exact τ.leftMul_squareValue_le a (τ.ofPreTraceGNS x)

@[simp] lemma leftMulPreTrace_apply (a : A) (x : τ.PreTraceGNS) :
    τ.leftMulPreTrace a x = τ.toPreTraceGNS (τ.finiteSquareLeftMul a (τ.ofPreTraceGNS x)) := rfl

@[simp] lemma leftMulPreTrace_mul (a b : A) :
    τ.leftMulPreTrace (a*b) = τ.leftMulPreTrace a ∘L τ.leftMulPreTrace b := by
  apply ContinuousLinearMap.ext
  intro x
  apply τ.ofPreTraceGNS.injective
  apply Subtype.ext
  exact mul_assoc a b (τ.ofPreTraceGNS x).1

lemma leftMulPreTrace_inner (a : A) (x y : τ.PreTraceGNS) :
    ⟪τ.leftMulPreTrace a x,y⟫_ℂ = ⟪x,τ.leftMulPreTrace (star a) y⟫_ℂ :=
  τ.leftMul_complexInner a (τ.ofPreTraceGNS x) (τ.ofPreTraceGNS y)

open UniformSpace Completion ContinuousLinearMap

def traceGNSRep : A →⋆ₙₐ[ℂ] (τ.TraceGNS →L[ℂ] τ.TraceGNS) where
  toFun a := (τ.leftMulPreTrace a).completion
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      change (τ.leftMulPreTrace 0).completion (x : τ.TraceGNS) = 0
      have h : τ.leftMulPreTrace 0 x = 0 := by
        apply τ.ofPreTraceGNS.injective
        apply Subtype.ext
        exact zero_mul _
      simpa [Completion.coe_zero, Completion.coe_add, Completion.coe_smul] using
        congrArg (fun v : τ.PreTraceGNS => (v : τ.TraceGNS)) h
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      have h : τ.leftMulPreTrace (a+b) x = τ.leftMulPreTrace a x + τ.leftMulPreTrace b x := by
        apply τ.ofPreTraceGNS.injective
        apply Subtype.ext
        exact add_mul _ _ _
      simpa [Completion.coe_zero, Completion.coe_add, Completion.coe_smul] using
        congrArg (fun v : τ.PreTraceGNS => (v : τ.TraceGNS)) h
  map_smul' c a := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using induction_on with
    | hp =>
      exact isClosed_eq (τ.leftMulPreTrace (c • a)).completion.continuous
        (c • (τ.leftMulPreTrace a).completion).continuous
    | ih x =>
      have h : τ.leftMulPreTrace (c • a) x = c • τ.leftMulPreTrace a x := by
        apply τ.ofPreTraceGNS.injective
        apply Subtype.ext
        exact smul_mul_assoc _ _ _
      simpa [Completion.coe_zero, Completion.coe_add, Completion.coe_smul] using
        congrArg (fun v : τ.PreTraceGNS => (v : τ.TraceGNS)) h
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    induction x using induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp
  map_star' a := by
    apply (eq_adjoint_iff _ _).mpr
    intro x y
    induction x, y using induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x y => simpa using τ.leftMulPreTrace_inner (star a) x y

def traceGNSLambda : τ.finiteSquareAlgebra →ₗ[ℂ] τ.TraceGNS where
  toFun x := (τ.toPreTraceGNS x : τ.TraceGNS)
  map_add' x y := by
    rw [_root_.map_add]
    exact Completion.coe_add _ _
  map_smul' c x := by simp

lemma traceGNSLambda_dense : DenseRange τ.traceGNSLambda := by
  have hr : Set.range τ.traceGNSLambda =
      Set.range (fun x : τ.PreTraceGNS => (x : τ.TraceGNS)) := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨τ.toPreTraceGNS x,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨τ.ofPreTraceGNS x,rfl⟩
  rw [DenseRange,hr]
  exact Completion.denseRange_coe

lemma traceGNSLambda_norm_sq (x : τ.finiteSquareAlgebra) :
    ‖τ.traceGNSLambda x‖ ^ 2 = (τ (Positive.starMul x.1)).toReal := by
  change ‖(τ.toPreTraceGNS x : τ.TraceGNS)‖ ^ 2 = _
  rw [Completion.norm_coe, τ.preTraceGNS_norm_sq]
  rfl

lemma traceGNSRep_covariance (a : A) (x : τ.finiteSquareAlgebra) :
    τ.traceGNSRep a (τ.traceGNSLambda x) = τ.traceGNSLambda (τ.finiteSquareLeftMul a x) := by
  change (τ.leftMulPreTrace a).completion (τ.toPreTraceGNS x : τ.TraceGNS) = _
  rw [ContinuousLinearMap.completion_apply_coe]
  rfl

theorem trace_gns_exists (τ : ExtendedTrace A) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
      (Λ : τ.finiteSquareAlgebra →ₗ[ℂ] H),
      DenseRange Λ ∧
      (∀ x, ‖Λ x‖ ^ 2 = (τ (Positive.starMul x.1)).toReal) ∧
      (∀ a x, π a (Λ x) = Λ (τ.finiteSquareLeftMul a x)) :=
  ⟨τ.TraceGNS, inferInstance, inferInstance, inferInstance, τ.traceGNSRep,
    τ.traceGNSLambda, τ.traceGNSLambda_dense, τ.traceGNSLambda_norm_sq,
    τ.traceGNSRep_covariance⟩

end ExtendedTrace
end TraceConeClassification

end

end OAI
