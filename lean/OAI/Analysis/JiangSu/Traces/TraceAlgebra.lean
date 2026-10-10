import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

namespace UnitalTomsWinter

variable {A R ι : Type*} [Ring A] [StarRing A] [AddCommGroup R]

structure AlgebraicTrace (A R : Type*) [Ring A] [AddCommGroup R] where
  toAddMonoidHom : A →+ R
  cyclic : ∀ a b, toAddMonoidHom (a * b) = toAddMonoidHom (b * a)

instance : CoeFun (AlgebraicTrace A R) (fun _ => A → R) :=
  ⟨fun τ => τ.toAddMonoidHom⟩

theorem trace_compression (τ : AlgebraicTrace A R) (s : Finset ι)
    (x : ι → A) (e h b : A) (hh : h * h = e)
    (hframe : ∑ i ∈ s, star (x i) * e * x i = 1) :
    τ (∑ i ∈ s, h * x i * b * star (x i) * h) = τ b := by
  rw [map_sum]
  calc
    ∑ i ∈ s, τ.toAddMonoidHom (h * x i * b * star (x i) * h) =
        ∑ i ∈ s, τ.toAddMonoidHom (b * (star (x i) * e * x i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        τ.toAddMonoidHom (h * x i * b * star (x i) * h) =
            τ.toAddMonoidHom (x i * b * star (x i) * h * h) := by
          simpa only [mul_assoc] using τ.cyclic h (x i * b * star (x i) * h)
        _ = τ.toAddMonoidHom (x i * (b * star (x i) * e)) := by
          rw [mul_assoc, hh]; simp only [mul_assoc]
        _ = τ.toAddMonoidHom (b * (star (x i) * e * x i)) := by
          simpa only [mul_assoc] using τ.cyclic (x i) (b * star (x i) * e)
    _ = τ.toAddMonoidHom (b * ∑ i ∈ s, star (x i) * e * x i) := by
      rw [Finset.mul_sum, map_sum]
    _ = τ.toAddMonoidHom b := by rw [hframe, mul_one]

def cornerSymmetry (p q : A) : A := p + p - q

theorem cornerSymmetry_selfAdjoint {p q : A}
    (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) :
    IsSelfAdjoint (cornerSymmetry p q) := (hp.add hp).sub hq

omit [StarRing A] in
theorem cornerSymmetry_square {p q : A}
    (hp : p * p = p) (hq : q * q = q)
    (hpq : p * q = p) (hqp : q * p = p) :
    cornerSymmetry p q * cornerSymmetry p q = q := by
  simp only [cornerSymmetry, sub_mul, mul_sub, add_mul, mul_add, hp, hq, hpq, hqp]
  noncomm_ring

omit [StarRing A] in
theorem cornerSymmetry_supported {p q : A}
    (hq : q * q = q) (hpq : p * q = p) (hqp : q * p = p) :
    q * cornerSymmetry p q = cornerSymmetry p q ∧
      cornerSymmetry p q * q = cornerSymmetry p q := by
  simp only [cornerSymmetry, mul_sub, mul_add, sub_mul, add_mul, hq, hpq, hqp,
    and_self]

omit [StarRing A] in
theorem trace_cornerSymmetry (τ : AlgebraicTrace A R) {p q : A}
    (hhalf : τ p + τ p = τ q) : τ (cornerSymmetry p q) = 0 := by
  change τ.toAddMonoidHom (p + p - q) = 0
  rw [map_sub, map_add]
  exact sub_eq_zero.mpr hhalf

theorem normalized_isometry {h b x v : A}
    (hh : IsSelfAdjoint h) (hv : IsSelfAdjoint v)
    (hsq : h * h = b) (hnorm : v * (star x * b * x) * v = 1) :
    star (h * x * v) * (h * x * v) = 1 := by
  simp only [star_mul, hh.star_eq, hv.star_eq]
  calc
    v * (star x * h) * (h * x * v) = v * (star x * (h * h) * x) * v := by
      simp only [mul_assoc]
    _ = 1 := by rw [hsq, hnorm]

theorem isometry_range_projection {w : A} (hw : star w * w = 1) :
    IsSelfAdjoint (w * star w) ∧ (w * star w) * (w * star w) = w * star w := by
  constructor
  · simp [IsSelfAdjoint]
  · calc
      (w * star w) * (w * star w) = w * (star w * w) * star w := by
        simp only [mul_assoc]
      _ = w * star w := by rw [hw, mul_one]

end UnitalTomsWinter

open scoped ComplexOrder

namespace UnitalTomsWinter

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure TracialState extends A →ₚ[ℂ] ℂ where
  normalized : toPositiveLinearMap 1 = 1
  tracial : ∀ a b, toPositiveLinearMap (a * b) = toPositiveLinearMap (b * a)

variable {A}

namespace TracialState

noncomputable def algebraicTrace (τ : TracialState A) : AlgebraicTrace A ℂ where
  toAddMonoidHom := τ.toPositiveLinearMap.toLinearMap.toAddMonoidHom
  cyclic := τ.tracial

noncomputable def twoNorm (τ : TracialState A) (a : A) : ℝ :=
  ‖τ.toPositiveLinearMap.toPreGNS a‖

theorem twoNorm_eq (τ : TracialState A) (a : A) :
    τ.twoNorm a = Real.sqrt (τ.toPositiveLinearMap (star a * a)).re := by
  rfl

theorem twoNorm_nonneg (τ : TracialState A) (a : A) : 0 ≤ τ.twoNorm a := norm_nonneg _

@[simp] theorem twoNorm_zero (τ : TracialState A) : τ.twoNorm 0 = 0 := by
  simp [twoNorm]

@[simp] theorem twoNorm_one (τ : TracialState A) : τ.twoNorm 1 = 1 := by
  simp [twoNorm_eq, τ.normalized]

theorem twoNorm_add_le (τ : TracialState A) (a b : A) :
    τ.twoNorm (a + b) ≤ τ.twoNorm a + τ.twoNorm b := by
  simpa [twoNorm] using norm_add_le (τ.toPositiveLinearMap.toPreGNS a)
    (τ.toPositiveLinearMap.toPreGNS b)

theorem twoNorm_smul (τ : TracialState A) (z : ℂ) (a : A) :
    τ.twoNorm (z • a) = ‖z‖ * τ.twoNorm a := by
  simp [twoNorm, norm_smul]

@[simp] theorem twoNorm_star (τ : TracialState A) (a : A) :
    τ.twoNorm (star a) = τ.twoNorm a := by
  simp only [twoNorm_eq, star_star, τ.tracial a (star a)]

theorem twoNorm_mul_left (τ : TracialState A) (a b : A) :
    τ.twoNorm (a * b) ≤ ‖a‖ * τ.twoNorm b := by
  let f := τ.toPositiveLinearMap
  have hop : ‖f.leftMulMapPreGNS a‖ ≤ ‖a‖ := by
    unfold PositiveLinearMap.leftMulMapPreGNS
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  calc
    τ.twoNorm (a * b) = ‖f.leftMulMapPreGNS a (f.toPreGNS b)‖ := rfl
    _ ≤ ‖f.leftMulMapPreGNS a‖ * ‖f.toPreGNS b‖ :=
      (f.leftMulMapPreGNS a).le_opNorm _
    _ ≤ ‖a‖ * τ.twoNorm b := mul_le_mul_of_nonneg_right hop (norm_nonneg _)

theorem twoNorm_mul_right (τ : TracialState A) (a b : A) :
    τ.twoNorm (b * a) ≤ ‖a‖ * τ.twoNorm b := by
  calc
    τ.twoNorm (b * a) = τ.twoNorm (star a * star b) := by
      rw [← star_mul, twoNorm_star]
    _ ≤ ‖star a‖ * τ.twoNorm (star b) := τ.twoNorm_mul_left _ _
    _ = ‖a‖ * τ.twoNorm b := by rw [norm_star, twoNorm_star]

theorem twoNorm_le_norm (τ : TracialState A) (a : A) : τ.twoNorm a ≤ ‖a‖ := by
  simpa using τ.twoNorm_mul_left a 1

noncomputable def toPreGNSContinuous (τ : TracialState A) :
    A →L[ℂ] τ.toPositiveLinearMap.PreGNS :=
  τ.toPositiveLinearMap.toPreGNS.toLinearMap.mkContinuous 1
    (fun a => by simpa [twoNorm] using τ.twoNorm_le_norm a)

theorem continuous_twoNorm (τ : TracialState A) : Continuous τ.twoNorm :=
  τ.toPreGNSContinuous.continuous.norm

end TracialState
end UnitalTomsWinter

end OAI
