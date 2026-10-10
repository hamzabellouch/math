import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.NoncommRing

namespace OAI
namespace CuntzComparison

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

end CuntzComparison

end OAI
