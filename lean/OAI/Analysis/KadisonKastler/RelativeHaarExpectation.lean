import OAI.Analysis.KadisonKastler.IndependenceMoments
import Mathlib.Algebra.Group.Conj

namespace OAI

/-! # Conjugating a free Haar model into relative free position

All expectation properties used here follow from its range and trace-pairing
identities. The finite-base construction supplies those identities later.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

/-- The centered part of a containing algebra for the finite base projection. -/
def relativeHaarKernel (E : B →ₗ[ℂ] B) (T : StarSubalgebra ℂ B) : Submodule ℂ B :=
  T.toSubmodule ⊓ LinearMap.ker E

@[simp]
theorem mem_relativeHaarKernel (E : B →ₗ[ℂ] B) (T : StarSubalgebra ℂ B) (x : B) :
    x ∈ relativeHaarKernel E T ↔ x ∈ T ∧ E x = 0 := Iff.rfl

/-- A trace projection is specified by precisely its range and pairing properties. -/
structure TraceBaseProjection (τ : FaithfulTracialState B) (D : StarSubalgebra ℂ B)
    (E : B →ₗ[ℂ] B) : Prop where
  mem : ∀ x, E x ∈ D
  pairing : ∀ b ∈ D, ∀ x, τ.toLinearMap (b * E x) = τ.toLinearMap (b * x)

namespace TraceBaseProjection

variable {τ : FaithfulTracialState B} {D T : StarSubalgebra ℂ B} {E : B →ₗ[ℂ] B}
    (hE : TraceBaseProjection τ D E)

include hE

theorem trace (x : B) : τ.toLinearMap (E x) = τ.toLinearMap x := by
  simpa only [one_mul] using hE.pairing 1 D.one_mem x

omit hE in
theorem eq_of_pairings {x y : B} (hx : x ∈ D) (hy : y ∈ D)
    (h : ∀ b ∈ D, τ.toLinearMap (b * x) = τ.toLinearMap (b * y)) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_mem_base_of_trace_pairings τ D (D.sub_mem hx hy)
  intro b hb
  rw [mul_sub, map_sub, h b hb, sub_self]

theorem fixed {x : B} (hx : x ∈ D) : E x = x :=
  eq_of_pairings (hE.mem x) hx (fun b hb => hE.pairing b hb x)

theorem left_mul {d : B} (hd : d ∈ D) (x : B) : E (d * x) = d * E x := by
  apply eq_of_pairings (hE.mem _) (D.mul_mem hd (hE.mem x))
  intro b hb
  rw [hE.pairing b hb]
  simpa only [mul_assoc] using (hE.pairing (b * d) (D.mul_mem hb hd) x).symm

theorem right_mul {d : B} (hd : d ∈ D) (x : B) : E (x * d) = E x * d := by
  apply eq_of_pairings (hE.mem _) (D.mul_mem (hE.mem x) hd)
  intro b hb
  rw [hE.pairing b hb]
  calc
    τ.toLinearMap (b * (x * d)) = τ.toLinearMap (d * (b * x)) := by
      rw [← mul_assoc, τ.tracial]
    _ = τ.toLinearMap ((d * b) * E x) := by
      rw [← mul_assoc, ← hE.pairing (d * b) (D.mul_mem hd hb)]
    _ = τ.toLinearMap (b * (E x * d)) := by
      rw [mul_assoc, τ.tracial d (b * E x), mul_assoc]

theorem kernel_trace {x : B} (hx : E x = 0) : τ.toLinearMap x = 0 := by
  rw [← hE.trace x, hx, map_zero]

theorem kernel_left_mul {d x : B} (hd : d ∈ D) (hx : E x = 0) : E (d * x) = 0 := by
  rw [hE.left_mul hd, hx, mul_zero]

theorem kernel_right_mul {d x : B} (hd : d ∈ D) (hx : E x = 0) : E (x * d) = 0 := by
  rw [hE.right_mul hd, hx, zero_mul]

/-- Conjugation by a unitary commuting with the base preserves its trace projection. -/
theorem conjugate (w : unitary B) (hw : ∀ d ∈ D, Commute (w : B) d) (x : B) :
    E ((w : B) * x * star (w : B)) = E x := by
  apply eq_of_pairings (hE.mem _) (hE.mem _)
  intro b hb
  rw [hE.pairing b hb, hE.pairing b hb]
  have he : star (w : B) * b * (w : B) = b := by
    calc
      _ = star (w : B) * (b * (w : B)) := mul_assoc _ _ _
      _ = star (w : B) * ((w : B) * b) := by rw [(hw b hb).eq]
      _ = b := by rw [← mul_assoc, w.property.1, one_mul]
  calc
    τ.toLinearMap (b * ((w : B) * x * star (w : B))) =
        τ.toLinearMap (star (w : B) * (b * (w : B) * x)) := by
      rw [← mul_assoc b, ← mul_assoc b, τ.tracial]
    _ = τ.toLinearMap (b * x) := by
      simpa only [mul_assoc] using congrArg (fun z => τ.toLinearMap (z * x)) he

end TraceBaseProjection

/-- Integer powers of a conjugated unitary telescope exactly. -/
theorem haarPower_unitary_conjugate (w s : unitary B) (k : ℤ) :
    haarPower (w * s * star w) k = (w : B) * haarPower s k * star (w : B) := by
  have h : (w * s * star w) ^ k = w * s ^ k * star w := by
    simpa only [Unitary.star_eq_inv] using (conj_zpow (i := k) (a := w) (b := s))
  exact congrArg (fun v : unitary B => (v : B)) h

/-- Traces are invariant under the same conjugation. -/
theorem trace_unitary_conjugate (τ : FaithfulTracialState B) (w : unitary B) (x : B) :
    τ.toLinearMap ((w : B) * x * star (w : B)) = τ.toLinearMap x := by
  rw [τ.tracial, ← mul_assoc, w.property.1, one_mul]

/-- In particular, conjugation retains the Haar moments. -/
theorem haar_moments_unitary_conjugate (τ : FaithfulTracialState B)
    (w s : unitary B)
    (hs : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower s k) = 0) :
    ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower (w * s * star w) k) = 0 := by
  intro k hk
  rw [haarPower_unitary_conjugate, trace_unitary_conjugate, hs k hk]

end

end KadisonKastler

end OAI
