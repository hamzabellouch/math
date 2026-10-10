import OAI.AlgebraicGeometry.AbhyankarSathaye.Identities
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI

/-!
# Polynomial maps and finitely presented quotients

Ring homomorphisms preserve the defining polynomial expressions. Algebra maps
annihilating two or three relations descend to the corresponding quotient.
-/

noncomputable section
namespace AbhyankarSathaye

section Maps
variable {B D H : Type*} [CommRing B] [CommRing D]
variable [FunLike H B D] [RingHomClass H B D]

@[simp] theorem map_S (f : H) (h u v w : B) :
    f (S h u v w) = S (f h) (f u) (f v) (f w) := by simp [S, map_ofNat]

@[simp] theorem map_P (f : H) (x y s : B) :
    f (P x y s) = P (f x) (f y) (f s) := by simp [P, map_ofNat]

@[simp] theorem map_Alpha (f : H) (x s : B) :
    f (Alpha x s) = Alpha (f x) (f s) := by simp [Alpha, map_ofNat]

@[simp] theorem map_Beta (f : H) (x y s : B) :
    f (Beta x y s) = Beta (f x) (f y) (f s) := by simp [Beta, map_ofNat]

end Maps

section Presentations
variable {B A D : Type*} [CommRing B] [CommRing A] [CommRing D]
variable [Algebra B A] [Algebra B D]

def lift_pair (a b : A) (f : A →ₐ[B] D) (ha : f a = 0) (hb : f b = 0) :
    (A ⧸ Ideal.span {a,b}) →ₐ[B] D := by
  have hi : Ideal.span {a,b} ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hb
  exact Ideal.Quotient.liftₐ _ f (fun z hz => hi hz)

@[simp] theorem lift_pair_mk (a b : A) (f : A →ₐ[B] D) (ha hb) (z : A) :
    lift_pair a b f ha hb (Ideal.Quotient.mk _ z) = f z := rfl

def lift_triple (a b c : A) (f : A →ₐ[B] D)
    (ha : f a = 0) (hb : f b = 0) (hc : f c = 0) :
    (A ⧸ Ideal.span {a,b,c}) →ₐ[B] D := by
  have hi : Ideal.span {a,b,c} ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  exact Ideal.Quotient.liftₐ _ f (fun z hz => hi hz)

@[simp] theorem lift_triple_mk (a b c : A) (f : A →ₐ[B] D) (ha hb hc) (z : A) :
    lift_triple a b c f ha hb hc (Ideal.Quotient.mk _ z) = f z := rfl

theorem quotient_pair_left (a b : A) : Ideal.Quotient.mk (Ideal.span {a,b}) a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem quotient_pair_right (a b : A) : Ideal.Quotient.mk (Ideal.span {a,b}) b = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem quotient_triple_first (a b c : A) :
    Ideal.Quotient.mk (Ideal.span {a,b,c}) a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem quotient_triple_second (a b c : A) :
    Ideal.Quotient.mk (Ideal.span {a,b,c}) b = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem quotient_triple_third (a b c : A) :
    Ideal.Quotient.mk (Ideal.span {a,b,c}) c = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

end Presentations
end AbhyankarSathaye

end

end OAI
