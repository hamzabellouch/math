import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.TaylorDescent

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift
universe u
variable {K A α : Type u} [CommRing K] [CommRing A]
  [Algebra K A] [Algebra (MvPolynomial α K) A]
  [IsScalarTower K (MvPolynomial α K) A]
  [IsNoetherianRing A] [Finite α]
  [Algebra.FormallySmooth (MvPolynomial α K) A]

lemma fullTaylor_comp_of (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) :
    (fullTaylor (K := K) (α := α) I J q hq).comp
        (algebraMap A (AdicCompletion J A)) =
      (TaylorTarget.map (TaylorTarget.quotientCoefficient (S := AdicCompletion J A) I) q).comp
        (taylor (K := K) (α := α) I q hq) := by
  ext a
  exact fullTaylor_of I J q hq a

omit [IsNoetherianRing A] [Finite α] in
lemma coefficient_comp_of (I J : Ideal A) (q : ℕ) :
    (algebraMap (AdicCompletion J A)
        (TaylorTarget.Ring ((AdicCompletion J A) ⧸ I.map (algebraMap A (AdicCompletion J A))) α q)).comp
        (algebraMap A (AdicCompletion J A)) =
      (TaylorTarget.map (TaylorTarget.quotientCoefficient (S := AdicCompletion J A) I) q).comp
        (coefficient (α := α) I q) := by
  ext a
  change TaylorTarget.mk _ α q (MvPolynomial.C _) =
    TaylorTarget.map _ q (TaylorTarget.mk _ α q (MvPolynomial.C _))
  rw [TaylorTarget.map_mk,MvPolynomial.map_C]
  rfl

theorem fullTaylor_mem_pow (I J : Ideal A) (q : ℕ) (hq : 1 ≤ q) (N : ℕ)
    (b : AdicCompletion J A)
    (hb : b ∈ (J.map (algebraMap A (AdicCompletion J A))) ^ (N+q-1)) :
    fullTaylor (K := K) (α := α) I J q hq b ∈
      ((J.map (algebraMap A (AdicCompletion J A))).map
        (algebraMap (AdicCompletion J A)
          (TaylorTarget.Ring ((AdicCompletion J A) ⧸ I.map (algebraMap A (AdicCompletion J A))) α q))) ^ N := by
  have hh := Ideal.mem_map_of_mem (fullTaylor (K := K) (α := α) I J q hq) hb
  rw [Ideal.map_pow,Ideal.map_map,fullTaylor_comp_of,← Ideal.map_map,← Ideal.map_pow] at hh
  have hle := Ideal.map_mono (f := TaylorTarget.map
    (TaylorTarget.quotientCoefficient (S := AdicCompletion J A) I) q)
      (actions_cofinal (K := K) (α := α) I J q hq N).1
  have ht := hle hh
  rwa [Ideal.map_pow,Ideal.map_map,← coefficient_comp_of,← Ideal.map_map] at ht

end BoundaryOnly.FormalObstruction.AlgebraicReplacement.TaylorShift

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

theorem derivation_mem_pow (D : Derivation k A A) (I : Ideal A) (q : ℕ)
    {f : A} (hf : f ∈ I^(q+1)) : D f ∈ I^q := by
  induction q generalizing f with
  | zero => simp
  | succ q ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
      apply (I^(q+1)).add_mem
      · exact Ideal.mul_mem_right _ _ ha
      · rw [pow_succ]
        simpa only [mul_comm] using Ideal.mul_mem_mul (ih ha) hb
    · intro a b ha hb
      simpa only [map_add] using (I^(q+1)).add_mem ha hb

theorem ninth_order_bounds (L r m : Ideal A) (hL : L ≤ m) (hcube : L^3 ≤ r) :
    L^9 ≤ r^3 ∧ L^8 ≤ r^2 * m^2 := by
  constructor
  · calc
      L^9 = (L^3)^3 := by rw [← pow_mul]
      _ ≤ r^3 := pow_le_pow_left' hcube 3
  · calc
      L^8 = (L^3)^2 * L^2 := by rw [← pow_mul, ← pow_add]
      _ ≤ r^2 * m^2 := mul_le_mul' (pow_le_pow_left' hcube 2) (pow_le_pow_left' hL 2)

theorem eighth_le_mul (r m : Ideal A) : r^2 * m^2 ≤ m * r := by
  calc
    r^2 * m^2 ≤ r * m := mul_le_mul' (Ideal.pow_le_self (by omega)) (Ideal.pow_le_self (by omega))
    _ = m * r := mul_comm _ _

theorem span_eq_of_generator_congruence {ι : Type*} [Fintype ι]
    (m : Ideal A) (hm : m ≤ Ideal.jacobson ⊥) (v w : ι → A)
    (h : ∀ i, w i - v i ∈ m * Ideal.span (Set.range v)) :
    Ideal.span (Set.range w) = Ideal.span (Set.range v) := by
  let r := Ideal.span (Set.range v)
  let s := Ideal.span (Set.range w)
  have hmr : m * r ≤ r := Ideal.mul_le_right
  have hs : s ≤ r := Ideal.span_le.mpr (by
    rintro _ ⟨i,rfl⟩
    have he : w i = (w i - v i) + v i := by ring
    rw [he]
    exact r.add_mem (hmr (h i)) (Ideal.subset_span ⟨i,rfl⟩))
  have hr : r ≤ s ⊔ m • r := Ideal.span_le.mpr (by
    rintro _ ⟨i,rfl⟩
    have hw : w i ∈ s ⊔ m • r := (show s ≤ s ⊔ m • r from le_sup_left) (Ideal.subset_span ⟨i,rfl⟩)
    have hd : w i - v i ∈ s ⊔ m • r := (show m * r ≤ s ⊔ m • r from le_sup_right) (h i)
    exact sub_sub_cancel (w i) (v i) ▸ (s ⊔ m • r).sub_mem hw hd)
  exact le_antisymm hs (Submodule.le_of_le_smul_of_le_jacobson_bot
    (Submodule.fg_span (Set.finite_range v)) hm hr)

end BoundaryOnly.FormalObstruction.AlgebraicReplacement

end

end OAI
