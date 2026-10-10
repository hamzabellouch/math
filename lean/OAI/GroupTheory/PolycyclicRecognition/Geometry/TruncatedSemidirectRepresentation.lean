import OAI.GroupTheory.PolycyclicRecognition.Algebra.TruncatedEnvelopingDerivation
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Lie.SemiDirect

namespace OAI

/-! # Representing a semidirect extension on the truncated enveloping algebra -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "Q" => TruncatedEnvelopingAlgebra R L

def truncatedLeftRepresentation (c : ℕ) : L →ₗ⁅R⁆ Module.End R (Q c) :=
  (Algebra.lmul R (Q c)).toLieHom.comp (truncatedEnvelopingGenerator c)

@[simp]
theorem truncatedLeftRepresentation_apply (c : ℕ) (x : L) (u : Q c) :
    truncatedLeftRepresentation (R := R) c x u = truncatedEnvelopingGenerator c x * u := rfl

theorem truncated_derivation_left_commutator (c : ℕ) (D : LieDerivation R L L) (x : L) :
    ⁅truncatedEnvelopingDerivation c D, truncatedLeftRepresentation (R := R) c x⁆ =
      truncatedLeftRepresentation (R := R) c (D x) := by
  ext u
  change truncatedEnvelopingDerivation c D (truncatedEnvelopingGenerator c x * u) -
    truncatedEnvelopingGenerator c x * truncatedEnvelopingDerivation c D u = _
  rw [truncatedEnvelopingDerivation_mul, truncatedEnvelopingDerivation_generator]
  simp

theorem truncated_left_derivation_commutator (c : ℕ) (D : LieDerivation R L L) (x : L) :
    ⁅truncatedLeftRepresentation (R := R) c x, truncatedEnvelopingDerivation c D⁆ =
      -truncatedLeftRepresentation (R := R) c (D x) := by
  rw [← lie_skew, truncated_derivation_left_commutator]

variable {H : Type*} [LieRing H] [LieAlgebra R H]

def truncatedSemidirectRepresentation (c : ℕ) (ψ : H →ₗ⁅R⁆ LieDerivation R L L) :
    (L ⋊⁅ψ⁆ H) →ₗ⁅R⁆ Module.End R (Q c) where
  toFun p := truncatedLeftRepresentation (R := R) c p.left +
    truncatedEnvelopingDerivationRepresentation c (ψ p.right)
  map_add' p q := by
    change truncatedLeftRepresentation (R := R) c (p.left + q.left) +
      truncatedEnvelopingDerivationRepresentation c (ψ (p.right + q.right)) = _
    simp only [map_add]
    abel
  map_smul' r p := by
    change truncatedLeftRepresentation (R := R) c (r • p.left) +
      truncatedEnvelopingDerivationRepresentation c (ψ (r • p.right)) = _
    simp only [map_smul, RingHom.id_apply, smul_add]
  map_lie' {p q} := by
    change truncatedLeftRepresentation (R := R) c
      (⁅p.left, q.left⁆ + ψ p.right q.left - ψ q.right p.left) +
      truncatedEnvelopingDerivationRepresentation c (ψ ⁅p.right, q.right⁆) =
      ⁅truncatedLeftRepresentation (R := R) c p.left + truncatedEnvelopingDerivation c (ψ p.right),
        truncatedLeftRepresentation (R := R) c q.left + truncatedEnvelopingDerivation c (ψ q.right)⁆
    simp only [map_add, map_sub, LieHom.map_lie, lie_add, add_lie,
      truncated_left_derivation_commutator, truncated_derivation_left_commutator]
    change _ + ⁅truncatedEnvelopingDerivation c (ψ p.right),
      truncatedEnvelopingDerivation c (ψ q.right)⁆ = _
    abel

@[simp]
theorem truncatedEnvelopingDerivation_one (c : ℕ) (D : LieDerivation R L L) :
    truncatedEnvelopingDerivation c D 1 = 0 := by
  change truncatedEnvelopingProjection c (envelopingDerivation D (1 :
    UniversalEnvelopingAlgebra R L)) = 0
  have h : envelopingDerivation D (1 : UniversalEnvelopingAlgebra R L) = 0 := by
    simpa using envelopingDerivation_scalar D (1 : R)
  rw [h, map_zero]

theorem truncatedSemidirectRepresentation_injective (c : ℕ)
    (ψ : H →ₗ⁅R⁆ LieDerivation R L L) (hψ : Function.Injective ψ)
    (hgen : Function.Injective (truncatedEnvelopingGenerator (R := R) (L := L) c)) :
    Function.Injective (truncatedSemidirectRepresentation c ψ) := by
  intro p q hpq
  have hl : p.left = q.left := by
    apply hgen
    have h := DFunLike.congr_fun hpq 1
    change truncatedEnvelopingGenerator c p.left * 1 +
      truncatedEnvelopingDerivation c (ψ p.right) 1 =
      truncatedEnvelopingGenerator c q.left * 1 +
      truncatedEnvelopingDerivation c (ψ q.right) 1 at h
    simpa only [mul_one, truncatedEnvelopingDerivation_one, add_zero] using h
  have hd : truncatedEnvelopingDerivation c (ψ p.right) =
      truncatedEnvelopingDerivation c (ψ q.right) := by
    change truncatedLeftRepresentation (R := R) c p.left +
      truncatedEnvelopingDerivation c (ψ p.right) =
      truncatedLeftRepresentation (R := R) c q.left +
      truncatedEnvelopingDerivation c (ψ q.right) at hpq
    rw [hl] at hpq
    exact add_left_cancel hpq
  have hr : p.right = q.right := by
    apply hψ
    apply LieDerivation.ext
    intro x
    apply hgen
    have h := DFunLike.congr_fun hd (truncatedEnvelopingGenerator c x)
    simpa only [truncatedEnvelopingDerivation_generator] using h
  exact SemiDirectSum.ext hl hr

theorem truncatedLeftRepresentation_nilpotent (c : ℕ) (x : L) :
    IsNilpotent (truncatedLeftRepresentation (R := R) c x) := by
  have hq : (truncatedEnvelopingGenerator (R := R) c x) ^ c = 0 := by
    simpa only [List.map_replicate, List.prod_replicate] using
      truncatedEnvelopingGenerator_prod_eq_zero (R := R) c (List.replicate c x)
        (by simp only [List.length_replicate, le_refl])
  refine ⟨c, ?_⟩
  change (Algebra.lmul R (Q c) (truncatedEnvelopingGenerator c x)) ^ c = 0
  rw [← map_pow, hq, map_zero]

end PolycyclicRecognition

end

end OAI
