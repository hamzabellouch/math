import Mathlib
import OAI.Analysis.Commutator.CrossingPairings
import OAI.Analysis.Commutator.PairingElimination
import OAI.Analysis.Commutator.TensorPermutations3

namespace OAI

noncomputable section

noncomputable section

open scoped TensorProduct

namespace Kadison

attribute [instance] PreHilbert.normed PreHilbert.ipSpace

namespace PreHilbert

end PreHilbert

end Kadison

namespace Kadison.PreHilbert

end Kadison.PreHilbert

namespace Kadison

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

end Kadison

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end Kadison

namespace Kadison

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

end Kadison

namespace Kadison

section Gram

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

end Gram

end Kadison

namespace Kadison

section GramEquiv

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

end GramEquiv

namespace PreHilbert

end PreHilbert

end Kadison

noncomputable section

namespace Kadison

namespace Pairing

variable {J : Type*}

variable [LinearOrder J]

variable [Fintype J]

end Pairing

end Kadison

namespace Kadison

open PreHilbert

end Kadison

namespace Kadison

open PreHilbert

end Kadison

namespace Kadison

namespace Pairing

end Pairing

end Kadison

namespace Kadison

open PreHilbert

def tailVector {k l : ℕ} {E : Type*} (x : Fin k → E) (y : Fin l → E) :
    TailSlots k l → E := fun j => Sum.elim x y (ofLex j)

@[simp] theorem tailVector_inl {k l : ℕ} {E : Type*} (x : Fin k → E)
    (y : Fin l → E) (a : Fin k) : tailVector x y (Sum.inl a) = x a := rfl

@[simp] theorem tailVector_inr {k l : ℕ} {E : Type*} (x : Fin k → E)
    (y : Fin l → E) (b : Fin l) : tailVector x y (Sum.inr b) = y b := rfl

theorem pairing_coefficient_zero_noncrossing (E : PreHilbert) (k l : ℕ)
    (T : hilbertPower E k →L[ℂ] hilbertPower E l)
    (Jmap : E → E) (B : E → E → ℂ) (c : Pairing (TailSlots k l) → ℂ)
    (h : TailSlots k l × ℕ → E) (horth : Orthonormal ℂ h)
    (hself : ∀ a, Jmap (h a) = h a)
    (hB : ∀ a b, B (h a) (h b) = if a = b then 1 else 0)
    (hexp : ∀ v : TailSlots k l → E,
      inner ℂ (hilbertPure E l (fun j => Jmap (v (.inr j))))
        (T (hilbertPure E k (fun i => v (.inl i)))) =
        ∑ σ, c σ * Pairing.contraction σ B v)
    (τ : Pairing (TailSlots k l)) (hτ : ¬ τ.Crosses) : c τ = 0 := by
  by_contra hc
  apply hτ
  constructor
  · intro a
    cases he : τ (.inl a) with
    | inl b => exact (hc (pairing_coefficient_zero_source E k l T Jmap B c h horth hself hB hexp τ a b he)).elim
    | inr b => exact ⟨b, rfl⟩
  · intro a
    cases he : τ (.inr a) with
    | inl b => exact ⟨b, rfl⟩
    | inr b => exact (hc (pairing_coefficient_zero_test E k l T Jmap B c h horth hself hB hexp τ a b he)).elim

theorem pairing_operator_eq_zero (E : PreHilbert) (k l : ℕ)
    (T : hilbertPower E k →L[ℂ] hilbertPower E l)
    (Jmap : E → E) (hJ : Function.Involutive Jmap)
    (B : E → E → ℂ) (c : Pairing (TailSlots k l) → ℂ)
    (h : TailSlots k l × ℕ → E) (horth : Orthonormal ℂ h)
    (hself : ∀ a, Jmap (h a) = h a)
    (hB : ∀ a b, B (h a) (h b) = if a = b then 1 else 0)
    (hexp : ∀ v : TailSlots k l → E,
      inner ℂ (hilbertPure E l (fun j => Jmap (v (.inr j))))
        (T (hilbertPure E k (fun i => v (.inl i)))) =
        ∑ σ, c σ * Pairing.contraction σ B v)
    (hkl : k ≠ l) : T = 0 := by
  have hJJ (z : E) : Jmap (Jmap z) = z := hJ z
  have hz := pairing_coefficients_zero_of_ne E k l T Jmap B c h horth hself hB hexp hkl
  apply continuousLinearMap_ext_pure E k
  intro x
  change T (hilbertPure E k x) = 0
  apply eq_zero_of_hilbertPure_inner E l
  intro y
  have hh := hexp (tailVector x (Jmap ∘ y))
  simpa only [tailVector_inl, tailVector_inr, Function.comp_apply, hJJ,
    hz, zero_mul, Finset.sum_const_zero] using hh

theorem crossing_contraction_inner (E : PreHilbert) (n : ℕ)
    (Jmap : E → E) (hJ : Function.Involutive Jmap)
    (B : E → E → ℂ) (hB : ∀ x y, B x y = inner ℂ (Jmap y) x)
    (e : Equiv.Perm (Fin n)) (x y : Fin n → E) :
    Pairing.contraction (Pairing.crossPairing e) B (tailVector x (Jmap ∘ y)) =
      inner ℂ (hilbertPure E n y)
        (hilbertPermute E n e.symm (hilbertPure E n x)) := by
  classical
  have hJJ (z : E) : Jmap (Jmap z) = z := hJ z
  rw [Pairing.contraction_crossPairing, hilbertPermute_pure, inner_hilbertPure]
  simp only [tailVector_inl, tailVector_inr, Function.comp_apply, hB, hJJ]
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.prod_comp e (fun j => inner ℂ (y j) (x (e.symm j))))

theorem pairing_operator_eq_permutation_sum (E : PreHilbert) (n : ℕ)
    (T : hilbertPower E n →L[ℂ] hilbertPower E n)
    (Jmap : E → E) (hJ : Function.Involutive Jmap)
    (B : E → E → ℂ) (hB : ∀ x y, B x y = inner ℂ (Jmap y) x)
    (c : Pairing (TailSlots n n) → ℂ)
    (h : TailSlots n n × ℕ → E) (horth : Orthonormal ℂ h)
    (hself : ∀ a, Jmap (h a) = h a)
    (hexp : ∀ v : TailSlots n n → E,
      inner ℂ (hilbertPure E n (fun j => Jmap (v (.inr j))))
        (T (hilbertPure E n (fun i => v (.inl i)))) =
        ∑ σ, c σ * Pairing.contraction σ B v) :
    T = ∑ e : Equiv.Perm (Fin n), c (Pairing.crossPairing e) •
      (hilbertPermute E n e.symm).toContinuousLinearEquiv.toContinuousLinearMap := by
  classical
  have hJJ (z : E) : Jmap (Jmap z) = z := hJ z
  have hBorth (a b) : B (h a) (h b) = if a = b then 1 else 0 := by
    rw [hB, hself]
    rw [orthonormal_iff_ite.mp horth]
    simp only [eq_comm]
  have hz := pairing_coefficient_zero_noncrossing E n n T Jmap B c h horth hself hBorth hexp
  apply continuousLinearMap_ext_pure E n
  intro x
  apply sub_eq_zero.mp
  apply eq_zero_of_hilbertPure_inner E n
  intro y
  rw [inner_sub_right]
  apply sub_eq_zero.mpr
  have hh := hexp (tailVector x (Jmap ∘ y))
  simp only [tailVector_inl, tailVector_inr, Function.comp_apply, hJJ] at hh
  rw [hh, Pairing.sum_contraction_crossing B _ c hz]
  simp only [sum_apply, smul_apply,
    inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro e _
  exact congrArg (fun z => c (Pairing.crossPairing e) * z)
    ((Pairing.contraction_crossPairing e B (tailVector x (Jmap ∘ y))).symm.trans
      (crossing_contraction_inner E n Jmap hJ B hB e x y))

end Kadison
end
end
end

end OAI
