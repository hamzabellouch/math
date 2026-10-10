import Mathlib
import OAI.Analysis.Commutator.InvariantForms

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def rawCycleTrace (σ : Equiv.Perm J) (A : J → Matrix I I 𝕜) : 𝕜 :=
  Matrix.trace (permutationMatrix σ * tensorMatrices A)

lemma rawCycleTrace_eq_sum (σ : Equiv.Perm J) (A : J → Matrix I I 𝕜) :
    rawCycleTrace σ A = ∑ a : J → I, ∏ j, A j (a (σ j)) (a j) := by
  classical
  simp only [rawCycleTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    permutationMatrix, tensorMatrices]
  apply Finset.sum_congr rfl
  intro a _
  have he (b : J → I) : a = b ∘ σ.symm ↔ b = a ∘ σ := by
    constructor
    · intro h; ext j; simpa using (congrFun h (σ j)).symm
    · rintro rfl; simp [Function.comp_def]
  simp only [he, ite_mul, one_mul, zero_mul]
  simp

def cycleSet (σ : Equiv.Perm J) := Quotient (Equiv.Perm.SameCycle.setoid σ)

instance (σ : Equiv.Perm J) : Fintype (cycleSet σ) := by
  unfold cycleSet
  exact Fintype.ofFinite _

def cycleCount (σ : Equiv.Perm J) : ℕ := Fintype.card (cycleSet σ)

omit [DecidableEq J] in
lemma constant_on_cycle {R : Type*} (σ : Equiv.Perm J) (f : J → R)
    (hf : ∀ j, f (σ j) = f j) {i j : J} (h : σ.SameCycle i j) : f i = f j := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply, hf] using ih

def fixedLabelEquiv (R : Type*) (σ : Equiv.Perm J) :
    {f : J → R // ∀ j, f (σ j) = f j} ≃ (cycleSet σ → R) where
  toFun f := Quotient.lift f.val (fun _ _ h => constant_on_cycle σ f.val f.property h)
  invFun f := ⟨fun j => f (Quotient.mk _ j), fun j => congrArg f (Quotient.sound (by
    exact (Equiv.Perm.SameCycle.refl σ j).apply_left))⟩
  left_inv f := by rfl
  right_inv f := by ext q; refine Quotient.inductionOn q (fun j => ?_); rfl

lemma fixedLabel_card (R : Type*) [Fintype R] [DecidableEq R] (σ : Equiv.Perm J) :
    Fintype.card {f : J → R // ∀ j, f (σ j) = f j} =
      Fintype.card R ^ cycleCount σ := by
  classical
  rw [Fintype.card_congr (fixedLabelEquiv R σ), Fintype.card_fun, cycleCount]

lemma rawCycleTrace_single (b : J → I) (hb : Function.Injective b)
    (σ τ : Equiv.Perm J) :
    rawCycleTrace σ (fun j => Matrix.single (b (τ j)) (b j) (1 : 𝕜)) =
      if σ = τ then 1 else 0 := by
  classical
  unfold rawCycleTrace
  rw [tensorMatrices_single, Matrix.trace_mul_single]
  simp only [MulOpposite.op_one, one_smul, permutationMatrix]
  have he : b = (fun j => b (τ j)) ∘ σ.symm ↔ σ = τ := by
    constructor
    · intro h
      apply Equiv.ext
      intro j
      apply hb
      simpa using congrFun h (σ j)
    · rintro rfl
      ext j
      simp
  by_cases h : σ = τ
  · subst τ
    simp [Function.comp_def]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (he.mp hh))]

def inflateMatrix {R : Type*} [DecidableEq R] (A : Matrix I I 𝕜) :
    Matrix (I × R) (I × R) 𝕜 :=
  fun a b => if a.2 = b.2 then A a.1 b.1 else 0

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
lemma prod_inflateMatrix {R : Type*} [DecidableEq R]
    (σ : Equiv.Perm J) (A : J → Matrix I I 𝕜) (a : J → I) (r : J → R) :
    (∏ j, inflateMatrix (A j) (a (σ j), r (σ j)) (a j, r j)) =
      if ∀ j, r (σ j) = r j then ∏ j, A j (a (σ j)) (a j) else 0 := by
  classical
  by_cases h : ∀ j, r (σ j) = r j
  · simp [inflateMatrix, h]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

omit [Fintype I] [DecidableEq I] in
lemma fixedLabel_indicator_sum (R : Type*) [Fintype R] [DecidableEq R]
    (σ : Equiv.Perm J) :
    (∑ r : J → R, if ∀ j, r (σ j) = r j then (1 : 𝕜) else 0) =
      (Fintype.card R : 𝕜) ^ cycleCount σ := by
  classical
  calc
    _ = (Fintype.card {r : J → R // ∀ j, r (σ j) = r j} : 𝕜) := by
      rw [Fintype.card_subtype]
      exact Finset.sum_boole _ _
    _ = _ := by rw [fixedLabel_card, Nat.cast_pow]

lemma rawCycleTrace_inflate (R : Type*) [Fintype R] [DecidableEq R]
    (σ : Equiv.Perm J) (A : J → Matrix I I 𝕜) :
    rawCycleTrace σ (fun j => inflateMatrix (R := R) (A j)) =
      (Fintype.card R : 𝕜) ^ cycleCount σ * rawCycleTrace σ A := by
  classical
  rw [rawCycleTrace_eq_sum, rawCycleTrace_eq_sum]
  calc
    _ = ∑ ar : (J → I) × (J → R),
        ∏ j, inflateMatrix (A j) (ar.1 (σ j), ar.2 (σ j)) (ar.1 j, ar.2 j) := by
      apply Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow J (fun _ => I) (fun _ => R))
      intro x
      rfl
    _ = ∑ a : J → I, ∑ r : J → R,
        ∏ j, inflateMatrix (A j) (a (σ j), r (σ j)) (a j, r j) :=
      Fintype.sum_prod_type _
    _ = ∑ a : J → I, ∑ r : J → R,
        (if ∀ j, r (σ j) = r j then (1 : 𝕜) else 0) *
          ∏ j, A j (a (σ j)) (a j) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro r _
      rw [prod_inflateMatrix]
      split_ifs <;> simp
    _ = _ := by
      simp_rw [← Finset.sum_mul, fixedLabel_indicator_sum]
      rw [Finset.mul_sum]

def cycleTrace (σ : Equiv.Perm J) (A : J → Matrix I I ℂ) : ℂ :=
  (Fintype.card I : ℂ)⁻¹ ^ cycleCount σ * rawCycleTrace σ A

lemma cycleTrace_inflate (R : Type*) [Fintype R] [DecidableEq R] [Nonempty R]
    (σ : Equiv.Perm J) (A : J → Matrix I I ℂ) :
    cycleTrace σ (fun j => inflateMatrix (R := R) (A j)) = cycleTrace σ A := by
  classical
  have hr : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [cycleTrace, Fintype.card_prod, Nat.cast_mul, _root_.mul_inv_rev, mul_pow,
    rawCycleTrace_inflate]
  have hc : ((Fintype.card R : ℂ)⁻¹ ^ cycleCount σ) *
      (Fintype.card R : ℂ) ^ cycleCount σ = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hr, one_pow]
  calc
    _ = (((Fintype.card R : ℂ)⁻¹ ^ cycleCount σ) *
        (Fintype.card R : ℂ) ^ cycleCount σ) *
          ((Fintype.card I : ℂ)⁻¹ ^ cycleCount σ * rawCycleTrace σ A) := by ring
    _ = _ := by rw [hc, one_mul]

lemma cycleTrace_single (b : J → I) (hb : Function.Injective b)
    (σ τ : Equiv.Perm J) :
    cycleTrace σ (fun j => Matrix.single (b (τ j)) (b j) 1) =
      if σ = τ then (Fintype.card I : ℂ)⁻¹ ^ cycleCount τ else 0 := by
  rw [cycleTrace, rawCycleTrace_single b hb]
  split_ifs with h
  · subst τ; rw [mul_one]
  · rw [mul_zero]

lemma cycleTrace_coefficients_unique [Nonempty I] (b : J → I)
    (hb : Function.Injective b) (c d : Equiv.Perm J → ℂ)
    (h : ∀ A : J → Matrix I I ℂ, ∑ σ, c σ * cycleTrace σ A =
      ∑ σ, d σ * cycleTrace σ A) : c = d := by
  classical
  funext τ
  have he := h (fun j => Matrix.single (b (τ j)) (b j) 1)
  simp only [cycleTrace_single b hb, mul_ite, mul_zero] at he
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at he
  apply mul_right_cancel₀ _ he
  exact pow_ne_zero _ (inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero))

lemma stable_cycle_coefficients [Nonempty I] (R : Type*) [Fintype R]
    [DecidableEq R] [Nonempty R] (b : J → I) (hb : Function.Injective b)
    (c d : Equiv.Perm J → ℂ)
    (h : ∀ A : J → Matrix I I ℂ, ∑ σ, c σ * cycleTrace σ A =
      ∑ σ, d σ * cycleTrace σ (fun j => inflateMatrix (R := R) (A j))) : c = d := by
  apply cycleTrace_coefficients_unique b hb c d
  intro A
  simpa only [cycleTrace_inflate] using h A

theorem invariant_multilinear_form_normalized [Nonempty I] (b : J → I)
    (hb : Function.Injective b) (F : MultilinearMap ℂ (fun _ : J => Matrix I I ℂ) ℂ)
    (hF : ∀ (U : unitary (Matrix I I ℂ)) (A : J → Matrix I I ℂ),
      F (fun j => (U : Matrix I I ℂ) * A j * star (U : Matrix I I ℂ)) = F A) :
    ∃! c : Equiv.Perm J → ℂ, ∀ A : J → Matrix I I ℂ,
      F A = ∑ σ, c σ * cycleTrace σ A := by
  classical
  obtain ⟨c, hc⟩ := invariant_multilinear_form b hb F hF
  let d : Equiv.Perm J → ℂ := fun σ => c σ * (Fintype.card I : ℂ) ^ cycleCount σ
  have hi : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd (A : J → Matrix I I ℂ) : F A = ∑ σ, d σ * cycleTrace σ A := by
    rw [hc]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [d, cycleTrace, rawCycleTrace]
    rw [mul_assoc, ← mul_assoc ((Fintype.card I : ℂ) ^ cycleCount σ),
      ← mul_pow, mul_inv_cancel₀ hi, one_pow, one_mul]
  refine ⟨d, hd, ?_⟩
  intro e he
  exact cycleTrace_coefficients_unique b hb e d (fun A => (he A).symm.trans (hd A))

end Kadison.SchurWeyl
end

end OAI
