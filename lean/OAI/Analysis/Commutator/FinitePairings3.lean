import Mathlib
import OAI.Analysis.Commutator.FinitePairings
import OAI.Analysis.Commutator.FinitePairings2
import OAI.Analysis.Commutator.HilbertTensors

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

open PreHilbert

abbrev TailSlots (k l : ℕ) := Fin k ⊕ₗ Fin l

lemma finite_constant_coefficient_bound {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {N : ℕ} (T : E →L[ℂ] F) (v : Fin (N+1) → E) (hv : Orthonormal ℂ v)
    (w : F) (hw : ‖w‖ = 1) (c : ℂ) (hc : ∀ n, inner ℂ w (T (v n)) = c) :
    (N+1 : ℝ) * ‖c‖ ^ 2 ≤ ‖T‖ ^ 2 := by
  have hh := hv.sum_inner_products_le (T.adjoint w) (s := Finset.univ)
  have hc' (n) : ‖inner ℂ (v n) (T.adjoint w)‖ = ‖c‖ := by
    rw [← norm_inner_symm, ContinuousLinearMap.adjoint_inner_left, hc]
  simp only [hc', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hh
  have hn := T.adjoint.le_opNorm w
  rw [ContinuousLinearMap.adjoint.norm_map, hw, mul_one] at hn
  exact hh.trans (pow_le_pow_left₀ (norm_nonneg _) hn 2)

lemma finite_pairing_source_bound (E F : PreHilbert) (k l N : ℕ)
    (Ω : E) (hΩ : ‖Ω‖ = 1) (T : wordSpace E F k →L[ℂ] wordSpace E F l)
    (c : Pairing (TailSlots k l) → ℂ) (h : TailSlots k l × Fin (N+1) → F)
    (horth : Orthonormal ℂ h)
    (hexp : ∀ v : TailSlots k l → TailSlots k l × Fin (N+1),
      inner ℂ (word E F l Ω (fun j => h (v (.inr j))))
        (T (word E F k Ω (fun i => h (v (.inl i))))) =
        ∑ σ, c σ * Pairing.contraction σ (fun a b => if a = b then 1 else 0) v)
    (τ : Pairing (TailSlots k l)) (a b : Fin k) (hab : τ (.inl a) = .inl b) :
    (N+1 : ℝ) * ‖c τ‖ ^ 2 ≤ ‖T‖ ^ 2 := by
  classical
  let labels := fun (n : Fin (N+1)) => Pairing.finiteLabels τ (.inl a) n
  let source := fun n (i : Fin k) => labels n (.inl i)
  let test := fun (j : Fin l) => labels (0 : Fin (N+1)) (.inr j)
  have htest (n : Fin (N+1)) (j : Fin l) : labels n (.inr j) = test j := by
    have hne : Pairing.repr τ (.inr j) ≠ Pairing.repr τ (.inl a) := by
      intro hh
      rcases (Pairing.repr_eq_iff τ (.inl a) (.inr j)).mp hh.symm with hh | hh
      · cases hh
      · rw [hab] at hh
        cases hh
    simp only [labels, test, Pairing.finiteLabels, ite_eq_right hne]
  have hinj : Function.Injective source := by
    intro n m he
    have hh := congrArg Prod.snd (congrFun he a)
    simpa only [source, labels, Pairing.finiteLabels, ite_true] using hh
  have hsource : Orthonormal ℂ
      (fun n => word E F k Ω (fun i => h (source n i))) :=
    (word_orthonormal E F Ω hΩ h horth k).comp source hinj
  refine finite_constant_coefficient_bound T _ hsource
    (word E F l Ω (fun j => h (test j))) ?_ (c τ) ?_
  · rw [norm_word, hΩ]
    simp only [horth.norm_eq_one, Finset.prod_const_one, mul_one]
  · intro n
    have hh := hexp (labels n)
    have hsum : (∑ σ, c σ * Pairing.contraction σ
        (fun a b => if a = b then 1 else 0) (labels n)) = c τ := by
      have hcon (σ) : Pairing.contraction σ
          (fun a b => if a = b then 1 else 0) (labels n) = if σ = τ then 1 else 0 := by
        exact Pairing.finite_contraction_isolation τ σ (.inl a) n
          id (fun a b => if a = b then 1 else 0) (fun _ _ => rfl)
      simp only [hcon, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    rw [hsum] at hh
    simpa only [source, htest] using hh

lemma finite_pairing_test_bound (E F : PreHilbert) (k l N : ℕ)
    (Ω : E) (hΩ : ‖Ω‖ = 1) (T : wordSpace E F k →L[ℂ] wordSpace E F l)
    (c : Pairing (TailSlots k l) → ℂ) (h : TailSlots k l × Fin (N+1) → F)
    (horth : Orthonormal ℂ h)
    (hexp : ∀ v : TailSlots k l → TailSlots k l × Fin (N+1),
      inner ℂ (word E F l Ω (fun j => h (v (.inr j))))
        (T (word E F k Ω (fun i => h (v (.inl i))))) =
        ∑ σ, c σ * Pairing.contraction σ (fun a b => if a = b then 1 else 0) v)
    (τ : Pairing (TailSlots k l)) (a b : Fin l) (hab : τ (.inr a) = .inr b) :
    (N+1 : ℝ) * ‖c τ‖ ^ 2 ≤ ‖T‖ ^ 2 := by
  classical
  let labels := fun (n : Fin (N+1)) => Pairing.finiteLabels τ (.inr a) n
  let source := fun (i : Fin k) => labels (0 : Fin (N+1)) (.inl i)
  let test := fun n (j : Fin l) => labels n (.inr j)
  have hsource (n : Fin (N+1)) (i : Fin k) : labels n (.inl i) = source i := by
    have hne : Pairing.repr τ (.inl i) ≠ Pairing.repr τ (.inr a) := by
      intro hh
      rcases (Pairing.repr_eq_iff τ (.inr a) (.inl i)).mp hh.symm with hh | hh
      · cases hh
      · rw [hab] at hh
        cases hh
    simp only [labels, source, Pairing.finiteLabels, ite_eq_right hne]
  have hinj : Function.Injective test := by
    intro n m he
    have hh := congrArg Prod.snd (congrFun he a)
    simpa only [test, labels, Pairing.finiteLabels, ite_true] using hh
  have htest : Orthonormal ℂ
      (fun n => word E F l Ω (fun j => h (test n j))) :=
    (word_orthonormal E F Ω hΩ h horth l).comp test hinj
  have hc (n : Fin (N+1)) : inner ℂ (word E F l Ω (fun j => h (test n j)))
      (T (word E F k Ω (fun i => h (source i)))) = c τ := by
    have hh := hexp (labels n)
    have hsum : (∑ σ, c σ * Pairing.contraction σ
        (fun a b => if a = b then 1 else 0) (labels n)) = c τ := by
      have hcon (σ) : Pairing.contraction σ
          (fun a b => if a = b then 1 else 0) (labels n) = if σ = τ then 1 else 0 := by
        exact Pairing.finite_contraction_isolation τ σ (.inr a) n
          id (fun a b => if a = b then 1 else 0) (fun _ _ => rfl)
      simp only [hcon, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    rw [hsum] at hh
    simpa only [test, hsource] using hh
  have hh := htest.sum_inner_products_le
    (T (word E F k Ω (fun i => h (source i)))) (s := Finset.univ)
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hh
  have hn := T.le_opNorm (word E F k Ω (fun i => h (source i)))
  rw [norm_word, hΩ] at hn
  simp only [horth.norm_eq_one, Finset.prod_const_one, mul_one] at hn
  exact hh.trans (pow_le_pow_left₀ (norm_nonneg _) hn 2)

end Kadison
end

end OAI
