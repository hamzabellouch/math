import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNormBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesLift

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction HistorySignedDecode HistorySignedSpectator
open scoped BigOperators

lemma norm_map_prod_le {α : Type*} (xs : List α) (f : α → ℂ) (B : α → ℝ)
    (hB : ∀ a ∈ xs, 0 ≤ B a) (hf : ∀ a ∈ xs, ‖f a‖ ≤ B a) :
    ‖(xs.map f).prod‖ ≤ (xs.map B).prod := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.prod_cons, norm_mul]
    exact mul_le_mul (hf a List.mem_cons_self)
      (ih (fun b hb => hB b (List.mem_cons_of_mem a hb))
        (fun b hb => hf b (List.mem_cons_of_mem a hb)))
      (norm_nonneg _) (hB a List.mem_cons_self)

theorem norm_spectatorFactor_le_product (g : (q : ℕ) → ZMod q → ℂ)
    (outside : List ℕ) (B : ℕ → ℝ) (hB : ∀ q ∈ outside, 0 ≤ B q)
    (hg : ∀ q ∈ outside, ∀ x, ‖g q x‖ ≤ B q) (a : SignedState) :
    ‖spectatorFactor g outside a‖ ≤ (outside.map B).prod :=
  norm_map_prod_le outside _ B hB (fun q hq => hg q hq _)

theorem norm_spectatorProduct_le_power (g : (q : ℕ) → ZMod q → ℂ)
    (outside : List ℕ) (B : ℕ → ℝ) (hB : ∀ q ∈ outside, 0 ≤ B q)
    (hg : ∀ q ∈ outside, ∀ x, ‖g q x‖ ≤ B q) {l : ℕ} (h : SignedHistory l) :
    ‖spectatorProduct g outside h‖ ≤ (outside.map B).prod ^ (2^l) := by
  have hP : 0 ≤ (outside.map B).prod := List.prod_nonneg (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hB q hq)
  induction h with
  | leaf a => simpa only [spectatorProduct, HistorySignedSpectator.leafProduct, pow_zero,pow_one] using norm_spectatorFactor_le_product g outside B hB hg a
  | @node l a p u hp hm left right il ir =>
    change ‖spectatorProduct g outside left * star (spectatorProduct g outside right)‖ ≤ _
    rw [norm_mul, norm_star]
    calc
      _ ≤ (outside.map B).prod^(2^l) * (outside.map B).prod^(2^l) :=
        mul_le_mul il ir (norm_nonneg _) (pow_nonneg hP _)
      _ = (outside.map B).prod^(2^(l+1)) := by rw [pow_succ, pow_mul, pow_two]

theorem norm_pairSpectator_le_power (g : (q : ℕ) → ZMod q → ℂ)
    (outside : List ℕ) (B : ℕ → ℝ) (hB : ∀ q ∈ outside, 0 ≤ B q)
    (hg : ∀ q ∈ outside, ∀ x, ‖g q x‖ ≤ B q) {l : ℕ} (h k : SignedHistory l) :
    ‖pairSpectator g outside h k‖ ≤ (outside.map B).prod ^ (2^(l+1)) := by
  have hP : 0 ≤ (outside.map B).prod := List.prod_nonneg (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hB q hq)
  change ‖spectatorProduct g outside h * star (spectatorProduct g outside k)‖ ≤ _
  rw [norm_mul, norm_star]
  calc
    _ ≤ (outside.map B).prod^(2^l) * (outside.map B).prod^(2^l) :=
      mul_le_mul (norm_spectatorProduct_le_power g outside B hB hg h)
        (norm_spectatorProduct_le_power g outside B hB hg k) (norm_nonneg _) (pow_nonneg hP _)
    _ = (outside.map B).prod^(2^(l+1)) := by rw [pow_succ, pow_mul, pow_two]

theorem residueTransform_norm_le_prime (d : Decomposition) (p : ℕ) (hp : p.Prime)
    (v : ZMod p) : ‖residueTransform d p v‖ ≤ (p : ℝ) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hs := residueTransform_sq_sum d p hp
  have hv : ‖residueTransform d p v‖^2 ≤ (p : ℝ) := by
    rw [←hs]
    exact Finset.single_le_sum (f := fun x : ZMod p => ‖residueTransform d p x‖^2)
      (fun x _ => sq_nonneg _) (Finset.mem_univ v)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  nlinarith [norm_nonneg (residueTransform d p v)]

theorem norm_actual_residueTest_le {l : ℕ} (d : Decomposition)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l)
    (hout : ∀ q ∈ outside, q.Prime)
    (z : ZMod (pairModulus h k outside) × ZMod (pairModulus h k outside)) :
    ‖residueTest (residueTransform d) V outside h k z‖ ≤ (outside.prod : ℝ)^(2^(l+1)) := by
  classical
  have hp := norm_pairSpectator_le_power (residueTransform d) outside (fun q => (q:ℝ))
    (fun q _ => Nat.cast_nonneg q) (fun q hq x => residueTransform_norm_le_prime d q (hout q hq) x)
    (rebuild h z.1.val z.2.val) (rebuild k z.1.val z.2.val)
  have hp' : ‖pairSpectator (residueTransform d) outside
      (rebuild h z.1.val z.2.val) (rebuild k z.1.val z.2.val)‖ ≤
      (outside.prod : ℝ)^(2^(l+1)) := by simpa only [Nat.cast_list_prod] using hp
  unfold residueTest residueMask
  split_ifs
  · simpa only [Complex.ofReal_one,one_mul,spectatorResidue] using hp'
  · simp only [Complex.ofReal_zero,zero_mul,norm_zero]
    positivity

theorem norm_actual_liftedResidueTest_le {l : ℕ} (d : Decomposition)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (M : ℕ)
    (hd : pairModulus h k outside ∣ M) (hout : ∀ q ∈ outside, q.Prime)
    (z : ZMod M × ZMod M) :
    ‖liftedResidueTest (residueTransform d) V outside h k M hd z‖ ≤
      (outside.prod : ℝ)^(2^(l+1)) := norm_actual_residueTest_le d V outside h k hout _

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
