import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorBasic

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectator
open Construction HistorySignedDecode

lemma norm_prod_le_one (xs : List ℂ) (hx : ∀x∈xs,‖x‖≤1) : ‖xs.prod‖≤1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := hx x (List.mem_cons_self)
    have ht := ih (fun y hy=>hx y (List.mem_cons_of_mem x hy))
    simpa only [List.prod_cons,norm_mul,one_mul] using
      mul_le_mul hh ht (norm_nonneg _) (by norm_num : (0:ℝ)≤1)

theorem norm_spectatorFactor_le (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (hg : ∀q∈outside,∀x,‖g q x‖≤1) (a : SignedState) :
    ‖spectatorFactor g outside a‖≤1 := by
  apply norm_prod_le_one
  intro z hz
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
  exact hg q hq _

theorem norm_leafProduct_le (f : SignedState→ℂ) (hf : ∀a,‖f a‖≤1)
    {l : ℕ} (h : SignedHistory l) : ‖leafProduct f h‖≤1 := by
  induction h with
  | leaf a => exact hf a
  | node a p u hp hm left right il ir =>
    simpa only [leafProduct,norm_mul,Complex.norm_conj,one_mul] using
      mul_le_mul il ir (norm_nonneg _) (by norm_num : (0:ℝ)≤1)

theorem norm_spectatorProduct_le (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (hg : ∀q∈outside,∀x,‖g q x‖≤1) {l : ℕ} (h : SignedHistory l) :
    ‖spectatorProduct g outside h‖≤1 :=
  norm_leafProduct_le _ (norm_spectatorFactor_le g outside hg) h

theorem norm_pairSpectator_le (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ)
    (hg : ∀q∈outside,∀x,‖g q x‖≤1) {l : ℕ} (h k : SignedHistory l) :
    ‖pairSpectator g outside h k‖≤1 := by
  simpa only [pairSpectator,norm_mul,Complex.norm_conj,one_mul] using
    mul_le_mul (norm_spectatorProduct_le g outside hg h)
      (norm_spectatorProduct_le g outside hg k) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)

end Ostmann.Arithmetic.HistorySignedSpectator

end

end OAI
