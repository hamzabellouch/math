import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorProductMixedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesBounds

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkResidueNormSum
open Construction HistoryBulkSpectatorProduct HistoryBulkSpectatorDiagramAverage
open HistorySignedSpectatorDiagramAverage HistoryCRTIntegration

theorem evaluate_norm_le {F : Type*} [Field F] (g : F → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hg : ∀x, ‖g x‖ ≤ B) (D : Fˣ)
    {l : ℕ} (p : Tree.Parameters F l) (a b : Fˣ) (y : F)
    (M : Tree.Leaves l → Fˣ) :
    ‖p.evaluate g D a b y M‖ ≤ B^(2^l) := by
  induction p generalizing a b y with
  | leaf s c =>
    cases c <;> simpa [Tree.Parameters.evaluate] using hg y
  | @branch l s a' b' u left right ihl ihr =>
    simp only [Tree.Parameters.evaluate]
    split_ifs
    · simpa only [norm_zero] using pow_nonneg hB (2^(l+1))
    · rw [norm_mul]
      calc
        _ ≤ B^(2^l)*B^(2^l) := mul_le_mul (ihl _ _ _ _) (ihr _ _ _ _)
          (norm_nonneg _) (pow_nonneg hB _)
        _ = B^(2^(l+1)) := by rw [pow_succ, pow_mul, pow_two]

theorem diagram_value_norm_le {F : Type*} [Field F] (g : F → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hg : ∀x, ‖g x‖ ≤ B) {l : ℕ} (T : Tree.Diagram F l)
    (M : Tree.Leaves l → Fˣ) : ‖T.value g M‖ ≤ B^(2^l) := by
  unfold Tree.Diagram.value
  cases l with
  | zero =>
    cases hp : T.parameters with
    | leaf s c => cases c <;> simpa [Tree.Parameters.value] using hg ((s:F) / M (fun i => Fin.elim0 i))
  | succ l => exact evaluate_norm_le g hB hg _ _ _ _ _ _

theorem orderedIntegrand_norm_le {q l m : ℕ} [Fact q.Prime]
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (T U : Tree.Diagram (ZMod q) l)
    (g : ZMod q → ℂ) {B : ℝ} (hB : 0 ≤ B) (hg : ∀x, ‖g x‖ ≤ B)
    (x : Fin (2^l)×Fin m → (ZMod q)ˣ) :
    ‖orderedIntegrand σ T U g x‖ ≤ B^(2^(l+1)) := by
  rw [orderedIntegrand, norm_mul, Complex.norm_conj]
  calc
    _ ≤ B^(2^l)*B^(2^l) := mul_le_mul (diagram_value_norm_le g hB hg _ _)
      (diagram_value_norm_le g hB hg _ _) (norm_nonneg _) (pow_nonneg hB _)
    _ = B^(2^(l+1)) := by rw [pow_succ, pow_mul, pow_two]

theorem actual_unitTest_norm_le (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (roots : UnitPair outside.prod) (x : Fin (2^l)×Fin m → (ZMod outside.prod)ˣ) :
    ‖unitTest h k hs ks hp hV σ (residueTransform d) roots x‖ ≤
      (outside.prod:ℝ)^(2^(l+1)) := by
  let := primeAtFact hp
  rw [unitTest, norm_prod]
  calc
    _ ≤ ∏i : Fin outside.length, (primeAt outside i:ℝ)^(2^(l+1)) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      exact orderedIntegrand_norm_le _ _ _ _ (Nat.cast_nonneg _)
        (HistorySignedResidues.residueTransform_norm_le_prime d _ (hp _ (List.get_mem outside i))) _
    _ = (outside.prod:ℝ)^(2^(l+1)) := by
      rw [Finset.prod_pow]
      congr 1
      rw [← Nat.cast_prod, HistorySignedSpectatorDiagramAverage.primeAt_prod]

theorem actual_mixedTest_norm_le (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (roots : MixedPair outside.prod) (x : Fin (2^l)×Fin m → (ZMod outside.prod)ˣ) :
    ‖mixedTest h k hs ks hp hV σ (residueTransform d) roots x‖ ≤
      (outside.prod:ℝ)^(2^(l+1)) := by
  classical
  by_cases hr : IsUnit roots.1
  · rw [mixedTest_eq_of_isUnit _ _ _ _ _ _ _ _ _ _ hr]
    exact actual_unitTest_norm_le d h k hs ks hp hV σ _ x
  · rw [mixedTest_nonunit _ _ _ _ _ _ _ _ _ _ hr, norm_zero]
    positivity

end Ostmann.Arithmetic.HistoryBulkResidueNormSum

end

end OAI
