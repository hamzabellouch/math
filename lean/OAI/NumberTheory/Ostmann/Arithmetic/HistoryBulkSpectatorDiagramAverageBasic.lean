import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkCoupled
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagramParametersEvaluation
import OAI.NumberTheory.Ostmann.Arithmetic.PermutationDiagramComparisonActual
import OAI.NumberTheory.Ostmann.Construction.ActualRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverage
open Construction CanonicalHistoryLeafBulk PermutationDiagramComparison ResidueHaar
open HistoryResidueRegular HistoryTreeParameters HistorySignedSpectatorDiagram
variable {q depth m : ℕ} [Fact q.Prime]

def orderedIntegrand (σ : Equiv.Perm (Fin (2^depth)×Fin m))
    (T1 T2 : Tree.Diagram (ZMod q) depth) (g : ZMod q→ℂ)
    (samples : Fin (2^depth)×Fin m→(ZMod q)ˣ) : ℂ :=
  T1.value g (orderedProducts σ samples).1*conj (T2.value g (orderedProducts σ samples).2)

def orderedCorrelation (σ : Equiv.Perm (Fin (2^depth)×Fin m))
    (T1 T2 : Tree.Diagram (ZMod q) depth) (g : ZMod q→ℂ) : ℂ :=
  average (orderedIntegrand σ T1 T2 g)

def haarSamplesEquiv (depth m : ℕ) (G : Type*) :
    (Fin (2^depth)×Fin m→G) ≃ (Fin (2^depth)×Fin m→G) where
  toFun := haarSamples
  invFun := fun samples=>samples ∘ (slotChange depth m).symm
  left_inv samples := by funext u; simp only [haarSamples,Function.comp_apply,Equiv.apply_symm_apply]
  right_inv samples := by funext u; simp only [haarSamples,Function.comp_apply,Equiv.symm_apply_apply]

theorem orderedCorrelation_eq_slotCorrelation
    (σ : Equiv.Perm (Fin (2^depth)×Fin m))
    (T1 T2 : Tree.Diagram (ZMod q) depth) (g : ZMod q→ℂ) :
    orderedCorrelation σ T1 T2 g=slotCorrelation (haarPermutation σ) T1 T2 g := by
  have he := average_equiv (haarSamplesEquiv depth m (ZMod q)ˣ)
    (fun samples=>T1.value g (slotLeaves (haarPermutation σ) samples).1*
      conj (T2.value g (slotLeaves (haarPermutation σ) samples).2))
  change average (fun samples=>T1.value g
      (slotLeaves (haarPermutation σ) (haarSamples samples)).1*
        conj (T2.value g (slotLeaves (haarPermutation σ) (haarSamples samples)).2))=_ at he
  change average (fun samples=>T1.value g (orderedProducts σ samples).1*
    conj (T2.value g (orderedProducts σ samples).2))=_
  simpa only [orderedProducts_eq_slotLeaves,slotCorrelation] using he

theorem actual_l2Sq_eq_one (d : Decomposition) : FiniteField.l2Sq (residueTransform d q)=1 := by
  unfold FiniteField.l2Sq
  rw [residueTransform_sq_sum d q (Fact.out : q.Prime)]
  exact inv_mul_cancel₀ (by exact_mod_cast (Fact.out : q.Prime).ne_zero)

theorem orderedCorrelation_actual_universal (d : Decomposition)
    (σ : Equiv.Perm (Fin (2^depth)×Fin m)) (hm : 0 < m)
    (T1 T2 : Tree.Diagram (ZMod q) depth) (hq : 3≤q) :
    ‖orderedCorrelation σ T1 T2 (residueTransform d q)‖≤(3:ℝ)^(2^depth) := by
  rw [orderedCorrelation_eq_slotCorrelation]
  exact slotCorrelation_universal_bound _ hm T1 T2 hq _ (actual_l2Sq_eq_one d).le

theorem orderedCorrelation_actual_good_haar (d : Decomposition)
    (σ : Equiv.Perm (Fin (2^depth)×Fin m)) (hm : 0 < m)
    (T1 T2 : Tree.Diagram (ZMod q) depth) (hq : 3≤q)
    (hgood : ¬Conclusion.TransferBadArrangement (haarPermutation σ)) :
    ‖orderedCorrelation σ T1 T2 (residueTransform d q)‖≤
      Tree.treeComparisonConstant (depth-2)*
        ((FiniteField.correlationBound (residueTransform d q):ℝ)+(q:ℝ)^(-(1/4:ℝ))) := by
  rw [orderedCorrelation_eq_slotCorrelation]
  exact slotCorrelation_transfer_good_bound _ hm T1 T2 hq hgood _
    (by simp only [residueTransform_eq,Supply.additiveTransform_zero]) (actual_l2Sq_eq_one d).le

end Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverage

end

end OAI
