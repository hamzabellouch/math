import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UncutTreeEdges

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}
namespace TreePath
variable {w : NumericalLine D h ℓ}

lemma edge_injective (P : TreePath w L) : Function.Injective P.edge := by
  intro i j hij
  have hi := P.endpoints i
  have hj := P.endpoints j
  rw [←hij] at hj
  cases hfi : P.forward i <;> cases hfj : P.forward j <;>
    simp only [hfi,hfj,Bool.false_eq_true,ite_false,ite_true] at hi hj
  · have he := P.distinct (hi.1.trans hj.1.symm)
    exact Fin.ext (congrArg (fun k : Fin (P.length+1) => k.val) he)
  · have he := P.distinct (hi.1.trans hj.2.symm)
    have hf := P.distinct (hi.2.trans hj.1.symm)
    have he' := congrArg Fin.val he
    have hf' := congrArg Fin.val hf
    simp only [Fin.val_castSucc,Fin.val_succ] at he' hf'
    omega
  · have he := P.distinct (hi.1.trans hj.2.symm)
    have hf := P.distinct (hi.2.trans hj.1.symm)
    have he' := congrArg Fin.val he
    have hf' := congrArg Fin.val hf
    simp only [Fin.val_castSucc,Fin.val_succ] at he' hf'
    omega
  · have he := P.distinct (hi.1.trans hj.1.symm)
    exact Fin.ext (congrArg (fun k : Fin (P.length+1) => k.val) he)

lemma nonfixed_unique_on_path (P : TreePath w L) (q : S.Index)
    (hq : ¬S.IsFixed w.line q) (i : Fin P.length) (hi : (q:ℕ) ∣ w.line.label (P.edge i)) :
    ∀ j, (q:ℕ) ∣ w.line.label (P.edge j) ↔ j=i := by
  intro j
  rw [unique_occurrence_of_free w.line q hq (P.edge i) hi (P.edge j)]
  exact P.edge_injective.eq_iff
end TreePath

structure GapFamily (w : NumericalLine D h ℓ) (a : S.FixedResidues w.line) (L t : ℕ) where
  path : Fin t → TreePath w L
  modulus : Fin t → S.FixedIndex w.line
  gap : ∀ j, (path j).IsGap a (modulus j)
  uncut : ∀ j i, (path j).edge i ∈ uncutTreeEdges w.line a
  disjoint : ∀ j k, j≠k → ∀ i n, (path j).edge i ≠ (path k).edge n

namespace GapFamily
variable {w : NumericalLine D h ℓ} {a : S.FixedResidues w.line} {t : ℕ}
variable (F : GapFamily w a L t)

theorem select_singletons (hf : NoFixedForbidden w.line D L a) :
    ∃ (edge : ∀ j, Fin (F.path j).length) (q : Fin t → S.Index),
      (∀ j, (q j:ℕ) ∣ w.line.label ((F.path j).edge (edge j))) ∧
      (∀ j, ¬S.IsFixed w.line (q j)) ∧ Function.Injective q ∧
      (∀ j k, j≠k → ∀ i, ¬(q j:ℕ) ∣ w.line.label ((F.path k).edge i)) ∧
      (∀ j k, q j≠(F.modulus k).val) := by
  have hw (j : Fin t) := (F.path j).gap_has_nonfixed a (F.uncut j) hf (F.modulus j) (F.gap j)
  choose e q hdiv hfree using hw
  have habsent : ∀ j k, j≠k → ∀ i, ¬(q j:ℕ) ∣ w.line.label ((F.path k).edge i) := by
    intro j k hne i hi
    have he := (unique_occurrence_of_free w.line (q j) (hfree j)
      ((F.path j).edge (e j)) (hdiv j) ((F.path k).edge i)).mp hi
    exact F.disjoint j k hne (e j) i he.symm
  refine ⟨e,q,hdiv,hfree,?_,habsent,?_⟩
  · intro j k he
    by_contra hne
    apply habsent j k hne (e k)
    rw [he]
    exact hdiv k
  · intro j k he
    exact hfree j (he ▸ (F.modulus k).property)

end GapFamily
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
