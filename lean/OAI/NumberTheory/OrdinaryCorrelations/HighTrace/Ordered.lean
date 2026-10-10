import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrivateFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Splice
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Precedes
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Symbolic
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ActivityResidue
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CoordinateEquiv

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ n : ℕ}
namespace PrivateFamily
variable {w : ClosedLine h ℓ} {F : PrivateFamily w D L n}

noncomputable def Case.ordered (c : Case) (A : Finset (Fin n)) : Fin A.card ≃ A :=
  match c with
  | .intrinsic | .first | .before => (A.orderIsoOfFin rfl).toEquiv
  | .last | .after => Fin.revPerm.trans (A.orderIsoOfFin rfl).toEquiv

lemma Case.ordered_precedes (c : Case) (A : Finset (Fin n)) {i j : Fin A.card} (hij : i<j) :
    c.Precedes (c.ordered A i).val (c.ordered A j).val := by
  cases c with
  | intrinsic | first | before => exact (A.orderIsoOfFin rfl).strictMono hij
  | last | after => exact (A.orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.mpr hij)

namespace Test
variable {j : Fin n}
lemma modulus_mem (t : F.Test j) : (t.modulus:ℕ) ∈ t.support := by
  cases t with
  | extra | tail => exact mem_insert_self _ _
  | compare i q r hi => exact mem_union_left _ (mem_union_left _ hi)

lemma modulus_eq_selected (t : F.Test j) (ht : ¬t.Linear) : t.modulus=t.selected := by
  cases t with
  | extra => rfl
  | tail q => exact (ht trivial).elim
  | compare i q r hi => exact (ht trivial).elim
end Test

noncomputable def testEmbedding (c : Case) (A : Finset (Fin n))
    (t : ∀ j : A, F.Test j.val) (hinj : Function.Injective (fun j => (t j).selected)) :
    Fin A.card ↪ S.Index where
  toFun i := (t (c.ordered A i)).selected
  inj' := hinj.comp (c.ordered A).injective

noncomputable def testSystem (hl : ∀ i, w.label i ∈ D.members)
    (c : Case) (A : Finset (Fin n)) (t : ∀ j : A, F.Test j.val)
    (ht : ∀ j, (t j).Valid) (hinj : Function.Injective (fun j => (t j).selected))
    (hfuture : ∀ i j : A, c.Precedes i.val j.val → ((t j).selected:ℕ) ∉ (t i).support) :
    TriangularExpressions (testEmbedding c A t hinj) ((ℓ+L)+L) where
  expression i := (t (c.ordered A i)).symbolic hl
  modulus i := (t (c.ordered A i)).modulus
  linear i := decide (t (c.ordered A i)).Linear
  divisor_modulus i hi := (t (c.ordered A i)).modulus_eq_selected (of_decide_eq_false hi)
  divisor_own_absent i hi := (t (c.ordered A i)).symbolic_own_absent hl (of_decide_eq_false hi)
  linear_modulus_ne i hi := (t (c.ordered A i)).modulus_ne_selected (ht _) (of_decide_eq_true hi)
  future_absent i j hij := by
    intro hp
    have hf := hfuture (c.ordered A i) (c.ordered A j) (c.ordered_precedes A hij)
    rcases mem_insert.mp hp with hp|hp
    · change (t (c.ordered A j)).selected=(t (c.ordered A i)).modulus at hp
      exact hf (by rw [hp]; exact Test.modulus_mem _)
    · exact hf ((t (c.ordered A i)).symbolic_support hl hp)

noncomputable def testSize (B : ℝ) (C₀ : ℝ) (h ℓ L : ℕ) : ℝ :=
  Real.log ((((ℓ+L)+L:ℕ):ℝ)*h*Real.exp (B*⌈C₀*Real.log B⌉₊)+2)

lemma testSize_nonneg (B C₀ : ℝ) (h ℓ L : ℕ) : 0 ≤ testSize B C₀ h ℓ L := by
  apply Real.log_nonneg
  have hn : 0 ≤ (((ℓ+L+L:ℕ):ℝ)*h*Real.exp (B*⌈C₀*Real.log B⌉₊)) := by positivity
  linarith

lemma Test.log_symbolic_size {j : Fin n} (t : F.Test j)
    (hl : ∀ i, w.label i ∈ D.members) (hB : 0 ≤ B) (x : S.Index → ℕ)
    (hx : ∀ p, (x p:ℝ) ≤ Real.exp B) :
    Real.log (|((t.symbolic hl).eval (fun p => (x p:ℤ)):ℝ)|+2) ≤ testSize B C₀ h ℓ L := by
  apply Real.log_le_log (by positivity)
  have hb := t.symbolic_size hl hB x hx
  simp only [Nat.cast_add]
  linarith only [hb]

lemma testSystem_admissible (hl : ∀ i, w.label i ∈ D.members)
    (c : Case) (A : Finset (Fin n)) (t : ∀ j : A, F.Test j.val)
    (ht : ∀ j, (t j).Valid) (hinj : Function.Injective (fun j => (t j).selected))
    (hfuture : ∀ i j : A, c.Precedes i.val j.val → ((t j).selected:ℕ) ∉ (t i).support)
    (hnd : ∀ j, if (t j).Linear then ¬(((t j).modulus:ℕ):ℤ) ∣ (t j).coefficient
      else (t j).expression ≠ 0)
    (hB : 0 ≤ B) (P : ℝ) (hP : ∀ p : S.Index, P ≤ (p:ℝ))
    (hupper : ∀ p : S.Index, (p:ℝ) ≤ Real.exp B)
    (r : S.Residues) (hq : ∀ i p, (F.witness i).spec.ResidueTest p (F.witness i).vertex (r p)) :
    (testSystem hl c A t ht hinj hfuture).Admissible P (testSize B C₀ h ℓ L) (fun p => (p:ℕ)) := by
  intro i
  let tj := t (c.ordered A i)
  have hd : ((tj.modulus:ℕ):ℤ) ∣ tj.expression := tj.holds_residues (ht _) r hq
  have hn : if tj.Linear then ¬((tj.modulus:ℕ):ℤ) ∣ tj.coefficient else tj.expression ≠ 0 :=
    hnd (c.ordered A i)
  change (if decide tj.Linear then
      ArithmeticClause.linear ((tj.symbolic hl).linearCoeff tj.selected (fun p => ((p:ℕ):ℤ)))
        ((tj.symbolic hl).constantTerm tj.selected (fun p => ((p:ℕ):ℤ))) (tj.modulus:ℕ)
    else ArithmeticClause.divisor ((tj.symbolic hl).eval (fun p => ((p:ℕ):ℤ)))).Holds P _ (tj.selected:ℕ)
  by_cases hlin : tj.Linear
  · rw [ite_eq_left (decide_eq_true hlin)]
    change Nat.Prime (tj.modulus:ℕ) ∧ P ≤ (tj.modulus:ℝ) ∧ _
    refine ⟨S.prime_mem _ tj.modulus.property,hP _,?_,?_⟩
    · rw [tj.symbolic_coefficient hl]
      simpa only [ite_eq_left hlin] using hn
    · rw [←(tj.symbolic hl).eval_affine tj.selected, tj.symbolic_eval hl]
      exact hd
  · rw [ite_eq_right (by simpa using hlin)]
    change (tj.symbolic hl).eval (fun p => ((p:ℕ):ℤ)) ≠ 0 ∧ _
    refine ⟨?_,tj.log_symbolic_size hl hB _ hupper,?_⟩
    · rw [tj.symbolic_eval hl]
      simpa only [ite_eq_right hlin] using hn
    · rw [tj.symbolic_eval hl,←tj.modulus_eq_selected hlin]
      exact hd

end PrivateFamily
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
