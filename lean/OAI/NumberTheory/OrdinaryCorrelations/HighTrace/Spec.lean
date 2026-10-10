import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Splice
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeInjective
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LabelPrimeSetEraseProduct
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CoordinateEquiv
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CoefficientEqSingle

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.ArithmeticSaving Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}
namespace GapFamily
variable {w : NumericalLine D h ℓ} {a : S.FixedResidues w.line}
variable (F : GapFamily w a L t)

def spec (j : Fin t) : S.Specification D h L :=
  (F.path j).specification (F.modulus j).val ((F.path j).gap_prime_free a (F.uncut j) (F.modulus j) (F.gap j))
    ((F.path j).gap_div_displacement a (F.modulus j) (F.gap j))

def expression (j : Fin t) : SquarefreeExpression S.Index L :=
  (F.spec j).segmentExpression 0 (F.path j).length

lemma expression_eval (j : Fin t) :
    (F.expression j).eval (fun p => ((p:ℕ):ℤ)) =
      (F.path j).vertex (Fin.last (F.path j).length)-(F.path j).vertex 0 := by
  rw [expression,(F.spec j).segmentExpression_eval 0 (F.path j).length (Nat.zero_le _) le_rfl]
  simp [spec,TreePath.specification,Fin.last]

lemma expression_support {j : Fin t} {p : S.Index} (hp : p ∈ (F.expression j).support) :
    ∃ i, (p:ℕ) ∣ w.line.label ((F.path j).edge i) := by
  have hs := (F.spec j).segmentExpression_support 0 (F.path j).length hp
  obtain he|he := mem_insert.mp hs
  · have he' : p=(F.modulus j).val := Subtype.ext he
    subst p
    exact ((F.spec j).segmentExpression_extra_absent 0 (F.path j).length hp).elim
  · obtain ⟨i,_,hp⟩ := mem_biUnion.mp he
    exact ⟨i,(Nat.mem_primeFactors.mp hp).2.1⟩

structure Selection where
  edge : ∀ j, Fin (F.path j).length
  q : Fin t → S.Index
  divides : ∀ j, (q j:ℕ) ∣ w.line.label ((F.path j).edge (edge j))
  nonfixed : ∀ j, ¬S.IsFixed w.line (q j)
  injective : Function.Injective q
  absent : ∀ j k, j≠k → ∀ i, ¬(q j:ℕ) ∣ w.line.label ((F.path k).edge i)
  modulus_ne : ∀ j k, q j≠(F.modulus k).val

lemma selection_exists (hf : NoFixedForbidden w.line D L a) : Nonempty F.Selection := by
  obtain ⟨e,q,hd,hf,hi,ha,hm⟩ := F.select_singletons hf
  exact ⟨⟨e,q,hd,hf,hi,ha,hm⟩⟩

namespace Selection
variable {F} (q : F.Selection)
def embedding : Fin t ↪ S.Index := ⟨q.q,q.injective⟩

def tests : TriangularExpressions q.embedding L where
  expression := F.expression
  modulus j := (F.modulus j).val
  linear _ := true
  divisor_modulus _ hi := Bool.noConfusion hi
  divisor_own_absent _ hi := (Bool.noConfusion hi)
  linear_modulus_ne i _ := (q.modulus_ne i i).symm
  future_absent i j hij := by
    intro hp
    obtain he|he := mem_insert.mp hp
    · exact q.modulus_ne j i he
    · obtain ⟨k,hk⟩ := F.expression_support he
      exact q.absent j i (ne_of_gt hij) k hk

lemma coefficient_not_dvd (j : Fin t) (hh : ¬((F.modulus j).val:ℕ) ∣ h) :
    ¬(((F.modulus j).val:ℕ):ℤ) ∣ (F.expression j).linearCoeff (q.q j) (fun p => ((p:ℕ):ℤ)) := by
  rw [expression,(F.spec j).segmentExpression_coefficient 0 (F.path j).length le_rfl (q.q j)]
  exact (F.spec j).singleton_coefficient_not_dvd (q.q j) (q.edge j)
    ((F.path j).nonfixed_unique_on_path (q.q j) (q.nonfixed j) (q.edge j) (q.divides j)) hh

lemma admissible (P K : ℝ) (hP : ∀ p : S.Index, P ≤ (p:ℝ))
    (hh : ∀ j, ¬((F.modulus j).val:ℕ) ∣ h) :
    q.tests.Admissible P K (fun p => (p:ℕ)) := by
  intro j
  change Nat.Prime ((F.modulus j).val:ℕ) ∧ P ≤ ((F.modulus j).val:ℝ) ∧ _
  refine ⟨S.prime_mem _ (F.modulus j).val.property,hP _,q.coefficient_not_dvd j (hh j),?_⟩
  change (((F.modulus j).val:ℕ):ℤ) ∣
    (F.expression j).linearCoeff (q.q j) (fun p => ((p:ℕ):ℤ)) * ((q.q j:ℕ):ℤ) +
      (F.expression j).constantTerm (q.q j) (fun p => ((p:ℕ):ℤ))
  rw [←(F.expression j).eval_affine (q.q j),F.expression_eval]
  exact (F.path j).gap_div_displacement a (F.modulus j) (F.gap j)

end Selection
end GapFamily
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
