import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Spec
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GapTemplate

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}
namespace NumericalLine
variable (w : NumericalLine D h ℓ)
def primeIndex (p : S.Index) (hp : p ∈ support w.linePrimeCode) : Fin (support w.linePrimeCode).card :=
  (FiniteSlotEncoding.enum (support w.linePrimeCode)).symm ⟨p,hp⟩
lemma values_primeIndex (p : S.Index) (hp : p ∈ support w.linePrimeCode) :
    values w.linePrimeCode (w.primeIndex p hp)=p := by
  exact congrArg Subtype.val ((FiniteSlotEncoding.enum (support w.linePrimeCode)).apply_symm_apply ⟨p,hp⟩)
lemma used_mem_support (p : S.Index) (hp : ∃ i, (p:ℕ) ∣ w.line.label i) :
    p ∈ support w.linePrimeCode := by
  rw [w.linePrimeCode_support]
  exact mem_filter.mpr ⟨mem_univ _,Or.inl hp⟩

def PackedGaps (L t : ℕ) : Prop :=
  ∃ a : S.FixedResidues w.line, NoFixedForbidden w.line D L a ∧ Nonempty (GapFamily w a L t)

structure GapCertificate (P : ℝ) where
  code : GapTemplate ℓ L ⌈C₀*Real.log B⌉₊ t (support w.linePrimeCode).card
  sign_eq : code.1=signBit w.line
  pattern_eq : code.2.1=pattern w.linePrimeCode
  formed : code.WellFormed h
  admissible : (code.system h formed).Admissible P 0 (fun i => (values w.linePrimeCode i:ℕ))
end NumericalLine

namespace GapFamily.Selection
variable {w : NumericalLine D h ℓ} {a : S.FixedResidues w.line} {F : GapFamily w a L t}
variable (q : F.Selection)

def selectedIndex (j : Fin t) : Fin (support w.linePrimeCode).card :=
  w.primeIndex (q.q j) (w.used_mem_support _ ⟨_,q.divides j⟩)
def modulusIndex (_ : F.Selection) (j : Fin t) : Fin (support w.linePrimeCode).card :=
  w.primeIndex (F.modulus j).val (w.used_mem_support _ (F.modulus j).property.1)
def template : GapTemplate ℓ L ⌈C₀*Real.log B⌉₊ t (support w.linePrimeCode).card :=
  ⟨signBit w.line,pattern w.linePrimeCode,fun j => (F.path j).code,q.selectedIndex,q.modulusIndex⟩

lemma selected_relabel (j : Fin t) : values w.linePrimeCode (q.template.selected j)=q.embedding j :=
  w.values_primeIndex _ _
lemma modulus_relabel (j : Fin t) : values w.linePrimeCode (q.template.modulus j)=q.tests.modulus j :=
  w.values_primeIndex _ _
lemma expression_relabel (j : Fin t) :
    (q.template.expression h j).relabel (values w.linePrimeCode)=q.tests.expression j := by
  change (PatternExpression.gap h (signBit w.line) (pattern w.linePrimeCode) (F.path j).code).relabel _=F.expression j
  rw [PatternExpression.gap_relabel]
  simp_rw [decode_pattern]
  exact F.pattern_source j
lemma formed : q.template.WellFormed h :=
  q.template.formed_of_relabel h (values w.linePrimeCode) q.embedding q.tests (fun _ => rfl)
    q.selected_relabel q.modulus_relabel q.expression_relabel
lemma template_admissible (P : ℝ) (hP : ∀ p : S.Index, P ≤ (p:ℝ))
    (hh : ∀ j, ¬((F.modulus j).val:ℕ) ∣ h) :
    (q.template.system h q.formed).Admissible P 0 (fun i => (values w.linePrimeCode i:ℕ)) :=
  q.template.admissible_of_relabel h q.formed (values w.linePrimeCode) q.embedding q.tests
    (fun _ => rfl) q.selected_relabel q.modulus_relabel q.expression_relabel P 0 (fun p => (p:ℕ))
    (q.admissible P 0 hP hh)
end GapFamily.Selection

namespace NumericalLine
variable (w : NumericalLine D h ℓ)
theorem packed_gap_certificate (P : ℝ) (hP : ∀ p : S.Index, P ≤ (p:ℝ))
    (hh : ∀ p : S.Index, ¬(p:ℕ) ∣ h) (hw : w.PackedGaps L t) :
    Nonempty (w.GapCertificate (L:=L) (t:=t) P) := by
  obtain ⟨a,ha,⟨F⟩⟩ := hw
  obtain ⟨q⟩ := F.selection_exists ha
  exact ⟨⟨q.template,rfl,rfl,q.formed,q.template_admissible P hP (fun j => hh _)⟩⟩

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
