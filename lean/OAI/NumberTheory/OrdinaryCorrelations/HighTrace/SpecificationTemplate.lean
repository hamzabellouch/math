import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CoordinateEquiv
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SpecSegment

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns
open Finset Classical

abbrev SpecificationTemplate (L J m : ℕ) :=
  SpecMetadata L × (SpecCodeSlot L J → Option (Fin m)) × Fin m

namespace SpecificationTemplate
variable {L J m : ℕ}
noncomputable def expression (d : SpecificationTemplate L J m) (h : ℕ) :
    SquarefreeExpression (Fin m) L :=
  PatternExpression.specSegment h d.1 d.2.1 d.1.2.2.val d.1.1.val

def selected (d : SpecificationTemplate L J m) : Fin 1 ↪ Fin m :=
  ⟨fun _ => d.2.2,fun _ _ _ => Subsingleton.elim _ _⟩

def WellFormed (d : SpecificationTemplate L J m) (h : ℕ) : Prop :=
  d.2.2 ∉ (d.expression h).support

noncomputable def system (d : SpecificationTemplate L J m) (h : ℕ) (hd : d.WellFormed h) :
    TriangularExpressions d.selected L where
  expression _ := d.expression h
  modulus _ := d.2.2
  linear _ := false
  divisor_modulus _ _ := rfl
  divisor_own_absent _ _ := hd
  linear_modulus_ne _ hi := Bool.noConfusion hi
  future_absent i j hij := by have : i=j := Subsingleton.elim _ _; subst j; exact (lt_irrefl _ hij).elim
end SpecificationTemplate

variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}

instance : Finite (S.Specification D h L) := by
  apply Finite.of_injective (fun s : S.Specification D h L => (specMetadata s,specPrimeCode s))
  intro s t he
  exact specification_code_injective s t (congrArg Prod.fst he) (congrArg Prod.snd he)
noncomputable instance : Fintype (S.Specification D h L) := Fintype.ofFinite _

namespace Specification
variable (s : S.Specification D h L)

noncomputable def extraName : Fin (support (specPrimeCode s)).card :=
  (FiniteSlotEncoding.enum (support (specPrimeCode s))).symm
    ⟨s.extra,(mem_support _ _).mpr ⟨none,rfl⟩⟩

lemma values_extraName : values (specPrimeCode s) s.extraName=s.extra := by
  change ((FiniteSlotEncoding.enum (support (specPrimeCode s)))
    ((FiniteSlotEncoding.enum (support (specPrimeCode s))).symm _)).val=s.extra
  rw [Equiv.apply_symm_apply]

noncomputable def codeTemplate :
    SpecificationTemplate L ⌈C₀*Real.log B⌉₊ (support (specPrimeCode s)).card :=
  (specMetadata s,pattern (specPrimeCode s),s.extraName)

lemma codeTemplate_expression :
    (s.codeTemplate.expression h).relabel (values (specPrimeCode s)) =
      s.segmentExpression s.suffix.val s.length := by
  unfold codeTemplate SpecificationTemplate.expression
  rw [PatternExpression.specSegment_relabel]
  simp_rw [decode_pattern]
  exact PatternExpression.specSegment_source _ _ _

lemma codeTemplate_formed : s.codeTemplate.WellFormed h := by
  intro hp
  apply s.segmentExpression_extra_absent s.suffix.val s.length
  rw [←s.codeTemplate_expression,SquarefreeExpression.support_relabel]
  exact mem_image.mpr ⟨s.extraName,hp,s.values_extraName⟩

noncomputable def densitySize (B C₀ : ℝ) (h L : ℕ) : ℝ :=
  Real.log ((L:ℝ)*h*Real.exp (B*⌈C₀*Real.log B⌉₊)+2)

lemma densitySize_nonneg : 0 ≤ densitySize B C₀ h L := by
  apply Real.log_nonneg
  have : 0 ≤ (L:ℝ)*h*Real.exp (B*⌈C₀*Real.log B⌉₊) := by positivity
  linarith

lemma suffix_log_size (hB : 0 ≤ B) (hS : ∀ p : S.Index, (p:ℝ) ≤ Real.exp B) :
    Real.log (|((s.segmentExpression s.suffix.val s.length).eval (fun p => ((p:ℕ):ℤ)):ℝ)|+2) ≤
      densitySize B C₀ h L := by
  apply Real.log_le_log (by positivity)
  have hb := SquarefreeExpression.abs_eval_le (s.segmentExpression s.suffix.val s.length)
    ⌈C₀*Real.log B⌉₊ B (h:ℝ) hB (Nat.cast_nonneg h)
    (s.segmentExpression_factor_card _ _) (s.segmentExpression_coeff_bound _ _)
    (fun p => ((p:ℕ):ℤ)) (by intro p hp; simpa using hS p)
  linarith only [hb]

lemma codeTemplate_admissible (P : ℝ) (hB : 0 ≤ B)
    (hS : ∀ p : S.Index, (p:ℝ) ≤ Real.exp B) :
    (s.codeTemplate.system h s.codeTemplate_formed).Admissible P (densitySize B C₀ h L)
      (fun a => (values (specPrimeCode s) a:ℕ)) := by
  intro i
  change (ArithmeticClause.divisor ((s.codeTemplate.expression h).eval
      (fun a => ((values (specPrimeCode s) a:ℕ):ℤ)))).Holds P _
        (values (specPrimeCode s) s.extraName:ℕ)
  rw [←SquarefreeExpression.eval_relabel _ (values (specPrimeCode s)) (fun p => ((p:ℕ):ℤ)),
    s.codeTemplate_expression,s.values_extraName]
  change _ ≠ 0 ∧ _ ∧ _
  refine ⟨?_,s.suffix_log_size hB hS,?_⟩
  · rw [s.segmentExpression_eval _ _ (Nat.le_of_lt s.suffix.isLt) le_rfl]
    intro hz
    have hv := congrArg Fin.val (s.offsets_distinct (sub_eq_zero.mp hz))
    have hi := s.suffix.isLt
    dsimp only at hv
    omega
  · rw [s.segmentExpression_eval _ _ (Nat.le_of_lt s.suffix.isLt) le_rfl]
    exact s.extra_div_suffix
end Specification

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
