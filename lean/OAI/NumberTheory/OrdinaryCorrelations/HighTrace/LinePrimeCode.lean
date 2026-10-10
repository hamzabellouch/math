import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AmplitudeGeOne
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.NumericalLine
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TotalCodeMass

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.SharedSlotPatterns OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ : ℕ}
namespace NumericalLine

def linePrimeCode (w : NumericalLine D h ℓ) : (Fin ℓ × Fin ⌈C₀*Real.log B⌉₊) → Option S.Index :=
  fun k => FiniteSlotEncoding.code (labelPrimeSet (w.line.label k.1) (w.labels k.1)) ⌈C₀*Real.log B⌉₊ k.2

def basicCode (w : NumericalLine D h ℓ) := (signBit w.line,linePrimeCode w)
lemma basicCode_injective : Function.Injective (basicCode : NumericalLine D h ℓ → _) := by
  intro w v he
  have hl : w.line=v.line := by
    apply GlobalRecord.line_eq_of_labels_signs
    · funext i
      have hs : labelPrimeSet (w.line.label i) (w.labels i)=labelPrimeSet (v.line.label i) (v.labels i) := by
        apply FiniteSlotEncoding.code_injective (m:=⌈C₀*Real.log B⌉₊)
        · rw [labelPrimeSet_card]; exact D.omega _ (w.labels i)
        · rw [labelPrimeSet_card]; exact D.omega _ (v.labels i)
        · funext j
          exact congrFun (congrArg Prod.snd he) (i,j)
      rw [←labelPrimeSet_product (w.line.label i) (w.labels i),
        ←labelPrimeSet_product (v.line.label i) (v.labels i),hs]
    · funext i
      have hs : signBit w.line i=signBit v.line i := congrFun (congrArg Prod.fst he) i
      rw [signBit_decode w.line i,signBit_decode v.line i,hs]
  cases w
  cases v
  cases hl
  rfl

lemma linePrimeCode_support (w : NumericalLine D h ℓ) :
    support w.linePrimeCode=fullUsedIndices w.line ([] : List (AttachedSpec w.line D 0)) := by
  ext p
  simp only [mem_support,fullUsedIndices,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨⟨i,j⟩,hj⟩
    left
    refine ⟨i,?_⟩
    have hp := (FiniteSlotEncoding.code_mem _ _ j p hj)
    exact (Nat.mem_primeFactors.mp ((mem_labelPrimeSet _ _ _).mp hp)).2.1
  · rintro (⟨i,hi⟩ | hp)
    · have hm : (labelPrimeSet (w.line.label i) (w.labels i)).card ≤ ⌈C₀*Real.log B⌉₊ := by
        rw [labelPrimeSet_card]; exact D.omega _ (w.labels i)
      obtain ⟨j,hj⟩ := (FiniteSlotEncoding.mem_iff_code _ _ hm p).mp ((mem_labelPrimeSet _ _ _).mpr
        (Nat.mem_primeFactors.mpr ⟨S.prime_mem p p.property,hi,(w.line.label_pos i).ne'⟩))
      exact ⟨(i,j),hj⟩
    · simp [listSupport] at hp

def lineReciprocalWeight (w : NumericalLine D h ℓ) : ℝ :=
  ∏ p ∈ support w.linePrimeCode, (p:ℝ)⁻¹

def lineMassBound (S : PrimeSystem) (ℓ J : ℕ) : ℝ :=
  2^ℓ*(ℓ*J+1:ℝ)*(ℓ*J+1:ℝ)^(ℓ*J)*(max 1 (∑ p : S.Index,(p:ℝ)⁻¹))^(ℓ*J)

lemma sum_lineReciprocalWeight_le :
    (∑ w : NumericalLine D h ℓ, w.lineReciprocalWeight) ≤ lineMassBound S ℓ ⌈C₀*Real.log B⌉₊ := by
  have hn (x : (Fin ℓ → Bool) × ((Fin ℓ × Fin ⌈C₀*Real.log B⌉₊) → Option S.Index)) :
      0 ≤ ∏ p ∈ support x.2, (p:ℝ)⁻¹ := prod_nonneg (fun p _ => by positivity)
  calc
    _ = ∑ c ∈ univ.image basicCode, ∏ p ∈ support c.2, (p:ℝ)⁻¹ := by
      rw [sum_image (fun w _ v _ he => basicCode_injective he)]
      rfl
    _ ≤ ∑ c : (Fin ℓ → Bool) × ((Fin ℓ × Fin ⌈C₀*Real.log B⌉₊) → Option S.Index),
        ∏ p ∈ support c.2, (p:ℝ)⁻¹ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun c _ _ => hn c)
    _ = 2^ℓ * ∑ c : (Fin ℓ × Fin ⌈C₀*Real.log B⌉₊) → Option S.Index, ∏ p ∈ support c,(p:ℝ)⁻¹ := by
      rw [Fintype.sum_prod_type]
      simp
    _ ≤ _ := by
      unfold lineMassBound
      simp only [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 2^ℓ)
      have hb := total_code_mass (σ:=Fin ℓ × Fin ⌈C₀*Real.log B⌉₊)
        (fun p : S.Index => (p:ℝ)⁻¹) (fun p => by positivity)
      simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,mul_assoc] at hb
      convert hb using 1
      congr 1
      congr 1
      exact Subsingleton.elim _ _

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
