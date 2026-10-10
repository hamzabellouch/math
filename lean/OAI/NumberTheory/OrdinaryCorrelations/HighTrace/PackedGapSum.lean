import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeSplit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TiltedListLocalMean
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GoodGapTemplate
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GapFilling

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open OrdinaryCorrelations.NumericalSubtrees Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}
namespace NumericalLine

def packedGapSum {T : ℝ} (D : S.DivisorFamily B τ C₀) (h ℓ L t : ℕ)
    (cut : S.Cutoffs T) : ℝ :=
  ∑ w : NumericalLine D h ℓ, avg (fun r : S.Residues =>
    if NoFixedForbidden w.line D L (S.binarySplit w.line r).1 ∧
      Nonempty (GapFamily w (S.binarySplit w.line r).1 L t) then
        |S.chronologicalKernel w.line cut r*allowedIndicator w.line D L r| else 0)

lemma line_absolute_integral {T : ℝ} (w : NumericalLine D h ℓ) (cut : S.Cutoffs T) :
    avg (fun r : S.Residues => |S.chronologicalKernel w.line cut r*allowedIndicator w.line D L r|) ≤
      (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*w.lineReciprocalWeight := by
  have hp : ∀ p : S.Index, (1:ℝ)^2 ≤ (p:ℝ) := by
    intro p
    norm_num only [one_pow]
    exact_mod_cast (S.prime_mem p p.property).one_lt.le
  have hh := repeated_unlit_tail_integral w.line w.labels cut
    ([] : List (AttachedSpec w.line D 0)) 1 le_rfl hp 0
  simp only [Nat.zero_le,ite_true,one_pow,mul_one] at hh
  have hc : (fullUsedIndices w.line ([] : List (AttachedSpec w.line D 0))).card ≤ ℓ*⌈C₀*Real.log B⌉₊ := by
    simpa using fullUsedIndices_card_le w.line ([] : List (AttachedSpec w.line D 0)) w.labels
  calc
    _ ≤ avg (fun r : S.Residues => |S.kernel w.line cut r| *listIndicator w.line ([] : List (AttachedSpec w.line D 0)) r) := by
      apply avg_mono
      intro r
      rw [chronologicalKernel_eq]
      have hi : listIndicator w.line ([] : List (AttachedSpec w.line D 0)) r=1 := by simp [listIndicator]
      rw [hi,mul_one]
      unfold allowedIndicator
      split_ifs <;> simp
    _ ≤ _ := hh
    _ ≤ _ := by
      rw [lineReciprocalWeight,linePrimeCode_support]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg A_pos.le _)
      exact pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg ℓ : (0:ℝ) ≤ (ℓ:ℝ))] : 1 ≤ (ℓ:ℝ)+2) hc

lemma packedGapSum_le_mass {T : ℝ} (cut : S.Cutoffs T) :
    packedGapSum D h ℓ L t cut ≤
      (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*packedGapMass D h ℓ L t := by
  unfold packedGapSum packedGapMass
  rw [mul_sum,GlobalRecord.subtype_sum_as_ite (fun w : NumericalLine D h ℓ => w.PackedGaps L t)
    (fun w => (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*w.lineReciprocalWeight)]
  apply sum_le_sum
  intro w hw
  by_cases hpack : w.PackedGaps L t
  · rw [ite_eq_left hpack]
    apply le_trans _ (w.line_absolute_integral (L:=L) cut)
    apply avg_mono
    intro r
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  · rw [ite_eq_right hpack]
    apply le_of_eq
    calc
      _ = avg (fun _ : S.Residues => (0:ℝ)) := by
        congr 1
        funext r
        apply ite_eq_right
        intro hr
        exact hpack ⟨(S.binarySplit w.line r).1,hr⟩
      _ = 0 := by simp [avg]

theorem packedGapSum_bound {T : ℝ} (cut : S.Cutoffs T)
    (P U : ℝ) (hP : 0 < P) (hU : 0 ≤ U)
    (hS : ∀ p : S.Index,P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp U)
    (hh : ∀ p : S.Index,¬(p:ℕ) ∣ h) :
    packedGapSum D h ℓ L t cut ≤
      (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*
      ((gapTemplateBudget ℓ L ⌈C₀*Real.log B⌉₊ t:ℝ)*
        (max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹))^(ℓ*⌈C₀*Real.log B⌉₊)*((2+U)/P)^t) := by
  apply (packedGapSum_le_mass cut).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity [A_pos])
  exact (packedGapMass_le_templateMass P (fun p => (hS p).1) hh).trans
    (gapTemplateMass_le S P U h ℓ L ⌈C₀*Real.log B⌉₊ t hP hU hS)

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
