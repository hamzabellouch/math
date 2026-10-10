import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetSampled
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationResidueValidity

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval TemplateOneSidedBudget
open HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

def naturalResidueModulus (g : List (ResidueGuard ι)) : ℕ := (residueModulus g).natAbs

theorem naturalResidueModulus_pos (g : List (ResidueGuard ι))
    (hg : ∀ q ∈ g, q.Valid) : 0 < naturalResidueModulus g :=
  Int.natAbs_pos.mpr (residueModulus_ne_zero g hg)

theorem residueGuards_natural_progression [DecidableEq ι]
    (g : List (ResidueGuard ι)) (hg : ∀ q ∈ g, q.Valid)
    (i : ι) (x : Other i → ℤ) (r n : ℕ) :
    (∀ q ∈ g, q.holds (insertCoordinate i x ((naturalResidueModulus g*n+r:ℕ):ℤ))) ↔
      (∀ q ∈ g, q.holds (insertCoordinate i x (r:ℤ))) := by
  apply residueGuards_iff_of_modEq g hg
  intro j
  by_cases hj : j=i
  · subst j
    simp only [insertCoordinate_self,Nat.cast_add,Nat.cast_mul]
    apply Int.modEq_iff_dvd.mpr
    have hd : residueModulus g ∣ (naturalResidueModulus g:ℤ) :=
      Int.dvd_natCast.mpr (dvd_refl _)
    have hh := dvd_mul_of_dvd_left hd (-(n:ℤ))
    convert hh using 1; ring
  · simp only [insertCoordinate,hj,dite_false]
    exact Int.ModEq.refl _

theorem sampled_frequencyArithmetic_natural_progression (k j : ℕ) (width : Role → ℕ)
    (a m : ℝ) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a m j) j [] s t)
    (i : (schedule k j).Constituent width)
    (x : Other i → ℤ) (r n : ℕ) :
    let e := sampledExpressions k j width
    let Q := naturalResidueModulus (historyResidueGuards k j s e t)
    frequencyArithmetic k (fun l => (bound a m l:ℤ)) j s
      (evalExpressions (insertCoordinate i x ((Q*n+r:ℕ):ℤ)) e) t ↔
    frequencyArithmetic k (fun l => (bound a m l:ℤ)) j s
      (evalExpressions (insertCoordinate i x (r:ℤ)) e) t := by
  dsimp only
  have hf := actual_historyFrequencyBounds a m j j [] (by simp) s t ht
  have hv := historyResidueGuards_valid k (fun l => (bound a m l:ℤ)) j s
    (sampledExpressions k j width) t
    (fun u => (sampledExpressions_good k j width (fun _ => 0) u).1) hf
  rw [← historyResidueGuards_holds k _ j s _ t _
    (sampledExpressions_good k j width _) hf]
  rw [← historyResidueGuards_holds k _ j s _ t _
    (sampledExpressions_good k j width _) hf]
  exact residueGuards_natural_progression _ hv i x r n

theorem sampled_naturalResidueModulus_pos (k j : ℕ) (width : Role → ℕ)
    (a m : ℝ) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a m j) j [] s t) :
    0 < naturalResidueModulus (historyResidueGuards k j s (sampledExpressions k j width) t) := by
  apply naturalResidueModulus_pos
  exact historyResidueGuards_valid k (fun l => (bound a m l:ℤ)) j s _ t
    (fun u => (sampledExpressions_good k j width (fun _ => 0) u).1)
    (actual_historyFrequencyBounds a m j j [] (by simp) s t ht)

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
