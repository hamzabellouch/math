import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RepeatedCenterUnlitCount
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LineList

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter
namespace LineList

def geometryRetained {B τ C₀ : ℝ} {D : (sourceSystem B).DivisorFamily B τ C₀}
    {h ℓ n : ℕ} (hh : 0 < h) (K₀ : ℝ)
    (x : LineList D (pathLength B) h ℓ n) (a : (sourceSystem B).FixedResidues x.line) : Prop :=
  RetainedCountConditions x.line hh a B K₀

theorem source_retained_signed_sum (h : ℕ) (hh : 0 < h) (τ T C₀ K₀ A : ℝ)
    (hτ : 1 ≤ τ) (hC₀ : 0 ≤ C₀) (hK₀ : 0 ≤ K₀) (hA : 0 ≤ A) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      Real.exp (A*(sourceListSlotBudget C₀ B:ℝ)*Real.log B) *
        retainedSum (D:=D) (L:=pathLength B) (h:=h) (ℓ:=sourceLength B)
          (n:=listCutoff B) cut (geometryRetained hh K₀) ≤
          B^(-(1+2*eta)*(sourceLength B:ℝ)) := by
  filter_upwards [source_retained_token_count C₀ K₀ τ hC₀ hK₀,
    GlobalRecord.source_signed_record_summation h hh τ T C₀ A hτ hC₀ hA] with B ht hs
  intro D cut
  have hG (x : LineList D (pathLength B) h (sourceLength B) (listCutoff B))
      (a : (sourceSystem B).FixedResidues x.line) (ha : geometryRetained hh K₀ x a) :
      Fintype.card (TaggedSlot x.line hh x.primitives a) ≤ exceptionalBudget B := by
    have he := ht (sourceSystem B) D h (sourceLength B) x.line hh x.primitives a x.length_le ha
    have he' : (Fintype.card (TaggedSlot x.line hh x.primitives a):ℝ) ≤ B^(1-rho/2) := by
      exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans he
    have hc : (Fintype.card (TaggedSlot x.line hh x.primitives a):ℝ) ≤
        (⌈B^(1-rho/2)⌉₊:ℝ) := he'.trans (Nat.le_ceil _)
    exact_mod_cast hc
  exact (mul_le_mul_of_nonneg_left (retainedSum_le_global hh (geometryRetained hh K₀) cut hG)
    (Real.exp_pos _).le).trans (hs D cut)

end LineList
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
