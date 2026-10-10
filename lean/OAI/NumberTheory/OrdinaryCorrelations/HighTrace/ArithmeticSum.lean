import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LineList
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RetainedKernel
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AffineResidueEquiv
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GeometryRetained

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
open Finset Classical Filter
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {L h ℓ n : ℕ}
namespace LineList

noncomputable def arithmeticSum {T : ℝ} (cut : S.Cutoffs T)
    (G : (x : LineList D L h ℓ n) → S.FixedResidues x.line → Prop)
    (q : ℕ) (z : ℝ → ℤ) (X : ℝ) : ℝ :=
  ∑ x : LineList D L h ℓ n,
    |(∑ m ∈ range ⌊X⌋₊, retainedKernel x.line cut x.primitives (G x)
      (S.integerResidues (q*(m:ℤ)+z X)))/X|

lemma arithmeticSum_tendsto {T : ℝ} (cut : S.Cutoffs T)
    (G : (x : LineList D L h ℓ n) → S.FixedResidues x.line → Prop)
    (q : ℕ) (hq : ∀ p : S.Index, Nat.Coprime q (p:ℕ)) (z : ℝ → ℤ) :
    Tendsto (arithmeticSum cut G q z) atTop
      (𝓝 (∑ x : LineList D L h ℓ n, |avg (retainedKernel x.line cut x.primitives (G x))|)) := by
  unfold arithmeticSum
  apply tendsto_finsetSum
  intro x hx
  exact (S.real_affine_origin_tendsto (retainedKernel x.line cut x.primitives (G x)) q hq z).abs

lemma arithmeticLimit_le_retainedSum {T : ℝ} (cut : S.Cutoffs T)
    (G : (x : LineList D L h ℓ n) → S.FixedResidues x.line → Prop) :
    (∑ x : LineList D L h ℓ n, |avg (retainedKernel x.line cut x.primitives (G x))|) ≤
      retainedSum cut G := by
  exact sum_le_sum (fun x hx => retainedKernel_avg_le x.line cut x.primitives (G x))

theorem source_retained_arithmetic_sum (h q : ℕ) (hh : 0 < h) (hq : 0 < q)
    (τ T C₀ K₀ A : ℝ) (hτ : 1 ≤ τ) (hC₀ : 0 ≤ C₀) (hK₀ : 0 ≤ K₀) (hA : 0 ≤ A) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T) (z : ℝ → ℤ) (δ : ℝ), 0 < δ →
      ∀ᶠ X : ℝ in atTop,
      Real.exp (A*(sourceListSlotBudget C₀ B:ℝ)*Real.log B) *
        arithmeticSum (D:=D) (L:=pathLength B) (h:=h) (ℓ:=sourceLength B)
          (n:=listCutoff B) cut (geometryRetained hh K₀) q z X ≤
          B^(-(1+2*eta)*(sourceLength B:ℝ)) + δ := by
  filter_upwards [source_retained_signed_sum h hh τ T C₀ K₀ A hτ hC₀ hK₀ hA,
    source_eventually_coprime q hq] with B hs hcop
  intro D cut z δ hδ
  let E := Real.exp (A*(sourceListSlotBudget C₀ B:ℝ)*Real.log B)
  have he : 0 ≤ E := (Real.exp_pos _).le
  have hl := (arithmeticSum_tendsto (D:=D) (ℓ:=sourceLength B) (n:=listCutoff B)
    cut (geometryRetained hh K₀) q hcop z).const_mul E
  have hb := (mul_le_mul_of_nonneg_left
    (arithmeticLimit_le_retainedSum (D:=D) (ℓ:=sourceLength B) (n:=listCutoff B)
      cut (geometryRetained hh K₀)) he).trans (hs D cut)
  exact hl.eventually (eventually_le_nhds (lt_of_le_of_lt hb (lt_add_of_pos_right _ hδ)))

end LineList
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
