import OAI.Probability.BenjaminiSchramm.MinimumHeightHit
import OAI.Probability.BenjaminiSchramm.UpperLayerSecondMoment
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma lintegral_support_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ≥0∞) (hf : Measurable f)
    (A : Set Ω) (hA : MeasurableSet A) (hzero : ∀ ω, ω ∉ A → f ω=0) :
    (∫⁻ ω, f ω ∂μ)^2 ≤ μ A*(∫⁻ ω, (f ω)^2 ∂μ) := by
  let g := A.indicator (fun _ => (1 : ℝ≥0∞))
  have hg : Measurable g := measurable_const.indicator hA
  have hfg : (fun ω => f ω*g ω)=f := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [g,Set.indicator_of_mem hω,mul_one]
    · simp only [g,Set.indicator_of_notMem hω,mul_zero,hzero ω hω]
  have hgg : (fun ω => (g ω)^2)=g := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [g,hω]
  have hgm : (∫⁻ ω, g ω ∂μ)=μ A := lintegral_indicator_one hA
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hf.aemeasurable hg.aemeasurable
  simp only [Pi.mul_apply,hfg,ENNReal.rpow_two,hgg,hgm] at hh
  have hsqrt (z : ℝ≥0∞) : (z^((1 : ℝ)/2))^2=z := by
    rw [←ENNReal.rpow_two,←ENNReal.rpow_mul]
    norm_num
  have hh2 := pow_le_pow_left' hh 2
  rw [mul_pow,hsqrt,hsqrt,mul_comm] at hh2
  exact hh2

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma restrictedLayerCount_moment_cauchy (I : Set E) (A : Set V) (p : unitInterval) (x : V) :
    (∫⁻ ω, restrictedLayerCount G I A ω x ∂law p)^2 ≤
      law p (restrictedHit G I x A) *
        (∫⁻ ω, (restrictedLayerCount G I A ω x)^2 ∂law p) := by
  apply lintegral_support_cauchy (law p) _ (measurable_restrictedLayerCount G I A x) _
    (measurableSet_finiteWitness _ (restrictedHit_upper G I x A) (restrictedHit_finiteWitness G I x A))
  intro ω hω
  apply ENNReal.tsum_eq_zero.mpr
  intro y
  exact ite_eq_right (fun h => hω ⟨y,h.1,h.2⟩)

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem adjustedUpLayerMoment_cauchy
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (p : unitInterval) (n : ℕ) (x : V) (u : ℝ) :
    (G.adjustedUpLayerMoment a R p n x u)^2 ≤
      G.law p (restrictedHit G.ends Set.univ x {y | R*((n : ℝ)-1) ≤ G.orbitAdjustedHeight a x y}) *
        (∫⁻ ω, (restrictedLayerCount G.ends
          (Percolation.internalEdges G.ends {y | G.adjustedLayerIndex a R u x y ≤ (n : ℤ)})
          {y | G.adjustedLayerIndex a R u x y=(n : ℤ)} ω x)^2 ∂G.law p) := by
  apply (restrictedLayerCount_moment_cauchy G.ends _ _ p x).trans
  apply mul_le_mul' (measure_mono ?_) le_rfl
  rintro ω ⟨y,hy,hxy⟩
  have hh := (G.adjustedLayerIndex_height_bounds a R u hR x y).1
  rw [hy] at hh
  refine ⟨y,?_,Percolation.conn_mono G.ends
    (show ω ∩ Percolation.internalEdges G.ends _ ⊆ ω ∩ Set.univ from fun e he => ⟨he.1,Set.mem_univ e⟩) hxy⟩
  exact_mod_cast hh.le

end CriticalPercolation.BondGraph

end

end OAI
