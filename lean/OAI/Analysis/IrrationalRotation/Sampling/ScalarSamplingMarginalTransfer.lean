import OAI.Analysis.IrrationalRotation.Sampling.UniformIntervalPhase
import Mathlib.MeasureTheory.Function.Floor

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.UniformIntervalPhase

theorem fractionLaw_absolutelyContinuous (N₀ n : ℝ) (hN : 0 < N₀) (hn : 0 < n) :
    fractionLaw N₀ n ≪ (volume : Measure ℝ) := by
  rw [← (scalar_marginal N₀ n hN hn).2.2]
  exact (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict

theorem ae_sample_congr {E : Type*} (N₀ n : ℝ) (hN : 0 < N₀) (hn : 0 < n)
    {f g : ℝ → E} (hfg : f =ᵐ[volume] g) :
    (fun x => f (Int.fract (n * x))) =ᵐ[lambdaLaw N₀]
      (fun x => g (Int.fract (n * x))) := by
  exact ae_of_ae_map ((measurable_const_mul n).fract.aemeasurable)
    ((fractionLaw_absolutelyContinuous N₀ n hN hn).ae_eq hfg)

theorem sampled_rectangle_congr (N₀ n n' : ℝ) (hN : 0 < N₀)
    (hn : 0 < n) (hn' : 0 < n') {s s' t t' : Set ℝ}
    (hs : s =ᵐ[volume] s') (ht : t =ᵐ[volume] t') :
    (lambdaLaw N₀).real {x | Int.fract (n * x) ∈ s ∧ Int.fract (n' * x) ∈ t} =
      (lambdaLaw N₀).real {x | Int.fract (n * x) ∈ s' ∧ Int.fract (n' * x) ∈ t'} := by
  unfold Measure.real
  congr 1
  apply measure_congr
  filter_upwards [ae_sample_congr N₀ n hN hn hs,
    ae_sample_congr N₀ n' hN hn' ht] with x hx hy
  rw [hx, hy]

theorem sampled_rectangle_Icc_eq_Ico (N₀ n n' : ℝ) (hN : 0 < N₀)
    (hn : 0 < n) (hn' : 0 < n') (a b c d : ℝ) :
    (lambdaLaw N₀).real
      {x | Int.fract (n * x) ∈ Icc a b ∧ Int.fract (n' * x) ∈ Icc c d} =
    (lambdaLaw N₀).real
      {x | Int.fract (n * x) ∈ Ico a b ∧ Int.fract (n' * x) ∈ Ico c d} :=
  sampled_rectangle_congr N₀ n n' hN hn hn' Ico_ae_eq_Icc.symm Ico_ae_eq_Icc.symm

theorem sampled_rectangle_Ioo_eq_Ico (N₀ n n' : ℝ) (hN : 0 < N₀)
    (hn : 0 < n) (hn' : 0 < n') (a b c d : ℝ) :
    (lambdaLaw N₀).real
      {x | Int.fract (n * x) ∈ Ioo a b ∧ Int.fract (n' * x) ∈ Ioo c d} =
    (lambdaLaw N₀).real
      {x | Int.fract (n * x) ∈ Ico a b ∧ Int.fract (n' * x) ∈ Ico c d} :=
  sampled_rectangle_congr N₀ n n' hN hn hn' Ioo_ae_eq_Ico Ioo_ae_eq_Ico

end Invariant233.UniformIntervalPhase

end

end OAI
