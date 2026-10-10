import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BilinearPart
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.UniformSmoothHarmonicBound

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySmoothDampedFamily
open Finset OrdinaryCorrelations SourcePrimeFactor Filter OrdinaryArchimedeanTwist MeasureTheory

def smoothCofactorHarmonic (f : ℕ → ℂ) (P S : Finset ℕ) (M L : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc M L).filter (fun n => n ∈ Nat.factoredNumbers S),
    ((n:ℂ)⁻¹ * twist f t n) / (primeCount P n+1:ℂ)

lemma continuous_smoothDamped (f : ℕ → ℂ) (P S : Finset ℕ) (n : ℕ) :
    Continuous (fun z : ℝ => smoothDamped f P S z n) := by
  unfold smoothDamped
  split_ifs
  · exact continuous_weightedFunction f P n
  · exact continuous_const

lemma smoothCofactorHarmonic_integral (f : ℕ → ℂ) (P S : Finset ℕ)
    (M L : ℕ) (t : ℝ) :
    smoothCofactorHarmonic f P S M L t =
      ∫ z in Set.Icc (0:ℝ) 1, ∑ n ∈ Finset.Ioc M L,
        (n:ℂ)⁻¹ * twist (smoothDamped f P S z) t n := by
  have hc (n : ℕ) : Continuous (fun z : ℝ =>
      (n:ℂ)⁻¹ * twist (smoothDamped f P S z) t n) := by
    unfold twist
    exact continuous_const.mul ((continuous_smoothDamped f P S n).mul continuous_const)
  rw [integral_finsetSum _ (fun n hn => (hc n).integrableOn_Icc)]
  unfold smoothCofactorHarmonic
  rw [sum_filter]
  apply sum_congr rfl
  intro n hn
  by_cases hs : n ∈ Nat.factoredNumbers S
  · simp only [hs, ite_true, twist, smoothDamped]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, cofactor_integral]
    ring
  · simp [hs, twist, smoothDamped]

theorem uniform_smooth_cofactor_harmonic {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ L : ℕ, M ≤ L → L ≤ 2*M →
      ∀ (P S : Finset ℕ), (∀ p ∈ P, Nat.Prime p) →
      ∀ t : ℝ, |t| ≤ (M:ℝ)^k/2 → ‖smoothCofactorHarmonic f P S M L t‖ ≤ ε := by
  filter_upwards [uniform_smooth_harmonic_segment_bound hf hm hNP k hk hε] with M hM
  intro L hML hL P S hP t ht
  rw [smoothCofactorHarmonic_integral]
  have hh := MeasureTheory.norm_integral_le_of_norm_le_const
    («μ» := volume.restrict (Set.Icc (0:ℝ) 1))
    (ae_restrict_of_forall_mem measurableSet_Icc (fun z hz => hM L hML hL P S hP z hz t ht))
  simpa using hh

end OrdinarySmoothDampedFamily

end

end OAI
