import OAI.NumberTheory.JointDickman.Amplification.TwistedBinDistance
import OAI.NumberTheory.JointDickman.Counting.ComplexFiniteShortAverages

namespace OAI

/-! # Nonprincipal short averages of the actual centered bin labels -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

noncomputable def twistedWeightedBinAverage {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (H z : ℝ) : ℂ :=
  (∑ n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊, (binLabel E ζ n-μ)*(w n : ℂ)*χ (n : ZMod q))/(H : ℂ)

theorem twistedWeightedBinAverage_eq_combination {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (J : ℕ) (c : (ι → Fin (J+1)) → ℂ)
    (Y H z : ℝ)
    (hcoeff : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ Y →
      binLabel E ζ n-μ = ∑ a : ι → Fin (J+1), c a*(binLabel E (fun i => interpolationNode (a i)) n : ℂ))
    (hzH : z+H ≤ Y) :
    twistedWeightedBinAverage E ζ μ w χ H z =
      complexFiniteShort univ c (fun a => twistedWeightedBinInterpolant E w a χ) H z := by
  unfold twistedWeightedBinAverage complexFiniteShort complexShortAverage
  calc
    _ = (∑ n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊, ∑ a : ι → Fin (J+1),
        c a*twistedWeightedBinInterpolant E w a χ n)/(H : ℂ) := by
      congr 1
      apply sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
      have hnY : (n : ℝ) ≤ Y :=
        ((Nat.le_floor_iff' (by omega : n ≠ 0)).mp (mem_Ioc.mp hn).2).trans hzH
      rw [hcoeff n hn1 hnY,sum_mul,sum_mul]
      apply sum_congr rfl
      intro a _
      simp only [twistedWeightedBinInterpolant,ArithmeticFunction.coe_mk,
        weightedBinInterpolant,ArithmeticFunction.pmul_apply,Complex.ofReal_mul,
        characterArithmetic,show n ≠ 0 by omega,ite_false]
      ring
    _ = _ := by
      rw [sum_comm]
      simp only [sum_div,mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro n _
      ring

theorem nonprincipal_weightedBinAverage_short
    (hMRT : ComplexShortIntervalInput) (hKMT : CharacterDistanceDivergence)
    (hM : PrimeReciprocalMertensInput)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (ζ : ι → ℂ) (μ : ℂ)
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p ∈ P B → p.Prime)
    (t : ℕ → ℕ → ℝ) (ht : ∀ B p, p ∈ P B → 0 ≤ t B p ∧ t B p ≤ 1)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖twistedWeightedBinAverage (fun i => primeBin (scale n) J (k i)) ζ μ
          (finitePrimeWeight (P B) (t B)) χ (H B) z‖^2) < ε := by
  obtain ⟨c,hc⟩ := centered_binLabel_interpolation ζ μ J
  let E n i := primeBin (scale n) J (k i)
  let X B n := A B*scale n
  let f B n (a : ι → Fin (J+1)) := twistedWeightedBinInterpolant (E n) (finitePrimeWeight (P B) (t B)) a χ
  have hw B n : |finitePrimeWeight (P B) (t B) n| ≤ 1 := by
    rw [abs_of_nonneg (finitePrimeWeight_bounds (ht B) n).1]
    exact (finitePrimeWeight_bounds (ht B) n).2
  have hX B : Tendsto (X B) atTop atTop := hscale.const_mul_atTop (hA B)
  have hwindow B : ∀ᶠ n in atTop, ∀ v : ℕ, 1 ≤ v → (v : ℝ) ≤ 3*X B n →
      binLabel (E n) ζ v-μ = ∑ a : ι → Fin (J+1), c a*(binLabel (E n) (fun i => interpolationNode (a i)) v : ℂ) := by
    filter_upwards [hscale.eventually (primeBin_count_eventually_le J hJ (3*A B))] with n hn v hv hvX
    apply hc (E n) v (by omega)
    intro i
    apply hn (k i) (hk i) v hv
    simpa only [X,mul_assoc] using hvX
  have hbound := complexFiniteShort_eventually_eventually hMRT univ c f
    (fun B n a _ => twistedWeightedBinInterpolant_multiplicative _ _
      (finitePrimeWeight_multiplicative (hP B) (t B)) a χ)
    (fun B n a _ v => twistedWeightedBinInterpolant_norm_le _ _ (hw B) a χ v)
    H X hH hX
    (fun B a _ => twistedWeightedBinInterpolant_distance hKMT hM hJ k hk (hP B) (t B)
      (ht B) a χ hχ (hA B) scale hscale)
  have hi B : ∀ᶠ n in atTop,
      (∫ z in X B n..2*X B n, ‖twistedWeightedBinAverage (E n) ζ μ
        (finitePrimeWeight (P B) (t B)) χ (H B) z‖^2) =
      (∫ z in X B n..2*X B n, ‖complexFiniteShort univ c (f B n) (H B) z‖^2) := by
    filter_upwards [hwindow B,(hX B).eventually_gt_atTop 0,
      (hX B).eventually_ge_atTop (H B)] with n hn hpos hlen
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by linarith : X B n ≤ 2*X B n)] at hz
    dsimp only
    rw [twistedWeightedBinAverage_eq_combination (E n) ζ μ (finitePrimeWeight (P B) (t B)) χ J c
      (3*X B n) (H B) z hn (by linarith [hz.2])]
  intro ε hε
  filter_upwards [hbound ε hε] with B hb
  filter_upwards [hb,hi B] with n hn he
  change (1/X B n)*(∫ z in X B n..2*X B n, ‖twistedWeightedBinAverage (E n) ζ μ
    (finitePrimeWeight (P B) (t B)) χ (H B) z‖^2) < ε
  rw [he]
  exact hn

end JointDickman

end OAI
