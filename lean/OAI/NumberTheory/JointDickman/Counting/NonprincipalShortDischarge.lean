import OAI.NumberTheory.JointDickman.Counting.NonprincipalBinShort
import OAI.NumberTheory.JointDickman.Counting.TwistedInterpolantShort
import OAI.NumberTheory.JointDickman.Counting.FiniteShortComponents

namespace OAI

/-! # Nonprincipal bin short averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem nonprincipal_weightedBinAverage_short_proved
    (_hKMT : CharacterDistanceDivergence) (_hM : PrimeReciprocalMertensInput)
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
  have hbound := complexFiniteShort_of_components univ c f
    (fun B n a _ v => twistedWeightedBinInterpolant_norm_le _ _ (hw B) a χ v)
    H X hH hX (fun a _ => twisted_interpolant_short hJ k hk P hP t ht χ hχ
      (J+1) a A H scale hA hH hscale)
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
