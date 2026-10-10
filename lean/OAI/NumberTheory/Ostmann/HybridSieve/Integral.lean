import OAI.NumberTheory.Ostmann.HybridSieve.CharacterFamily
import OAI.NumberTheory.Ostmann.HybridSieve.LogWindow
import OAI.NumberTheory.Ostmann.HybridSieve.PacketFamilyBound

namespace OAI

open MeasureTheory FourierTransform
open scoped Classical FourierTransform Real
namespace Ostmann.HybridSieve

noncomputable def dyadicPhaseSum (N : ℕ) (a : ℕ → ℂ) {Q : ℕ}
    (i : PrimitiveFamily Q) (H t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), a n * familyValue i n * fourierPhase (H*Real.log n) t

theorem exists_hybrid_integral_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Q : ℕ) (a : ℕ → ℂ) (H : ℝ), 0 < N → 0 < H →
      (∑ i : PrimitiveFamily Q, familyWeight i *
        (∫ t in Set.Icc (-1:ℝ) 1, ‖dyadicPhaseSum N a i H t‖^2)) ≤
      C * ((N:ℝ)/H+1+(Q:ℝ)^2*(harmonic (Q^2):ℝ)) *
        ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 := by
  obtain ⟨c,hc,hfourier⟩ := Ostmann.SchwartzCutoff.bump_fourier_uniform_lower
  let f := Ostmann.SchwartzCutoff.bumpSchwartz
  let J : ℝ := ∫ x : ℝ, ‖f x‖^2
  have hJ : 0 ≤ J := integral_nonneg (fun x => sq_nonneg ‖f x‖)
  have hc2 : 0 < c^2 := sq_pos_of_pos hc
  refine ⟨(J+1)/c^2, div_pos (by linarith) hc2, ?_⟩
  intro N Q a H hN hH
  let M := ⌊(N:ℝ)/H⌋₊+1
  let K : ℝ := (M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ)
  have hraw := packetFamily_integral_bound (Finset.Ioc N (2*N)) a
    (fun i : PrimitiveFamily Q => familyValue i) familyWeight familyWeight_nonneg
    (fun n : ℕ => H*Real.log n) f c K hc.le hfourier (by
      intro x
      obtain ⟨A,hA⟩ := active_window_interval N a H x hN hH
      have h := family_interval_sieve (Finset.Ioc N (2*N))
        (fun n => a n*f (x-H*Real.log n)) A M Q hA
      simpa only [K, norm_mul, mul_pow, mul_right_comm] using h)
  change c^2 * (∑ i : PrimitiveFamily Q, familyWeight i *
    (∫ t in Set.Icc (-1:ℝ) 1, ‖dyadicPhaseSum N a i H t‖^2)) ≤
      K*J*(∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2) at hraw
  have hK : K ≤ (N:ℝ)/H+1+(Q:ℝ)^2*(harmonic (Q^2):ℝ) := by
    dsimp [K, M]
    push_cast
    gcongr
    exact Nat.floor_le (by positivity)
  have hHarm : 0 ≤ (harmonic (Q^2):ℝ) := by
    by_cases hQ : Q = 0
    · simp [hQ]
    · exact_mod_cast (harmonic_pos (pow_ne_zero 2 hQ)).le
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hs0 : 0 ≤ ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  apply (mul_le_mul_iff_right₀ hc2).mp
  calc
    _ ≤ K*J*(∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2) := hraw
    _ ≤ ((N:ℝ)/H+1+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(J+1)*
        (∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hK (by linarith) hJ (hK0.trans hK)) hs0
    _ = c^2 * (((J+1)/c^2)*
        ((N:ℝ)/H+1+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*
        (∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2)) := by
      field_simp

end Ostmann.HybridSieve

end OAI
