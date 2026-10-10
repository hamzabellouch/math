import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSitePrefix
import OAI.NumberTheory.JointDickman.Counting.ShortWindowEnergy

namespace OAI

/-! # Prime-law errors control all bounded short-window tests -/
namespace JointDickman
open Finset Filter MeasureTheory Classical
open scoped Topology

theorem prime_site_window_energy_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (E : (Q → Bool) → ℝ) {H : ℝ} (hH : 1 ≤ H) {A : ℝ} (hA : 0 < A)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ f : ArithmeticFunction ℂ,
      (∀ k, ‖f k‖^2 ≤ E (fun p => decide (p.val ∣ k))) →
      (1/(A*scale n))*(∫ z in (A*scale n)..2*(A*scale n),
        ‖PublishedInputs.complexShortAverage f H z‖^2) <
          6*(∑ x, fullPrimeMass Q x*E x)+ε := by
  have hX : Tendsto (fun n => A*scale n) atTop atTop := hscale.const_mul_atTop hA
  have ht := ((prime_site_scaled_sum_tendsto Q hQ E (by norm_num : (0 : ℝ) < 3)).const_mul 2).comp hX
  have ht' : Tendsto (fun n =>
      2*(∑ k ∈ range (⌊3*(A*scale n)⌋₊+1), E (fun p => decide (p.val ∣ k)))/(A*scale n))
      atTop (𝓝 (6*∑ x, fullPrimeMass Q x*E x)) := by
    convert ht using 1
    · ext n
      dsimp only [Function.comp_apply]
      ring
    · congr 1
      ring
  filter_upwards [hX.eventually_gt_atTop 0,hX.eventually_ge_atTop H,
    ht'.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hε))] with n hn hHn he
  intro f hf
  exact (complexShortAverage_energy_le_prefix f _ hf hH hn hHn).trans_lt he

end JointDickman

end OAI
