import OAI.NumberTheory.TotientAsymptotic.RenewalConvolution
import OAI.NumberTheory.TotientAsymptotic.PrefixLower

namespace OAI

/-! Uniform lower bounds for renewal coefficients and unbanded prefix coordinates. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma normalizedRenewal_pos (n : ℕ) : 0 < normalizedRenewal n :=
  mul_pos (g_pos _) (pow_pos rho_pos _)

lemma renewal_uniform_lower (hford : FordRenewalInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c*(rho^n)⁻¹ ≤ g n := by
  have hlim := (normalizedRenewal_properties hford).1
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_gt_nhds (show gamma/2 < gamma by linarith [gamma_pos])))
  let T := insert (gamma/2) ((Finset.range N).image normalizedRenewal)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  let c := T.min' hT
  have hc : 0 < c := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact div_pos gamma_pos (by norm_num)
    · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hy
      exact normalizedRenewal_pos n
  refine ⟨c, hc, fun n => ?_⟩
  have hh : c ≤ normalizedRenewal n := by
    by_cases hn : n < N
    · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩))
    · exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans (hN n (by omega)).le
  have hp := mul_le_mul_of_nonneg_right hh (inv_pos.mpr (pow_pos rho_pos n)).le
  simpa only [normalizedRenewal, mul_assoc, mul_inv_cancel₀ (pow_pos rho_pos n).ne', mul_one]
    using hp

/-- A terminal lower bound forces exponential growth towards the front of
an unbanded prefix. The constant is independent of the dimension. -/
theorem unbanded_prefix_lower (hford : FordRenewalInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (u : ℕ → ℝ) (T : ℝ), 0 ≤ T → T ≤ u N →
      (∀ i < N, (∑ j ∈ Finset.Icc (i+1) N, a (j-i)*u j) ≤ u i) →
      ∀ i ≤ N, c*T*(rho^(N-i))⁻¹ ≤ u i := by
  obtain ⟨c, hc, hg⟩ := renewal_uniform_lower hford
  refine ⟨c, hc, ?_⟩
  intro N u T hT hu hs i hi
  calc
    _ = (c*(rho^(N-i))⁻¹)*T := by ring
    _ ≤ g (N-i)*T := mul_le_mul_of_nonneg_right (hg _) hT
    _ ≤ g (N-i)*u N := mul_le_mul_of_nonneg_left hu (g_pos _).le
    _ ≤ u i := renewal_prefix_lower N u hs hi

end TotientAsymptotic

end

end OAI
