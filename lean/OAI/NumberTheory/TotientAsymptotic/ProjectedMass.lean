import OAI.NumberTheory.TotientAsymptotic.PrefixProjection
import OAI.NumberTheory.TotientAsymptotic.MassUpper

namespace OAI

/-! Uniform summation over the possible common prime prefixes. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def projectedPrimeFactor (C D : ℝ) (K : ℕ) : ℝ :=
  (1+bandPrimeError C (9/10) K)*Real.exp (simplexBoxTail 4 K)*projectedEnvelope D K

lemma projectedPrimeFactor_tendsto (C : ℝ) {D : ℝ} (hD : 0 < D) :
    Tendsto (projectedPrimeFactor C D) atTop (nhds 0) := by
  have hb := bandPrimeError_tendsto C (by norm_num : (0 : ℝ)<9/10)
  have he := (Real.continuous_exp.tendsto (0 : ℝ)).comp (simplexBoxTail_tendsto 4)
  have hp := (summable_projectedEnvelope hD).tendsto_atTop_zero
  have hh := (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hb).mul he).mul hp
  change Tendsto (fun K => (1+bandPrimeError C (9/10) K)*
    Real.exp (simplexBoxTail 4 K)*projectedEnvelope D K) atTop (nhds 0)
  simpa only [Function.comp_def,add_zero,Real.exp_zero,one_mul,mul_zero] using hh

/-- Uniformly over every late truncation, the whole projected prime mass
is at most the normalizing full-dimensional volume. This includes the empty
prime prefix, whose mass is one. -/
theorem projected_mass_le_G (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ K : ℕ, H ≤ K → K ≤ m x →
    ∀ Q : Finset (Fin (R x K) → ℕ),
    (∀ p ∈ Q, (∀ j, (p j).Prime) ∧ primePrefixCoord p ∈ prefixBandRegion x K ∧
      primePrefixCoord p ∈ enlargedSimplex (R x K) (B x) (xi x 0) (fun j => xi x (j.val+1))) →
    (∑ p ∈ Q, reciprocalShiftWeight p) ≤ G x (m x) := by
  obtain ⟨C,hC,hprime⟩ := projected_prime_mass_bound hbox
  obtain ⟨D,hD,hproj⟩ := uniform_projected_volume_bound hren
  have hlate : ∀ᶠ K : ℕ in atTop,
      4 ≤ lam*(K : ℝ) ∧ projectedPrimeFactor C D K ≤ 1 ∧ projectedEnvelope D K ≤ 1 := by
    filter_upwards [((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop lam_pos).eventually
      (eventually_ge_atTop (4 : ℝ)),
      (projectedPrimeFactor_tendsto C hD).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),
      (summable_projectedEnvelope hD).tendsto_atTop_zero.eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))] with K hK hf he
    exact ⟨hK,hf.le,he.le⟩
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp hlate
  filter_upwards [eventually_ge_atTop H₀] with H hH
  filter_upwards [hproj,theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),inverse_scale_bound]
    with x hp hs hB hscale
  intro K hHK hKm Q hQ
  obtain ⟨hcut,hfactor,henv⟩ := hH₀ K (hH.trans hHK)
  have hG := (div_le_iff₀ (G_pos hB (m x))).mp (hp K hKm)
  change G x (R x K) ≤ projectedEnvelope D K*G x (m x) at hG
  by_cases hn : 0 < R x K
  · have hmass := hprime hs.1 hcut hB hscale hn Q hQ
    have hpos : 0 ≤ (1+bandPrimeError C (9/10) K)*Real.exp (simplexBoxTail 4 K) :=
      mul_nonneg (by linarith [bandPrimeError_nonneg hC.le (by norm_num : (0 : ℝ)<9/10) K])
        (Real.exp_pos _).le
    calc
      _ ≤ ((1+bandPrimeError C (9/10) K)*Real.exp (simplexBoxTail 4 K))*G x (R x K) := hmass
      _ ≤ ((1+bandPrimeError C (9/10) K)*Real.exp (simplexBoxTail 4 K))*
          (projectedEnvelope D K*G x (m x)) := mul_le_mul_of_nonneg_left hG hpos
      _ = projectedPrimeFactor C D K*G x (m x) := by unfold projectedPrimeFactor; ring
      _ ≤ G x (m x) := mul_le_of_le_one_left (G_pos hB _).le hfactor
  · have hn0 : R x K=0 := by omega
    have hcard : (Q.card : ℝ) ≤ 1 := by
      have hc : Q.card ≤ 1 := Finset.card_le_one.mpr (by
        intro p _ q _
        funext j
        have hj := j.isLt
        omega)
      exact_mod_cast hc
    have hweight (p : Fin (R x K) → ℕ) : reciprocalShiftWeight p=1 := by
      simp [reciprocalShiftWeight,hn0]
    calc
      _ = (Q.card : ℝ) := by simp [hweight]
      _ ≤ 1 := hcard
      _ = G x (R x K) := by simp [G,hn0]
      _ ≤ projectedEnvelope D K*G x (m x) := hG
      _ ≤ G x (m x) := mul_le_of_le_one_left (G_pos hB _).le henv

end TotientAsymptotic

end

end OAI
