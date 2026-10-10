import OAI.NumberTheory.EgyptianFractions.Defs
import OAI.NumberTheory.EgyptianFractions.MarkerCoverage
import OAI.NumberTheory.EgyptianFractions.PrescribedInversion
import OAI.NumberTheory.EgyptianFractions.PrescribedAnalysis
import OAI.NumberTheory.EgyptianFractions.UpperSlope

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- The combinatorial hypotheses of the prescribed-denominator corollary imply
all its eventual double-exponential lower bounds. -/
theorem prescribed_lower_of_marked
    (padding : ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
      ∀ m : ℕ, (∃ i : Fin r, n i = m) →
        ∃ n' : Fin (r + 1) → ℕ,
          IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m)
    (occurs : ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k)
    (short : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i : Fin k, n i = m) ∧
          (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)))
    (missing : ∀ k : ℕ, 2 ≤ v k ∧ v k ∉ D k) :
    ∀ c : ℝ, c < Real.log 2 / 257 → ∃ K : ℕ,
      ∀ k : ℕ, K ≤ k → Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ) := by
  have hmono : Monotone D := D_mono_of_padding padding
  have hsmall : ∀ M : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ m : ℕ, 2 ≤ m → m < M → m ∈ D k := by
    intro M
    obtain ⟨K, hK⟩ := bounded_markers_eventually hmono occurs M
    exact ⟨K, fun k hk m hm hM => hK k hk m hm hM.le⟩
  have hshort : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ r : ℕ, 3 ≤ r ∧ m ∈ D r ∧
        (r : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
    intro ε hε
    obtain ⟨M, hM, h⟩ := short ε hε
    refine ⟨M, hM, ?_⟩
    intro m hm
    obtain ⟨r, n, hn, hmark, hlen⟩ := h m hm
    have hmem : m ∈ D r := ⟨hM.trans hm, n, hn, hmark⟩
    exact ⟨r, marker_length_ge_three hmem, hmem, hlen⟩
  have hA : (0 : ℝ) < 257 / Real.log 2 :=
    div_pos (by norm_num) (Real.log_pos (by norm_num))
  have h := eventual_double_exp_lower_of_short_markers D v (257 / Real.log 2)
    hA missing hsmall (fun r k _ hrk => hmono hrk) hshort
  simpa only [one_div_div] using h

/-- Full assembly of the prescribed-denominator consequence, conditional only
on its exact combinatorial construction and elementary denominator inputs. -/
theorem prescribed_denominator_corollary_of_inputs
    (padding : ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
      ∀ m : ℕ, (∃ i : Fin r, n i = m) →
        ∃ n' : Fin (r + 1) → ℕ,
          IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m)
    (occurs : ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k)
    (short : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i : Fin k, n i = m) ∧
          (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)))
    (missing : ∀ k : ℕ, 2 ≤ v k ∧ v k ∉ D k)
    (upper : ∀ k : ℕ, 1 ≤ k → v k ≤ 1 + k ^ (2 ^ (k - 1))) :
    (∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      Real.exp (Real.exp ((k : ℝ) / 600)) ≤ (v k : ℝ) ∧
      v k ≤ 1 + k ^ (2 ^ (k - 1))) ∧
    (Real.log 2 / 257 ≤ Filter.liminf prescribedSlope Filter.atTop ∧
      Filter.liminf prescribedSlope Filter.atTop ≤
        Filter.limsup prescribedSlope Filter.atTop ∧
      Filter.limsup prescribedSlope Filter.atTop ≤ Real.log 2) ∧
    (∀ c : ℝ, c < Real.log 2 / 257 → ∃ k0 : ℕ,
      ∀ k : ℕ, k0 ≤ k →
        Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ)) := by
  have rates := prescribed_lower_of_marked padding occurs short missing
  have ratesE : ∀ c : ℝ, c < Real.log 2 / 257 →
      ∀ᶠ k : ℕ in atTop, Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ) := by
    intro c hc
    exact eventually_atTop.2 (rates c hc)
  have hpower : ∀ᶠ k : ℕ in atTop, 2 ≤ (v k : ℝ) ∧
      (v k : ℝ) ≤ 1 + (k : ℝ) ^ (2 ^ (k - 1)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    constructor
    · exact_mod_cast (missing k).1
    · exact_mod_cast upper k hk
  have hbounded : IsBoundedUnder (· ≤ ·) atTop prescribedSlope := by
    refine ⟨Real.log 2 + 1, ?_⟩
    change ∀ᶠ k : ℕ in atTop, prescribedSlope k ≤ Real.log 2 + 1
    filter_upwards [hpower, eventually_ge_atTop (2 : ℕ)] with k hk hk2
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    have hloglog : Real.log (Real.log (k : ℝ)) ≤ (k : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hkpos,
        Real.log_le_sub_one_of_pos hlogpos]
    have h := loglog_le_of_power_bound hk2 hk.1 hk.2
    unfold prescribedSlope
    apply (div_le_iff₀ hkpos).2
    nlinarith
  have hlow := liminf_slope_lower_of_double_exp (fun k => (v k : ℝ))
    (Real.log 2 / 257) hbounded ratesE
  have hupp := power_bound_slope_limits (fun k => (v k : ℝ)) hpower
  refine ⟨?_, ⟨hlow.1, hlow.2, hupp.2.2⟩, rates⟩
  have hexp := eventually_double_exp_six_hundred (fun k => (v k : ℝ)) ratesE
  apply eventually_atTop.1
  filter_upwards [hexp, eventually_ge_atTop (1 : ℕ)] with k hk hk1
  exact ⟨hk, upper k hk1⟩

end Problem337

end

end OAI
