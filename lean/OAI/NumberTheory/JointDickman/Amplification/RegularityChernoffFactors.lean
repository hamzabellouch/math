import OAI.NumberTheory.JointDickman.Arithmetic.RegularitySievePrimes
import OAI.NumberTheory.JointDickman.Amplification.DyadicTailSum

namespace OAI

/-! # Chernoff factors with the actual truncated sieve prime sets -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def prefixUpperFactor (B : ℕ) (c g τ s : ℝ) : ℝ :=
  Real.exp (-s * (g / 2 + τ) * auxiliaryLogLength B + ((Real.exp s - 1) / 2) *
    tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B) (primePrefix B g (auxiliaryPrimes B)))

noncomputable def prefixLowerFactor (B : ℕ) (c g τ s : ℝ) : ℝ :=
  Real.exp (s * (g / 2 - τ) * auxiliaryLogLength B + ((Real.exp (-s) - 1) / 2) *
    tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B) (primePrefix B g (auxiliaryPrimes B)))

theorem actual_prefix_chernoff_decay
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {τ : ℝ} (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 10 ∧ Real.exp s ≤ 2 ∧ Real.exp (-s) ≤ 2 ∧
      ∀ c g : ℝ, 0 < c → c ≤ 4 → 0 < g → g ≤ 1 →
        Tendsto (fun B => prefixUpperFactor B c g τ s) atTop (𝓝 0) ∧
        Tendsto (fun B => prefixLowerFactor B c g τ s) atTop (𝓝 0) := by
  obtain ⟨s, hs, _hsτ, hs1, he, hen, hmargin⟩ := exists_prefix_tilt hτ
  refine ⟨s, hs, hs1, he, hen, ?_⟩
  intro c g hc hc4 hg hg1
  let m := fun B => tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B) (primePrefix B g (auxiliaryPrimes B))
  have hm : Tendsto (fun B => m B / auxiliaryLogLength B) atTop (𝓝 g) :=
    tilt_prefix_mass_tendsto hM hc hc4 hg hg1
  have hpos : -s * (g / 2 + τ) + ((Real.exp s - 1) / 2) * g < 0 := by
    have h := (hmargin g hg.le hg1).1
    nlinarith [mul_pos hs hτ]
  have hneg : s * (g / 2 - τ) + ((Real.exp (-s) - 1) / 2) * g < 0 := by
    have h := (hmargin g hg.le hg1).2
    nlinarith [mul_pos hs hτ]
  have hℓ : ∀ᶠ B : ℕ in atTop, auxiliaryLogLength B ≠ 0 :=
    (auxiliaryLogLength_tendsto.eventually_gt_atTop 0).mono (fun _ h => ne_of_gt h)
  constructor
  · have hlim := (hm.const_mul ((Real.exp s - 1) / 2)).const_add (-s * (g / 2 + τ))
    have hprod := hlim.neg_mul_atTop hpos auxiliaryLogLength_tendsto
    apply Real.tendsto_exp_atBot.comp (hprod.congr' ?_)
    filter_upwards [hℓ] with B hB
    dsimp [prefixUpperFactor, m]
    field_simp
  · have hlim := (hm.const_mul ((Real.exp (-s) - 1) / 2)).const_add (s * (g / 2 - τ))
    have hprod := hlim.neg_mul_atTop hneg auxiliaryLogLength_tendsto
    apply Real.tendsto_exp_atBot.comp (hprod.congr' ?_)
    filter_upwards [hℓ] with B hB
    dsimp [prefixLowerFactor, m]
    field_simp

noncomputable def tailChernoffFactor (B i : ℕ) (c C : ℝ) : ℝ :=
  Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C) +
    ((Real.exp (-(1 / 10 : ℝ)) - 1) / 2) *
      tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B)
        ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)))

theorem actual_tail_chernoff_sum
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 4) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ B : ℕ in atTop, ∀ (S : Finset ℕ) (C : ℝ),
      (∀ i ∈ S, primeTailEndpoint B i ≤ B) →
      (∑ i ∈ S, tailChernoffFactor B i c C) ≤ D * Real.exp (-(1 / 10 : ℝ) * C) := by
  classical
  obtain ⟨K, _hK, hbound⟩ := tilt_tail_mass_lower hM hc hc4
  let D := Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) *
    ((2 : ℝ) ^ tailSaving / ((2 : ℝ) ^ tailSaving - 1))
  have hr : 1 < (2 : ℝ) ^ tailSaving := Real.one_lt_rpow (by norm_num) tailSaving_pos
  refine ⟨D, mul_pos (Real.exp_pos _) (div_pos (by positivity) (by linarith)), ?_⟩
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [hbound, hloglarge, eventually_gt_atTop 0] with B hB hlog hBpos
  intro S C hS
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hY0 : 0 < Real.log (auxiliaryCutoff B) := by linarith
  have hY (i : ℕ) : Real.log (auxiliaryCutoff B) ≤ primeTailEndpoint B i := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
    exact le_mul_of_one_le_left hY0.le hp
  exact dyadic_tail_chernoff_sum S hB0 hY0
    (fun i => tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B)
      ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)))
    (fun i _ => hB (primeTailEndpoint B i) (hY i)) hS

theorem tail_endpoint_index_lt {B i : ℕ} (hlog : 1 ≤ Real.log (auxiliaryCutoff B))
    (hi : primeTailEndpoint B i < B) : i < B := by
  have hp : (i : ℝ) < (2 : ℝ) ^ i := by exact_mod_cast (show i < 2 ^ i from Nat.lt_two_pow_self)
  have hm : (2 : ℝ) ^ i ≤ primeTailEndpoint B i :=
    le_mul_of_one_le_right (by positivity) hlog
  exact_mod_cast hp.trans (hm.trans_lt hi)

end JointDickman

end OAI
