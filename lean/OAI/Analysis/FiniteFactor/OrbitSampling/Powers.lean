import OAI.Analysis.FiniteFactor.Sampling.Selection
import OAI.Analysis.FiniteFactor.CrossedProduct.PhaseDecay

namespace OAI

namespace FiniteFactor
open Finset Filter
open scoped Topology
noncomputable section

def samplingQ (m : ℕ) : ℝ := (m : ℝ)^((7/10 : ℝ)*(m : ℝ))
def samplingH (m : ℕ) : ℕ := m^300
def samplingR (m K : ℕ) : ℕ := m*K*m^1000

theorem sampling_integer_candidates (Q : ℝ) (hQ : 4 ≤ Q) :
    Q/4 ≤ ((Finset.Icc ⌈Q/2⌉ ⌊Q⌋).card : ℝ) := by
  have hf := Int.sub_one_lt_floor Q
  have hc := Int.ceil_lt_add_one (Q/2)
  have horder : ⌈Q/2⌉ ≤ ⌊Q⌋ := by
    have : (⌈Q/2⌉ : ℝ) < (⌊Q⌋ : ℝ)+1 := by linarith
    have ht : ⌈Q/2⌉ < ⌊Q⌋+1 := by exact_mod_cast this
    omega
  rw [Int.card_Icc]
  have hcast : ((⌊Q⌋+1-⌈Q/2⌉).toNat : ℝ) = (⌊Q⌋ : ℝ)+1-(⌈Q/2⌉ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ ⌊Q⌋+1-⌈Q/2⌉)
  rw [hcast]
  linarith

theorem sampling_forbidden_budget (m K : ℕ) (hm : 4 ≤ m) (hK : K ≤ m) :
    (((2*samplingH m+1)^2*(2*samplingR m K+1) : ℕ) : ℝ) ≤ (m : ℝ)^1605 := by
  have hm1 : 1 ≤ m := by omega
  have hh : 1 ≤ samplingH m := one_le_pow₀ hm1
  have hr : samplingR m K ≤ m^1002 := by
    unfold samplingR
    calc
      m*K*m^1000 ≤ m*m*m^1000 := by gcongr
      _ = m^1002 := by ring
  have hp : 1 ≤ m^1002 := one_le_pow₀ hm1
  have hD : (2*samplingH m+1)^2*(2*samplingR m K+1) ≤ 27*m^1602 := by
    calc
      _ ≤ (3*samplingH m)^2*(3*m^1002) := by gcongr <;> omega
      _ = _ := by unfold samplingH; ring
  have h27 : 27 ≤ m^3 := (by norm_num : 27 ≤ (4 : ℕ)^3).trans (Nat.pow_le_pow_left hm 3)
  have hhD : (2*samplingH m+1)^2*(2*samplingR m K+1) ≤ m^1605 := by
    calc
      _ ≤ 27*m^1602 := hD
      _ ≤ m^3*m^1602 := Nat.mul_le_mul_right _ h27
      _ = _ := by ring
  exact_mod_cast hhD

/-- An explicit sufficiently-large threshold discharges the source's greedy
asymptotics, retaining Q, H, R and the exponent 0.69m exactly. -/
theorem exists_source_sampling_powers (m K : ℕ) (hm : 200000 ≤ m) (hK : K ≤ m) :
    ∃ N : Finset ℤ,
      (∀ n ∈ N, samplingQ m/2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ samplingQ m ∧ 0 < n) ∧
      (m : ℝ)^((69/100 : ℝ)*(m : ℝ)) ≤ (N.card : ℝ) ∧
      (N : Set ℤ).Pairwise (fun n n' => ¬SamplingConflict (samplingH m) (samplingR m K) n n') := by
  have hmR : (200000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hQ : (m : ℝ)^1606 ≤ samplingQ m := by
    unfold samplingQ
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hm1
    norm_num
    linarith
  have hmQ : (m : ℝ) ≤ samplingQ m := by
    calc
      _ ≤ (m : ℝ)^1606 := le_self_pow₀ hm1 (by norm_num)
      _ ≤ _ := hQ
  have hQ4 : 4 ≤ samplingQ m := by linarith
  have hR : (samplingR m K : ℝ) < samplingQ m/2 := by
    have hr : samplingR m K ≤ m^1002 := by
      unfold samplingR
      calc
        m*K*m^1000 ≤ m*m*m^1000 := by gcongr
        _ = _ := by ring
    have hsmall : (m : ℝ)^1002 * (m : ℝ) ≤ (m : ℝ)^1606 := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hm1 (by norm_num)
    have hrR : (samplingR m K : ℝ) ≤ (m : ℝ)^1002 := by exact_mod_cast hr
    have hpos : 0 < (m : ℝ)^1002 := by positivity
    nlinarith
  let S := Finset.Icc ⌈samplingQ m/2⌉ ⌊samplingQ m⌋
  have hS (n : ℤ) (hn : n ∈ S) :
      samplingQ m/2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ samplingQ m := by
    have hh := mem_Icc.mp hn
    constructor
    · exact (Int.le_ceil _).trans (by exact_mod_cast hh.1)
    · exact (show (n : ℝ) ≤ (⌊samplingQ m⌋ : ℝ) by exact_mod_cast hh.2).trans (Int.floor_le _)
  obtain ⟨N,hNS,hpair,hcard⟩ := exists_sampling_separated (samplingH m) (samplingR m K)
    (one_le_pow₀ (by omega)) S (fun n hn => by exact_mod_cast hR.trans_le (hS n hn).1)
  refine ⟨N, fun n hn => ⟨(hS n (hNS hn)).1, (hS n (hNS hn)).2, ?_⟩, ?_, hpair⟩
  · have hh := (hS n (hNS hn)).1
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  · have hcount : samplingQ m/4 ≤
        (((2*samplingH m+1)^2*(2*samplingR m K+1) : ℕ) : ℝ)*(N.card : ℝ) :=
      (sampling_integer_candidates _ hQ4).trans (by exact_mod_cast hcard)
    have hDb := sampling_forbidden_budget m K (by omega) hK
    have hcount' : samplingQ m/4 ≤ (m : ℝ)^1605*(N.card : ℝ) :=
      hcount.trans (mul_le_mul_of_nonneg_right hDb (Nat.cast_nonneg _))
    have hexp : (m : ℝ)^1605*(m : ℝ)^((69/100 : ℝ)*(m : ℝ))*(m : ℝ) ≤ samplingQ m := by
      unfold samplingQ
      calc
        _ = (m : ℝ)^(1605+(69/100 : ℝ)*(m : ℝ)+1) := by
          rw [Real.rpow_add hm0, Real.rpow_one, Real.rpow_add hm0]
          norm_num [Real.rpow_ofNat]
        _ ≤ _ := by
          apply Real.rpow_le_rpow_of_exponent_le hm1
          norm_num
          linarith
    have hprod : 0 < (m : ℝ)^1605 := by positivity
    have htarget : 0 ≤ (m : ℝ)^((69/100 : ℝ)*(m : ℝ)) := by positivity
    apply (mul_le_mul_iff_right₀ hprod).mp
    nlinarith

/-- A deterministic finite set fixed from the numerical stages alone. -/
def sourceSamplingPowers (s : ℕ) : Finset ℤ :=
  if h : 200000 ≤ sourceBlockSize s then
    Classical.choose (exists_source_sampling_powers (sourceBlockSize s)
      (sourceStageState s).K h (sourceStage s).m_ge_K)
  else ∅

theorem sourceSamplingPowers_spec (s : ℕ) (hs : 200000 ≤ sourceBlockSize s) :
    (∀ n ∈ sourceSamplingPowers s,
      samplingQ (sourceBlockSize s)/2 ≤ (n : ℝ) ∧
      (n : ℝ) ≤ samplingQ (sourceBlockSize s) ∧ 0 < n) ∧
    (sourceBlockSize s : ℝ)^((69/100 : ℝ)*(sourceBlockSize s : ℝ)) ≤
      ((sourceSamplingPowers s).card : ℝ) ∧
    ((sourceSamplingPowers s : Finset ℤ) : Set ℤ).Pairwise (fun n n' =>
      ¬SamplingConflict (samplingH (sourceBlockSize s))
        (samplingR (sourceBlockSize s) (sourceStageState s).K) n n') := by
  unfold sourceSamplingPowers
  rw [dite_eq_left hs]
  exact Classical.choose_spec (exists_source_sampling_powers _ _ hs (sourceStage s).m_ge_K)

theorem sourceSamplingPowers_eventually : ∀ᶠ s in atTop,
    (∀ n ∈ sourceSamplingPowers s,
      samplingQ (sourceBlockSize s)/2 ≤ (n : ℝ) ∧
      (n : ℝ) ≤ samplingQ (sourceBlockSize s) ∧ 0 < n) ∧
    (sourceBlockSize s : ℝ)^((69/100 : ℝ)*(sourceBlockSize s : ℝ)) ≤
      ((sourceSamplingPowers s).card : ℝ) ∧
    ((sourceSamplingPowers s : Finset ℤ) : Set ℤ).Pairwise (fun n n' =>
      ¬SamplingConflict (samplingH (sourceBlockSize s))
        (samplingR (sourceBlockSize s) (sourceStageState s).K) n n') := by
  filter_upwards [sourceBlockSize_tendsto.eventually (eventually_ge_atTop 200000)] with s hs
  exact sourceSamplingPowers_spec s hs

end
end FiniteFactor

end OAI
