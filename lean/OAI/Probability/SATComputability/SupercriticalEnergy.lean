import OAI.Probability.SATComputability.CandidateEnergy
import OAI.Probability.SATComputability.DeletionScaling

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped NNReal Topology

noncomputable def deletionLifetimeMean (n r : ℕ) [NeZero n] : ℝ :=
  (FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)).expect
    (maskLifetime (20*n) (deletionBudgetMask n r))

theorem zero_lifetime_linear {n : ℕ} [NeZero n] (b : ℝ≥0) {δ : ℝ}
    (hδ : 0 < δ) (hn : 2/δ ≤ (n : ℝ))
    (hP : auxiliaryPoissonProbability n b ≤ δ/40) :
    deletionLifetimeMean n 0 ≤ ((b : ℝ)+δ)*n := by
  have hc := (Nat.ceil_lt_add_one (mul_nonneg b.coe_nonneg (Nat.cast_nonneg n))).le
  have htail := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 20*n)
  have hn' : 2 ≤ δ*(n : ℝ) := by
    have h := (div_le_iff₀ hδ).mp hn
    nlinarith
  have h := zero_lifetime_mean_upper n b
  change deletionLifetimeMean n 0 ≤ _ at h
  push_cast at h
  nlinarith

theorem quotient_linear_lower {n q : ℕ} (hq : 0 < q) (hn : q ≤ n) :
    (n : ℝ)/(2*(q : ℝ)) ≤ (n/q : ℕ) := by
  have hr : 1 ≤ n/q := Nat.div_pos hn hq
  have hdiv := Nat.lt_mul_div_succ n hq
  have hb : n ≤ 2*q*(n/q) := by nlinarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*(q : ℝ))).mpr
  have hbR : (n : ℝ) ≤ 2*(q : ℝ)*((n/q : ℕ) : ℝ) := by exact_mod_cast hb
  nlinarith only [hbR]

theorem relaxedPoissonMinimum_supercritical {a : ℝ≥0}
    (ha : limitingCenter 3 < (a : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ n : ℕ in atTop, ε ≤ relaxedPoissonMinimum n a/n := by
  have hα10 : limitingCenter 3 < 10 := by
    have h := (limitingCenter_bounds 3 (by decide)).2
    norm_num at h
    linarith
  obtain ⟨d,hαd,hd⟩ := exists_between (lt_min ha hα10)
  have hda : d < (a : ℝ) := hd.trans_le (min_le_left _ _)
  have hd10 : d < 10 := hd.trans_le (min_le_right _ _)
  obtain ⟨b,hαb,hbd⟩ := exists_between hαd
  have hb : 0 < b := (limitingCenter_pos 3 (by decide)).trans hαb
  have hd0 : 0 < d := hb.trans hbd
  let δ : ℝ := (d-b)/4
  have hδ : 0 < δ := div_pos (sub_pos.mpr hbd) (by norm_num)
  have hδd : b+4*δ = d := by dsimp [δ]; ring
  let bNN : ℝ≥0 := ⟨b,hb.le⟩
  obtain ⟨q,hq,hslope⟩ := deletionSlope_small hδ
  let ε : ℝ := (δ/d)/(2*(q : ℝ))
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,?_⟩
  have hprob := (auxiliaryPoissonProbability_supercritical (a := bNN) hαb).eventually
    (gt_mem_nhds (show (0 : ℝ) < δ/40 by positivity))
  have hsize : ∀ᶠ n : ℕ in atTop, 2/δ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (2/δ))
  filter_upwards [hprob,hsize,eventually_ge_atTop q] with n hP hnsize hnq
  have hn0 : 0 < n := hq.trans_le hnq
  let : NeZero n := ⟨hn0.ne'⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let r := n/q
  let t := ⌊d*(n : ℝ)⌋₊
  have htUpper : (t : ℝ) ≤ d*n := Nat.floor_le (by positivity)
  have htLower : (d-δ)*(n : ℝ) ≤ t := by
    have hf := Nat.sub_one_lt_floor (d*(n : ℝ))
    have hh := (div_le_iff₀ hδ).mp hnsize
    dsimp [t]
    nlinarith
  have hdδ : 0 < d-δ := by linarith
  have htR : (0 : ℝ) < t := (mul_pos hdδ hnR).trans_le htLower
  have ht : 0 < t := by exact_mod_cast htR
  have htM : t ≤ 20*n := by
    have h : (t : ℝ) ≤ 20*n := htUpper.trans
      (mul_le_mul_of_nonneg_right (by linarith : d ≤ 20) hnR.le)
    exact_mod_cast h
  have hta : (t : ℝ≥0) ≤ a*n := by
    apply NNReal.coe_le_coe.mp
    change (t : ℝ) ≤ (a : ℝ)*n
    exact htUpper.trans (mul_le_mul_of_nonneg_right hda.le hnR.le)
  have hzero := zero_lifetime_linear bNN hδ hnsize hP.le
  have hinc := deletion_increment_linear n q hq
  change deletionLifetimeMean n r - deletionLifetimeMean n 0 ≤ deletionSlope q*n at hinc
  have hmean : deletionLifetimeMean n r ≤ (b+2*δ)*n := by
    change deletionLifetimeMean n 0 ≤ (b+δ)*n at hzero
    have hs := mul_le_mul_of_nonneg_right hslope.le hnR.le
    linarith
  have hgap : δ/d ≤ 1-deletionLifetimeMean n r/t := by
    have he : 1-deletionLifetimeMean n r/t = (t-deletionLifetimeMean n r)/t := by
      field_simp
    rw [he, div_le_div_iff₀ hd0 htR]
    have hg : δ*(n : ℝ) ≤ (t : ℝ)-deletionLifetimeMean n r := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hg hd0.le
    have h2 := mul_le_mul_of_nonneg_left htUpper hδ.le
    nlinarith
  have hr : r ≤ n+1 := (Nat.div_le_self n q).trans (Nat.le_succ n)
  have hlower := mean_lifetime_energy_lower hr ht htM a hta
  change (r : ℝ)*(1-deletionLifetimeMean n r/t) ≤ relaxedPoissonMinimum n a at hlower
  have hquot := quotient_linear_lower hq hnq
  have hprod : ε*n ≤ (r : ℝ)*(δ/d) := by
    have h := mul_le_mul_of_nonneg_right hquot (div_nonneg hδ.le hd0.le)
    dsimp only [ε,r]
    convert h using 1
    ring
  apply (le_div_iff₀ hnR).mpr
  exact hprod.trans ((mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg r)).trans hlower)

end FixedClauseThreshold.Computability

end OAI
