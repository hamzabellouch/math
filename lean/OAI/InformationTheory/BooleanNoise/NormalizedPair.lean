import OAI.InformationTheory.BooleanNoise.Basic
import OAI.InformationTheory.BooleanNoise.PairEntropy
import OAI.InformationTheory.BooleanNoise.EntropySeries
import OAI.InformationTheory.BooleanNoise.InverseScalars
import OAI.InformationTheory.BooleanNoise.InverseRegularity
import OAI.InformationTheory.BooleanNoise.LShape
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

namespace OAI

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem hasSum_weighted_nonneg_of_single_crossing
    {x weight : ℕ → ℝ} {total : ℝ}
    (hs : HasSum x 0) (hws : HasSum (fun j => weight j * x j) total)
    (hw : Monotone weight)
    (hcross : ∀ i j, i ≤ j → 0 < x i → 0 ≤ x j) : 0 ≤ total := by
  classical
  by_cases hpos : ∃ j, 0 < x j
  · let k := Nat.find hpos
    have hk : 0 < x k := Nat.find_spec hpos
    have hbefore : ∀ j, j < k → x j ≤ 0 := by
      intro j hj
      exact le_of_not_gt (Nat.find_min hpos hj)
    have hafter : ∀ j, k ≤ j → 0 ≤ x j := fun j hj => hcross k j hj hk
    have hshift : HasSum (fun j => (weight j - weight k) * x j) total := by
      convert hws.sub (hs.mul_left (weight k)) using 1
      · ext j
        ring
      · ring
    apply hshift.nonneg
    intro j
    by_cases hj : j < k
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hw hj.le)) (hbefore j hj)
    · exact mul_nonneg (sub_nonneg.mpr (hw (le_of_not_gt hj)))
        (hafter j (le_of_not_gt hj))
  · have hx : ∀ j, x j ≤ 0 := fun j => le_of_not_gt (fun hj => hpos ⟨j, hj⟩)
    have hzero : ∀ j, x j = 0 := by
      intro j
      have hle : -x j ≤ (0 : ℝ) := by
        simpa using le_hasSum hs.neg j (fun i _ => neg_nonneg.mpr (hx i))
      linarith [hx j]
    exact hws.nonneg (fun j => by rw [hzero j]; simp)

theorem logconvex_single_crossing {z : ℕ → ℝ}
    (hz : ∀ j, 0 ≤ z j) (hz0 : z 0 ≤ 1)
    (hlog : ∀ j, z (j + 1) ^ 2 ≤ z j * z (j + 2))
    (i j : ℕ) (hij : i ≤ j) (hi : 1 < z i) : 1 < z j := by
  have hprevious : ∀ n, 1 < z (n + 1) → z n ≤ z (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro h
      exact hz0.trans h.le
    | succ n ih =>
      intro h
      change 1 < z (n + 2) at h
      change z (n + 1) ≤ z (n + 2)
      by_contra hnot
      have hdesc : z (n + 2) < z (n + 1) := lt_of_not_ge hnot
      have hprev := ih (h.trans hdesc)
      have hmul := mul_le_mul_of_nonneg_right hprev (hz (n + 2))
      have hsq := hlog n
      nlinarith
  have hnext : ∀ n, 1 < z n → 1 < z (n + 1) := by
    intro n hn
    cases n with
    | zero => exact (not_lt_of_ge hz0 hn).elim
    | succ n =>
      have hprev := hprevious n hn
      have hmul := mul_le_mul_of_nonneg_right hprev (hz (n + 2))
      have hsq := hlog n
      change 1 < z (n + 2)
      nlinarith
  exact Nat.le_induction hi (fun n _ hn => hnext n hn) j hij

theorem logconvex_mul_pow {m : ℕ → ℝ}
    (hlog : ∀ j, m (j + 1) ^ 2 ≤ m j * m (j + 2)) (c : ℝ) (j : ℕ) :
    (m (j + 1) * c ^ (j + 1)) ^ 2 ≤
      (m j * c ^ j) * (m (j + 2) * c ^ (j + 2)) := by
  calc
    (m (j + 1) * c ^ (j + 1)) ^ 2 =
        m (j + 1) ^ 2 * (c ^ (j + 1)) ^ 2 := mul_pow _ _ _
    _ ≤ (m j * m (j + 2)) * (c ^ (j + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_right (hlog j) (sq_nonneg _)
    _ = (m j * c ^ j) * (m (j + 2) * c ^ (j + 2)) := by
      simp only [pow_add, pow_one, pow_two]
      ring

theorem logconvex_geometric_single_crossing {m : ℕ → ℝ}
    (hm : ∀ j, 0 ≤ m j) (hm0 : m 0 ≤ 1)
    (hlog : ∀ j, m (j + 1) ^ 2 ≤ m j * m (j + 2))
    {t : ℝ} (ht : 0 ≤ t) (i j : ℕ) (hij : i ≤ j)
    (hi : t ^ i < m i) : t ^ j < m j := by
  by_cases ht0 : t = 0
  · subst t
    by_cases hi0 : i = 0
    · subst i
      simp only [pow_zero] at hi
      exact (not_lt_of_ge hm0 hi).elim
    · have hmi : 0 < m i := by simpa [zero_pow hi0] using hi
      have hpositive : ∀ n, 0 < m (n + 1) → 0 < m (n + 2) := by
        intro n hn
        have hsq := hlog n
        have hm0 := hm n
        have hm2 := hm (n + 2)
        nlinarith
      have htail : ∀ k, i ≤ k → 0 < m k := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base => exact hmi
        | succ k hk ih =>
          obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          exact hpositive l ih
      have hj0 : j ≠ 0 := by omega
      simpa [zero_pow hj0] using htail j hij
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hzi : 1 < m i * (t⁻¹) ^ i := by
      rw [inv_pow, ← div_eq_mul_inv]
      exact (lt_div_iff₀ (pow_pos htpos i)).mpr (by simpa using hi)
    have hzj := logconvex_single_crossing
      (z := fun k => m k * (t⁻¹) ^ k)
      (fun k => mul_nonneg (hm k) (pow_nonneg (inv_nonneg.mpr ht) k))
      (by simpa using hm0) (logconvex_mul_pow hlog (t⁻¹)) i j hij hzi
    change 1 < m j * (t⁻¹) ^ j at hzj
    rw [inv_pow, ← div_eq_mul_inv] at hzj
    simpa only [one_mul] using (lt_div_iff₀ (pow_pos htpos j)).mp hzj

theorem weighted_hasSum_le_of_logconvex
    {m c weight : ℕ → ℝ} {t mass moment geometricMoment : ℝ}
    (hm : ∀ j, 0 ≤ m j) (hm0 : m 0 ≤ 1)
    (hlog : ∀ j, m (j + 1) ^ 2 ≤ m j * m (j + 2))
    (hc : ∀ j, 0 ≤ c j) (hw : Monotone weight) (ht : 0 ≤ t)
    (hs : HasSum (fun k => c k * m (k + 1)) mass)
    (hts : HasSum (fun k => c k * t ^ (k + 1)) mass)
    (hws : HasSum (fun k => weight k * (c k * m (k + 1))) moment)
    (hwts : HasSum (fun k => weight k * (c k * t ^ (k + 1))) geometricMoment) :
    geometricMoment ≤ moment := by
  have hdiff : HasSum (fun k => c k * (m (k + 1) - t ^ (k + 1))) 0 := by
    convert hs.sub hts using 1
    · ext k
      ring
    · ring
  have hwdiff : HasSum
      (fun k => weight k * (c k * (m (k + 1) - t ^ (k + 1))))
      (moment - geometricMoment) := by
    convert hws.sub hwts using 1
    ext k
    ring
  have hnonneg := hasSum_weighted_nonneg_of_single_crossing hdiff hwdiff hw ?_
  · linarith
  · intro i j hij hi
    have hmi : t ^ (i + 1) < m (i + 1) := by
      have hci := hc i
      nlinarith
    have hmj := logconvex_geometric_single_crossing hm hm0 hlog ht
      (i + 1) (j + 1) (Nat.add_le_add_right hij 1) hmi
    exact mul_nonneg (hc j) (sub_nonneg.mpr hmj.le)

noncomputable def rawPairMoment (a b : ℝ) (j : ℕ) : ℝ :=
  (1 + a) / 2 * (b / (1 + a)) ^ (2 * j) +
    (1 - a) / 2 * (b / (1 - a)) ^ (2 * j)

noncomputable def normalizedPairMoment (a b : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else rawPairMoment a b j / (1 - a ^ 2)

@[simp]
theorem normalizedPairMoment_zero (a b : ℝ) : normalizedPairMoment a b 0 = 1 := by
  simp [normalizedPairMoment]

@[simp]
theorem normalizedPairMoment_succ (a b : ℝ) (j : ℕ) :
    normalizedPairMoment a b (j + 1) = rawPairMoment a b (j + 1) / (1 - a ^ 2) := by
  simp [normalizedPairMoment]

theorem normalized_pair_scale_pos {a b : ℝ} (hab : |a| + |b| < 1) : 0 < 1 - a ^ 2 := by
  have h := mul_pos (pair_denom_add_pos a b hab) (pair_denom_sub_pos a b hab)
  nlinarith

theorem abs_lt_normalized_pair_scale {a b : ℝ} (hab : |a| + |b| < 1) :
    |b| < 1 - a ^ 2 := by
  have ha : |a| < 1 := lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) hab
  have hm := mul_nonneg (abs_nonneg a) (show 0 ≤ 1 - |a| by linarith)
  nlinarith [sq_abs a]

theorem two_atom_moment_logconvex (w u p q : ℝ)
    (hw : 0 ≤ w) (hu : 0 ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q) (j : ℕ) :
    (w * p ^ (j + 1) + u * q ^ (j + 1)) ^ 2 ≤
      (w * p ^ j + u * q ^ j) * (w * p ^ (j + 2) + u * q ^ (j + 2)) := by
  have hnonneg : 0 ≤ w * u * p ^ j * q ^ j * (p - q) ^ 2 := by positivity
  have heq :
      (w * p ^ j + u * q ^ j) * (w * p ^ (j + 2) + u * q ^ (j + 2)) -
          (w * p ^ (j + 1) + u * q ^ (j + 1)) ^ 2 =
        w * u * p ^ j * q ^ j * (p - q) ^ 2 := by
    simp only [pow_add, pow_one, pow_two]
    ring
  linarith

theorem rawPairMoment_logconvex {a b : ℝ} (hab : |a| + |b| < 1) (j : ℕ) :
    rawPairMoment a b (j + 1) ^ 2 ≤
      rawPairMoment a b j * rawPairMoment a b (j + 2) := by
  simpa only [rawPairMoment, ← pow_mul] using
    two_atom_moment_logconvex ((1 + a) / 2) ((1 - a) / 2)
      ((b / (1 + a)) ^ 2) ((b / (1 - a)) ^ 2)
      (le_of_lt (div_pos (pair_denom_add_pos a b hab) (by norm_num)))
      (le_of_lt (div_pos (pair_denom_sub_pos a b hab) (by norm_num)))
      (sq_nonneg _) (sq_nonneg _) j

theorem normalizedPairMoment_nonneg {a b : ℝ} (hab : |a| + |b| < 1) (j : ℕ) :
    0 ≤ normalizedPairMoment a b j := by
  unfold normalizedPairMoment
  split_ifs with hj
  · norm_num
  · apply div_nonneg _ (normalized_pair_scale_pos hab).le
    unfold rawPairMoment
    apply add_nonneg
    · apply mul_nonneg (by linarith [pair_denom_add_pos a b hab])
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) j
    · apply mul_nonneg (by linarith [pair_denom_sub_pos a b hab])
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) j

theorem normalizedPairMoment_one {a b : ℝ} (hab : |a| + |b| < 1) :
    normalizedPairMoment a b 1 = b ^ 2 / (1 - a ^ 2) ^ 2 := by
  have hp := ne_of_gt (pair_denom_add_pos a b hab)
  have hm := ne_of_gt (pair_denom_sub_pos a b hab)
  have hA := ne_of_gt (normalized_pair_scale_pos hab)
  norm_num [normalizedPairMoment, rawPairMoment]
  field_simp
  ring

theorem normalizedPairMoment_two {a b : ℝ} (hab : |a| + |b| < 1) :
    normalizedPairMoment a b 2 = b ^ 4 * (1 + 3 * a ^ 2) / (1 - a ^ 2) ^ 4 := by
  have hp := ne_of_gt (pair_denom_add_pos a b hab)
  have hm := ne_of_gt (pair_denom_sub_pos a b hab)
  have hA := ne_of_gt (normalized_pair_scale_pos hab)
  norm_num [normalizedPairMoment, rawPairMoment]
  field_simp
  ring

theorem normalizedPairMoment_logconvex {a b : ℝ} (hab : |a| + |b| < 1) (j : ℕ) :
    normalizedPairMoment a b (j + 1) ^ 2 ≤
      normalizedPairMoment a b j * normalizedPairMoment a b (j + 2) := by
  cases j with
  | zero =>
    rw [normalizedPairMoment_zero, one_mul, normalizedPairMoment_one hab,
      normalizedPairMoment_two hab]
    calc
      (b ^ 2 / (1 - a ^ 2) ^ 2) ^ 2 = b ^ 4 / (1 - a ^ 2) ^ 4 := by
        rw [div_pow, ← pow_mul, ← pow_mul]
      _ ≤ b ^ 4 * (1 + 3 * a ^ 2) / (1 - a ^ 2) ^ 4 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [show 0 ≤ 3 * a ^ 2 * b ^ 4 by positivity]
  | succ j =>
    change (rawPairMoment a b (j + 2) / (1 - a ^ 2)) ^ 2 ≤
      (rawPairMoment a b (j + 1) / (1 - a ^ 2)) *
        (rawPairMoment a b (j + 3) / (1 - a ^ 2))
    rw [div_pow, div_mul_div_comm, ← pow_two (1 - a ^ 2)]
    exact div_le_div_of_nonneg_right (rawPairMoment_logconvex hab (j + 1))
      (sq_nonneg (1 - a ^ 2))

theorem normalizedPairMoment_one_lt_one {a b : ℝ} (hab : |a| + |b| < 1) :
    normalizedPairMoment a b 1 < 1 := by
  rw [normalizedPairMoment_one hab]
  have hA := normalized_pair_scale_pos hab
  have hb := abs_lt_normalized_pair_scale hab
  have hprod := mul_pos (sub_pos.mpr hb) (add_pos_of_pos_of_nonneg hA (abs_nonneg b))
  apply (div_lt_one (sq_pos_of_pos hA)).mpr
  nlinarith [sq_abs b]

theorem hasSum_normalizedPairEntropy {a b : ℝ} (hab : |a| + |b| < 1) :
    HasSum (fun k => psiCoeff k * normalizedPairMoment a b (k + 1))
      (pairEntropyGap a b / (1 - a ^ 2)) := by
  have hp := hasSum_psi (abs_lt.mpr (pair_ratio_add_mem_Ioo a b hab))
  have hm := hasSum_psi (abs_lt.mpr (pair_ratio_sub_mem_Ioo a b hab))
  have hs := ((hp.mul_left ((1 + a) / 2)).add
    (hm.mul_left ((1 - a) / 2))).div_const (1 - a ^ 2)
  convert hs using 1
  · ext k
    rw [normalizedPairMoment_succ]
    unfold rawPairMoment
    ring
  · rw [pairEntropyGap_weighted a b hab]

theorem hasSum_normalizedPairDissipation {a b : ℝ} (hab : |a| + |b| < 1) :
    HasSum (fun k : ℕ => (2 * ((k : ℝ) + 1)) *
      (psiCoeff k * normalizedPairMoment a b (k + 1)))
      (pairDissipation a b / (1 - a ^ 2)) := by
  have hp := hasSum_mul_artanh (abs_lt.mpr (pair_ratio_add_mem_Ioo a b hab))
  have hm := hasSum_mul_artanh (abs_lt.mpr (pair_ratio_sub_mem_Ioo a b hab))
  have hs := ((hp.mul_left ((1 + a) / 2)).add
    (hm.mul_left ((1 - a) / 2))).div_const (1 - a ^ 2)
  convert hs using 1
  · ext k
    rw [normalizedPairMoment_succ]
    unfold rawPairMoment
    ring
  · rw [pairDissipation_weighted a b hab]

theorem normalized_pair_dissipation_ge_of_psi {a b v : ℝ}
    (hab : |a| + |b| < 1) (hv : |v| < 1)
    (hvpsi : psi v = pairEntropyGap a b / (1 - a ^ 2)) :
    v * Real.artanh v ≤ pairDissipation a b / (1 - a ^ 2) := by
  apply weighted_hasSum_le_of_logconvex
    (m := normalizedPairMoment a b) (c := psiCoeff)
    (weight := fun k => 2 * ((k : ℝ) + 1)) (t := v ^ 2)
    (normalizedPairMoment_nonneg hab)
    (by simp) (normalizedPairMoment_logconvex hab) psiCoeff_nonneg
  · intro i j hij
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    dsimp
    linarith
  · exact sq_nonneg v
  · exact hasSum_normalizedPairEntropy hab
  · simpa only [← pow_mul, hvpsi] using hasSum_psi hv
  · exact hasSum_normalizedPairDissipation hab
  · simpa only [← pow_mul, mul_assoc] using hasSum_mul_artanh hv

theorem normalized_pair_dissipation_ge_r {a b : ℝ} (hab : |a| + |b| < 1) :
    r (pairEntropyGap a b / (1 - a ^ 2)) ≤ pairDissipation a b / (1 - a ^ 2) := by
  have hs0 := pairEntropyGap_div_variance_nonneg a b hab
  have hs1 := pairEntropyGap_div_variance_lt_ell a b hab
  have hv := psiInv_mem_Ico hs0 hs1
  exact normalized_pair_dissipation_ge_of_psi hab
    (by simpa only [abs_of_nonneg hv.1] using hv.2) (psi_psiInv hs0 hs1)

private theorem normalized_pair_bound_of_antitone
    (hanti : AntitoneOn L (Set.Ioi 0)) {a b : ℝ} (hab : |a| + |b| < 1) :
    (1 - a ^ 2) *
        L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
      pairDissipation a b - 2 * pairEntropyGap a b := by
  have hA := normalized_pair_scale_pos hab
  have hs0 := pairEntropyGap_div_variance_nonneg a b hab
  have hs1 := pairEntropyGap_div_variance_lt_ell a b hab
  have hlow : 0 < ell - pairEntropyGap a b / (1 - a ^ 2) := sub_pos.mpr hs1
  have ha : |a| ≤ 1 :=
    (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) hab).le
  have hH := ell_mul_one_sub_sq_le_entropy ha
  have hratio : ell - pairEntropyGap a b / (1 - a ^ 2) ≤
      ((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2) := by
    apply (le_div_iff₀ hA).mpr
    calc
      (ell - pairEntropyGap a b / (1 - a ^ 2)) * (1 - a ^ 2) =
          ell * (1 - a ^ 2) - pairEntropyGap a b := by
        field_simp
      _ ≤ entropy a - pairEntropyGap a b := sub_le_sub_right hH _
      _ = (entropy (a + b) + entropy (a - b)) / 2 := by
        unfold pairEntropyGap
        ring
  have hL := hanti hlow (hlow.trans_le hratio) hratio
  rw [L_ell_sub hs0 hs1] at hL
  have hr := normalized_pair_dissipation_ge_r hab
  have hbound :
      L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
        (pairDissipation a b - 2 * pairEntropyGap a b) / (1 - a ^ 2) := by
    calc
      _ ≤ r (pairEntropyGap a b / (1 - a ^ 2)) -
          2 * (pairEntropyGap a b / (1 - a ^ 2)) := hL
      _ ≤ pairDissipation a b / (1 - a ^ 2) -
          2 * (pairEntropyGap a b / (1 - a ^ 2)) := sub_le_sub_right hr _
      _ = _ := by ring
  simpa only [mul_comm] using (le_div_iff₀ hA).mp hbound

theorem normalized_pair_bound {a b : ℝ} (hab : |a| + |b| < 1) :
    (1 - a ^ 2) *
        L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
      pairDissipation a b - 2 * pairEntropyGap a b :=
  normalized_pair_bound_of_antitone antitoneOn_L hab

end LeanBlast.CourtadeKumar

end OAI
