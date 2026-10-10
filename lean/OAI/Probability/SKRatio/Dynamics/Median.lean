import Mathlib
import OAI.Probability.SKRatio.FiniteChain.DiscreteDistanceNonneg
import OAI.Probability.SKRatio.Calculus.GibbsMeanCLM

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter
namespace SKRatio.Calculus

@[simp] lemma continuousKernel_zero {n : ℕ} (J : Interaction n) :
    continuousKernel J 0 = (1 : Matrix (Spin n) (Spin n) ℝ) := by
  funext x y
  simp [continuousKernel, Matrix.one_apply]

@[simp] lemma continuousDistance_zero {n : ℕ} (g : Disorder n) :
    continuousDistance g 0 = discreteDistance g 0 := by
  simp [continuousDistance, discreteDistance]

lemma continuousKernel_continuous_time {n : ℕ} (J : Interaction n) (x y : Spin n) :
    Continuous (fun t : ℝ => continuousKernel J t x y) := by
  unfold continuousKernel
  exact (continuous_apply x).comp ((semigroup_continuous J).clm_apply continuous_const)

lemma continuousDistance_continuous_time {n : ℕ} (g : Disorder n) :
    Continuous (continuousDistance g) := by
  have h : Continuous (Finset.univ.sup' Finset.univ_nonempty
      (fun (x : Spin n) (t : ℝ) =>
        totalVariation (continuousKernel (coupling g) t x) (mass g 0))) := by
    apply Continuous.finset_sup'
    intro x _
    unfold totalVariation
    apply continuous_const.mul
    exact continuous_finsetSum _ (fun y _ =>
      ((continuousKernel_continuous_time _ x y).sub continuous_const).abs)
  exact h.congr (fun t => Finset.sup'_apply _ _ t)

lemma continuousKernel_pos {n : ℕ} (g : Disorder n) {t : ℝ} (ht : 0 < t)
    (x y : Spin n) : 0 < continuousKernel (coupling g) t x y := by
  by_cases hn : n = 0
  · subst n
    have h := continuousKernel_sum (coupling g) t x
    rw [Fintype.sum_subsingleton _ y] at h
    linarith only [h]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have hs := continuousKernel_poisson_hasSum hn' g t x y
    have hpos : 0 < Real.exp (-(n:ℝ)*t) * ((n:ℝ)*t)^n /
        (n.factorial:ℝ) * (transition g^n) x y := by
      exact mul_pos (div_pos (mul_pos (Real.exp_pos _) (pow_pos
        (mul_pos (Nat.cast_pos.mpr hn') ht) _)) (Nat.cast_pos.mpr (Nat.factorial_pos _)))
        (transition_n_pos g x y)
    exact hpos.trans_le (hs.tsum_eq ▸ hs.summable.le_tsum n (fun k _ => by
      exact mul_nonneg (div_nonneg (mul_nonneg (Real.exp_nonneg _)
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) ht.le) _)) (Nat.cast_nonneg _))
        ((transition_pow_stochastic g k).1 x y)))

lemma continuousKernel_nat {n : ℕ} (J : Interaction n) (k : ℕ) :
    continuousKernel J (k : ℝ) = (continuousKernel J 1)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, continuousKernel_add, ih, pow_succ]

lemma exists_continuous_geometric_bound {n : ℕ} (g : Disorder n) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ k : ℕ, continuousDistance g k ≤ r^k := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_geometric_block_bound
    (continuousKernel (coupling g) 1) (continuousKernel_stochastic _ (by norm_num))
    (mass g 0) (mass_nonneg g 0) (sum_mass g 0) 1
    (by simpa only [pow_one] using continuousKernel_pos g (by norm_num : (0:ℝ)<1))
    (by simpa only [pow_one] using continuousKernel_stationary g 1)
  refine ⟨r, hr0, hr1, fun k => ?_⟩
  unfold continuousDistance
  rw [continuousKernel_nat]
  apply Finset.sup'_le
  intro x _
  simpa only [one_mul] using hr k x

lemma exists_continuous_mixing_time {n : ℕ} (g : Disorder n) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 ≤ t ∧ continuousDistance g t ≤ ε := by
  obtain ⟨r, hr0, hr1, hbound⟩ := exists_continuous_geometric_bound g
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).eventually
    (gt_mem_nhds hε)).exists
  exact ⟨k, Nat.cast_nonneg _, (hbound k).trans hk.le⟩

def medianTime {n : ℕ} (g : Disorder n) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ continuousDistance g t ≤ 1/2}

lemma medianTime_mem {n : ℕ} (g : Disorder n) :
    0 ≤ medianTime g ∧ continuousDistance g (medianTime g) ≤ 1/2 := by
  apply IsClosed.csInf_mem
    ((isClosed_le continuous_const continuous_id).inter
      (isClosed_le (continuousDistance_continuous_time g) continuous_const))
    (exists_continuous_mixing_time g (by norm_num))
    ⟨0, fun _ ht => ht.1⟩

lemma medianTime_le_iff {n : ℕ} (g : Disorder n) {t : ℝ} (ht : 0 ≤ t) :
    medianTime g ≤ t ↔ continuousDistance g t ≤ 1/2 := by
  constructor
  · intro h
    exact (continuousDistance_antitone g (medianTime_mem g).1 h).trans (medianTime_mem g).2
  · intro h
    exact csInf_le ⟨0, fun _ h => h.1⟩ ⟨ht, h⟩

lemma before_median {n : ℕ} (g : Disorder n) {t : ℝ} (ht : 0 ≤ t)
    (hbefore : t < medianTime g) : 1/2 < continuousDistance g t := by
  exact lt_of_not_ge (fun h => not_le_of_gt hbefore ((medianTime_le_iff g ht).mpr h))

lemma medianTime_pos {n : ℕ} (g : Disorder n) (hn : 2 ≤ n) : 0 < medianTime g := by
  have hid : 1/2 < continuousDistance g 0 := by
    rw [continuousDistance_zero]
    have hpow : (1/2:ℝ)^n ≤ (1/2:ℝ)^2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    have h := discreteDistance_zero_lower g
    norm_num at hpow
    linarith only [hpow, h]
  exact lt_of_not_ge (fun h => not_le_of_gt hid
    ((medianTime_le_iff g (le_refl 0)).mp h))

lemma continuousDistance_median {n : ℕ} (g : Disorder n) (hn : 2 ≤ n) :
    continuousDistance g (medianTime g) = 1/2 := by
  apply le_antisymm (medianTime_mem g).2
  by_contra h
  have hlt : continuousDistance g (medianTime g) < 1/2 := lt_of_not_ge h
  have hopen : IsOpen {t : ℝ | continuousDistance g t < 1/2} :=
    isOpen_lt (continuousDistance_continuous_time g) continuous_const
  obtain ⟨l, u, hmu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hlt)
  have hm : max 0 l < medianTime g := max_lt (medianTime_pos g hn) hmu.1
  obtain ⟨y, hy₀, hym⟩ := exists_between hm
  have hy : 0 ≤ y := (le_max_left 0 l).trans hy₀.le
  have hylt : continuousDistance g y < 1/2 :=
    hsub ⟨(le_max_right 0 l).trans_lt hy₀, hym.trans hmu.2⟩
  exact not_lt_of_gt (before_median g hy hym) hylt

lemma median_cutoff_sides_of_lag {n : ℕ} (g : Disorder n)
    {c C b δ : ℝ} (hc : 0 < c) (hb : 0 < b) (hb' : b < 1)
    (hδ : δ < 1/2) (hn : 1 < n)
    (hscale : c * Real.log n ≤ medianTime g ∧ medianTime g ≤ C * Real.log n)
    (hlag : ∀ t : ℝ, 0 ≤ t →
      t + (b*c/2)*Real.log n ≤ ((1+b)*C)*Real.log n →
      continuousDistance g t ≤ 1-δ →
      continuousDistance g (t+(b*c/2)*Real.log n) ≤ δ) :
    1-δ < continuousDistance g ((1-b)*medianTime g) ∧
      continuousDistance g ((1+b)*medianTime g) ≤ δ := by
  let s : ℝ := (b*c/2)*Real.log n
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hs : 0 < s := by dsimp [s]; positivity
  have hm : 0 ≤ medianTime g := (medianTime_mem g).1
  have hsmed : s ≤ b*medianTime g/2 := by
    have h := mul_le_mul_of_nonneg_left hscale.1 (div_nonneg hb.le (by norm_num : (0:ℝ)≤2))
    dsimp [s]
    nlinarith only [h]
  have hshift : medianTime g+s ≤ (1+b)*medianTime g := by nlinarith only [hsmed, hs]
  have hhor : medianTime g+s ≤ ((1+b)*C)*Real.log n := by
    calc
      _ ≤ (1+b)*medianTime g := hshift
      _ ≤ (1+b)*(C*Real.log n) :=
        mul_le_mul_of_nonneg_left hscale.2 (by linarith)
      _ = _ := by ring
  have hlo : 0 ≤ (1-b)*medianTime g := mul_nonneg (by linarith) hm
  have hlobefore : (1-b)*medianTime g+s < medianTime g := by
    nlinarith only [hsmed, hs]
  constructor
  · by_contra h
    have ht := hlag ((1-b)*medianTime g) hlo
      ((le_of_lt hlobefore).trans ((le_add_of_nonneg_right hs.le).trans hhor))
      (le_of_not_gt h)
    have hbefore := before_median g (add_nonneg hlo hs.le) hlobefore
    exact not_lt_of_ge (ht.trans hδ.le) hbefore
  · have hcmed : continuousDistance g (medianTime g) ≤ 1-δ := by
      linarith only [(medianTime_mem g).2, hδ]
    exact (continuousDistance_antitone g (add_nonneg hm hs.le) hshift).trans
      (hlag (medianTime g) hm hhor hcmed)

lemma uniform_continuous_cutoff_of_positive_lag
    (G : ∀ n : ℕ, Set (Disorder n)) {c C : ℝ} (hc : 0 < c)
    (hscale : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      c*Real.log n ≤ medianTime g ∧ medianTime g ≤ C*Real.log n)
    (hlag : ∀ ε α D δ : ℝ, 0 < ε → 0 < α → 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t : ℝ,
      0 ≤ t → t+α*Real.log n ≤ D*Real.log n →
      continuousDistance g t ≤ 1-ε → continuousDistance g (t+α*Real.log n) ≤ δ)
    {b : ℝ} (hb : 0 < b) (hb' : b < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      1-δ < continuousDistance g ((1-b)*medianTime g) ∧
        continuousDistance g ((1+b)*medianTime g) ≤ δ := by
  let e : ℝ := min δ (1/4)
  have he : 0 < e := lt_min hδ (by norm_num)
  have heδ : e ≤ δ := min_le_left _ _
  have hehalf : e < 1/2 := (min_le_right _ _).trans_lt (by norm_num)
  have ha : 0 < b*c/2 := by positivity
  filter_upwards [hscale, hlag e (b*c/2) ((1+b)*C) e he ha he,
    eventually_gt_atTop 1] with n hnscale hnlag hn
  intro g hg
  obtain ⟨hl, hu⟩ := median_cutoff_sides_of_lag g hc hb hb' hehalf hn
    (hnscale g hg) (hnlag g hg)
  exact ⟨(by linarith only [heδ, hl]), hu.trans heδ⟩

end SKRatio.Calculus

end
end

end OAI
