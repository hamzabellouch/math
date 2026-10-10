import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePosterior

variable {ι : Type*} [Fintype ι]

def weight (energy signal : ι → ℝ) (t : ℝ) (s : ι) : ℝ :=
  Real.exp (energy s + t * signal s)

def partition (energy signal : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ s, weight energy signal t s

def mean (energy signal observable : ι → ℝ) (t : ℝ) : ℝ :=
  (∑ s, observable s * weight energy signal t s) / partition energy signal t

def mass (energy signal : ι → ℝ) (t : ℝ) (s : ι) : ℝ :=
  weight energy signal t s / partition energy signal t

omit [Fintype ι] in
lemma weight_pos (energy signal : ι → ℝ) (t : ℝ) (s : ι) :
    0 < weight energy signal t s := Real.exp_pos _

lemma partition_pos [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) :
    0 < partition energy signal t := by
  exact Finset.sum_pos (fun s _ => weight_pos energy signal t s) Finset.univ_nonempty

lemma partition_ne_zero [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) :
    partition energy signal t ≠ 0 := ne_of_gt (partition_pos energy signal t)

lemma mass_pos [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) (s : ι) :
    0 < mass energy signal t s :=
  div_pos (weight_pos energy signal t s) (partition_pos energy signal t)

lemma sum_mass [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) :
    ∑ s, mass energy signal t s = 1 := by
  simp only [mass, ← Finset.sum_div]
  change partition energy signal t / partition energy signal t = 1
  exact div_self (partition_ne_zero energy signal t)

lemma mean_eq_sum_mass (energy signal observable : ι → ℝ) (t : ℝ) :
    mean energy signal observable t = ∑ s, observable s * mass energy signal t s := by
  simp only [mean, mass, ← mul_div_assoc, ← Finset.sum_div]

lemma mean_const [Nonempty ι] (energy signal : ι → ℝ) (t c : ℝ) :
    mean energy signal (fun _ => c) t = c := by
  rw [mean_eq_sum_mass, ← Finset.mul_sum, sum_mass, mul_one]

omit [Fintype ι] in
lemma hasDerivAt_weight (energy signal : ι → ℝ) (t : ℝ) (s : ι) :
    HasDerivAt (fun x => weight energy signal x s)
      (signal s * weight energy signal t s) t := by
  simpa [weight, mul_comm] using
    (((hasDerivAt_id t).mul_const (signal s)).const_add (energy s)).exp

lemma hasDerivAt_partition (energy signal : ι → ℝ) (t : ℝ) :
    HasDerivAt (partition energy signal)
      (∑ s, signal s * weight energy signal t s) t := by
  exact HasDerivAt.fun_sum (fun s _ => hasDerivAt_weight energy signal t s)

theorem hasDerivAt_mean [Nonempty ι] (energy signal observable : ι → ℝ) (t : ℝ) :
    HasDerivAt (mean energy signal observable)
      (mean energy signal (fun s => observable s * signal s) t -
        mean energy signal observable t * mean energy signal signal t) t := by
  have hn : HasDerivAt (fun x => ∑ s, observable s * weight energy signal x s)
      (∑ s, (observable s * signal s) * weight energy signal t s) t := by
    simpa only [mul_assoc] using HasDerivAt.fun_sum
      (fun s (_ : s ∈ Finset.univ) =>
        (hasDerivAt_weight energy signal t s).const_mul (observable s))
  convert! hn.div (hasDerivAt_partition energy signal t)
    (partition_ne_zero energy signal t) using 1
  dsimp [mean]
  field_simp

lemma hasDerivAt_log_partition [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun x => Real.log (partition energy signal x))
      (mean energy signal signal t) t := by
  simpa only [mean] using (hasDerivAt_partition energy signal t).log
    (partition_ne_zero energy signal t)

lemma hasDerivAt_mass [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) (s : ι) :
    HasDerivAt (fun x => mass energy signal x s)
      ((signal s - mean energy signal signal t) * mass energy signal t s) t := by
  convert! (hasDerivAt_weight energy signal t s).div
    (hasDerivAt_partition energy signal t) (partition_ne_zero energy signal t) using 1
  dsimp [mass, mean]
  field_simp [partition_ne_zero energy signal t]

lemma variance_eq_sum [Nonempty ι] (energy signal observable : ι → ℝ) (t : ℝ) :
    mean energy signal (fun s => (observable s) ^ 2) t -
        (mean energy signal observable t) ^ 2 =
      ∑ s, (observable s - mean energy signal observable t) ^ 2 *
        mass energy signal t s := by
  have heq (s : ι) :
      (observable s - mean energy signal observable t) ^ 2 * mass energy signal t s =
      (observable s) ^ 2 * mass energy signal t s -
        (2 * mean energy signal observable t) * (observable s * mass energy signal t s) +
        (mean energy signal observable t) ^ 2 * mass energy signal t s := by ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_mass,
    ← mean_eq_sum_mass, ← mean_eq_sum_mass]
  ring

lemma variance_nonneg [Nonempty ι] (energy signal observable : ι → ℝ) (t : ℝ) :
    0 ≤ mean energy signal (fun s => (observable s) ^ 2) t -
      (mean energy signal observable t) ^ 2 := by
  rw [variance_eq_sum]
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (sq_nonneg _) (mass_pos energy signal t s).le)

lemma variance_pos [Nonempty ι] (energy signal observable : ι → ℝ) (t : ℝ)
    (h : ∃ i j, observable i ≠ observable j) :
    0 < mean energy signal (fun s => (observable s) ^ 2) t -
      (mean energy signal observable t) ^ 2 := by
  rw [variance_eq_sum]
  apply Finset.sum_pos'
  · intro s _
    exact mul_nonneg (sq_nonneg _) (mass_pos energy signal t s).le
  · obtain ⟨i, j, hij⟩ := h
    have hex : ∃ s, observable s ≠ mean energy signal observable t := by
      by_contra! hn
      exact hij ((hn i).trans (hn j).symm)
    obtain ⟨s, hs⟩ := hex
    exact ⟨s, Finset.mem_univ s,
      mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hs)) (mass_pos energy signal t s)⟩

theorem hasDerivAt_spin_mean [Nonempty ι] (energy spin : ι → ℝ) (t : ℝ)
    (hspin : ∀ s, spin s = -1 ∨ spin s = 1) :
    HasDerivAt (mean energy spin spin)
      (1 - (mean energy spin spin t) ^ 2) t := by
  have heq : (fun s => spin s * spin s) = (fun _ : ι => (1 : ℝ)) := by
    funext s
    rcases hspin s with hs | hs <;> simp [hs]
  have hd := hasDerivAt_mean energy spin spin t
  rw [heq, mean_const] at hd
  simpa only [← sq] using hd

theorem mean_monotone [Nonempty ι] (energy signal : ι → ℝ) :
    Monotone (mean energy signal signal) := by
  apply monotone_of_deriv_nonneg
  · intro t
    exact (hasDerivAt_mean energy signal signal t).differentiableAt
  · intro t
    rw [(hasDerivAt_mean energy signal signal t).deriv]
    simpa only [← sq] using variance_nonneg energy signal signal t

lemma mean_lt [Nonempty ι] (energy signal observable : ι → ℝ) (t c : ℝ)
    (hle : ∀ s, observable s ≤ c) (hlt : ∃ s, observable s < c) :
    mean energy signal observable t < c := by
  apply (div_lt_iff₀ (partition_pos energy signal t)).2
  rw [partition, Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro s _
    exact mul_le_mul_of_nonneg_right (hle s) (weight_pos energy signal t s).le
  · obtain ⟨s, hs⟩ := hlt
    exact ⟨s, Finset.mem_univ s, mul_lt_mul_of_pos_right hs (weight_pos energy signal t s)⟩

lemma lt_mean [Nonempty ι] (energy signal observable : ι → ℝ) (t c : ℝ)
    (hle : ∀ s, c ≤ observable s) (hlt : ∃ s, c < observable s) :
    c < mean energy signal observable t := by
  apply (lt_div_iff₀ (partition_pos energy signal t)).2
  rw [partition, Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro s _
    exact mul_le_mul_of_nonneg_right (hle s) (weight_pos energy signal t s).le
  · obtain ⟨s, hs⟩ := hlt
    exact ⟨s, Finset.mem_univ s, mul_lt_mul_of_pos_right hs (weight_pos energy signal t s)⟩

theorem spin_mean_mem_Ioo [Nonempty ι] (energy signal spin : ι → ℝ) (t : ℝ)
    (hspin : ∀ s, spin s = -1 ∨ spin s = 1)
    (hneg : ∃ s, spin s = -1) (hpos : ∃ s, spin s = 1) :
    mean energy signal spin t ∈ Set.Ioo (-1 : ℝ) 1 := by
  constructor
  · apply lt_mean energy signal spin t (-1)
    · intro s
      rcases hspin s with hs | hs <;> simp [hs]
    · obtain ⟨s, hs⟩ := hpos
      exact ⟨s, by simp [hs]⟩
  · apply mean_lt energy signal spin t 1
    · intro s
      rcases hspin s with hs | hs <;> simp [hs]
    · obtain ⟨s, hs⟩ := hneg
      exact ⟨s, by simp [hs]⟩

end Problem367.FinitePosterior

end

end OAI
