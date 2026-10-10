import OAI.MathematicalPhysics.AlternatingFlow.Profiles

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Profiles

noncomputable def pulse (t : ℝ) : ℝ := deriv clock t

lemma pulse_smooth : ContDiff ℝ ∞ pulse := by
  exact ContDiff.deriv' (by simpa using clock_smooth)

lemma clock_hasDeriv (t : ℝ) : HasDerivAt clock (pulse t) t :=
  (clock_smooth.differentiable (by simp) t).hasDerivAt

lemma pulse_zero_left (t : ℝ) (ht : t ≤ 0) : pulse t = 0 := by
  have heq : clock =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds (by linarith : t < (1 : ℝ) / 4)] with u hu
    exact clock_zero u hu.le
  simpa [pulse] using heq.deriv_eq

lemma pulse_zero_right (t : ℝ) (ht : 1 ≤ t) : pulse t = 0 := by
  have heq : clock =ᶠ[𝓝 t] (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds (by linarith : (3 : ℝ) / 4 < t)] with u hu
    exact clock_one u hu.le
  simpa [pulse] using heq.deriv_eq

end Profiles

namespace TimeGlue

noncomputable def glue {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → ℝ) (W : ℕ → A → E) (t : ℝ) (x : A) : E :=
  ∑' k : ℕ, g (t - k) • W k x

lemma eq_sum {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → ℝ) (hg : ∀ t, t ≤ 0 → g t = 0) (W : ℕ → A → E)
    (t : ℝ) (x : A) (a : ℕ) (ht : t ≤ a) :
    glue g W t x = ∑ k ∈ Finset.range a, g (t - k) • W k x := by
  apply tsum_eq_sum
  intro k hk
  have hk' : a ≤ k := by simpa using hk
  have hka : (a : ℝ) ≤ k := by exact_mod_cast hk'
  rw [hg _ (by linarith), zero_smul]

lemma locally_eq_sum {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace A] (g : ℝ → ℝ) (hg : ∀ t, t ≤ 0 → g t = 0) (W : ℕ → A → E)
    (z : ℝ × A) : ∃ a : ℕ,
      Function.uncurry (glue g W) =ᶠ[𝓝 z]
        (fun z : ℝ × A => ∑ k ∈ Finset.range a, g (z.1 - k) • W k z.2) := by
  obtain ⟨a, ha⟩ := exists_nat_gt z.1
  refine ⟨a, ?_⟩
  have hn : ∀ᶠ z' : ℝ × A in 𝓝 z, z'.1 < (a : ℝ) :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds ha
  filter_upwards [hn] with z' hz'
  exact eq_sum g hg W z'.1 z'.2 a hz'.le

lemma smooth {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → ℝ) (hg : ∀ t, t ≤ 0 → g t = 0) (hs : ContDiff ℝ ∞ g)
    (W : ℕ → A → E) (hW : ∀ k, ContDiff ℝ ∞ (W k)) :
    ContDiff ℝ ∞ (Function.uncurry (glue g W)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  obtain ⟨a, ha⟩ := locally_eq_sum g hg W z
  have hf : ContDiff ℝ ∞
      (fun z : ℝ × A => ∑ k ∈ Finset.range a, g (z.1 - k) • W k z.2) := by
    apply ContDiff.sum
    intro k _
    exact (hs.comp (contDiff_fst.sub contDiff_const)).smul ((hW k).comp contDiff_snd)
  exact hf.contDiffAt.congr_of_eventuallyEq ha

lemma hasDerivAt {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g g' : ℝ → ℝ) (hg : ∀ t, t ≤ 0 → g t = 0) (hg' : ∀ t, t ≤ 0 → g' t = 0)
    (hd : ∀ t, HasDerivAt g (g' t) t) (W : ℕ → A → E) (t : ℝ) (x : A) :
    HasDerivAt (fun u => glue g W u x) (glue g' W t x) t := by
  obtain ⟨a, ha⟩ := exists_nat_gt t
  rw [eq_sum g' hg' W t x a ha.le]
  have hf : HasDerivAt (fun u => ∑ k ∈ Finset.range a, g (u - k) • W k x)
      (∑ k ∈ Finset.range a, g' (t - k) • W k x) t := by
    apply HasDerivAt.fun_sum
    intro k _
    have hk := ((hd (t - k)).comp t ((hasDerivAt_id t).sub_const (k : ℝ))).smul_const (W k x)
    simpa using hk
  apply hf.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ha] with u hu
  exact eq_sum g hg W u x a hu.le

lemma pulse_slot {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ℕ → A → E) (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (k : ℝ) (k + 1)) (x : A) :
    glue Profiles.pulse W t x = Profiles.pulse (t - k) • W k x := by
  apply tsum_eq_single k
  intro j hj
  rcases lt_or_gt_of_ne hj with hj | hj
  · have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    rw [Profiles.pulse_zero_right _ (by linarith [ht.1]), zero_smul]
  · have hj' : (k : ℝ) + 1 ≤ j := by exact_mod_cast hj
    rw [Profiles.pulse_zero_left _ (by linarith [ht.2]), zero_smul]

lemma clock_slot {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ℕ → A → E) (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (k : ℝ) (k + 1)) (x : A) :
    glue Profiles.clock W t x = (∑ j ∈ Finset.range k, W j x) +
      Profiles.clock (t - k) • W k x := by
  rw [eq_sum Profiles.clock (fun u hu => Profiles.clock_zero u (by linarith)) W t x
    (k + 1) (by simpa using ht.2), Finset.sum_range_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast (Finset.mem_range.1 hj)
  rw [Profiles.clock_one _ (by linarith [ht.1]), one_smul]

end TimeGlue
end AlternatingNS

end OAI
