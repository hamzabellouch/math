import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences

namespace OAI

open Filter Finset
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

theorem tendsto_tsum_abs_sub_of_probability_mass
    {ι α : Type*} {l : Filter α} {p : α → ι → ℝ} {q : ι → ℝ}
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i))) :
    Tendsto (fun n => ∑' i, |p n i - q i|) l (𝓝 0) := by
  have hmin_summable (n : α) : Summable (fun i => min (p n i) (q i)) := by
    apply hq_sum.summable.of_nonneg_of_le
    · intro i
      exact le_min (hp_nonneg n i) (hq_nonneg i)
    · intro i
      exact min_le_right _ _
  have hmin : Tendsto (fun n => ∑' i, min (p n i) (q i)) l (𝓝 1) := by
    rw [← hq_sum.tsum_eq]
    apply tendsto_tsum_of_dominated_convergence hq_sum.summable
    · intro i
      simpa using (hpoint i).min (tendsto_const_nhds (x := q i))
    · exact Filter.Eventually.of_forall fun n i => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp_nonneg n i) (hq_nonneg i))]
        exact min_le_right _ _
  have hid (n : α) : (∑' i, |p n i - q i|) = 2 - 2 * ∑' i, min (p n i) (q i) := by
    calc
      (∑' i, |p n i - q i|) = ∑' i, (p n i + q i - 2 * min (p n i) (q i)) := by
        apply tsum_congr
        intro i
        rcases le_total (p n i) (q i) with h | h
        · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
          ring
        · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
          ring
      _ = 2 - 2 * ∑' i, min (p n i) (q i) := by
        rw [((hp_sum n).summable.add hq_sum.summable).tsum_sub
          ((hmin_summable n).mul_left 2),
          (hp_sum n).summable.tsum_add hq_sum.summable, tsum_mul_left,
          (hp_sum n).tsum_eq, hq_sum.tsum_eq]
        norm_num
  simp_rw [hid]
  have hlim := (tendsto_const_nhds (x := (2 : ℝ))).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hmin)
  simpa using hlim

theorem tendsto_totalVariation_of_probability_mass
    {ι α : Type*} {l : Filter α} {p : α → ι → ℝ} {q : ι → ℝ}
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i))) :
    Tendsto (fun n => (1 / 2 : ℝ) * ∑' i, |p n i - q i|) l (𝓝 0) := by
  simpa using tendsto_const_nhds.mul
    (tendsto_tsum_abs_sub_of_probability_mass hp_nonneg hq_nonneg hp_sum hq_sum hpoint)

theorem profile_tail_le_of_moment
    {ι : Type*} (w : ι → ℕ) (p : ι → ℝ) (M : ℝ) (B : ℕ)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p)
    (hws : Summable (fun i => (w i : ℝ) * p i))
    (hM : (∑' i, (w i : ℝ) * p i) ≤ M) :
    (∑' i : {i // B < w i}, p i) ≤ M / (B + 1 : ℝ) := by
  have hB : (0 : ℝ) < B + 1 := by positivity
  apply (le_div_iff₀ hB).2
  rw [← tsum_mul_right]
  calc
    (∑' i : {i // B < w i}, p i * (B + 1 : ℝ)) ≤
        ∑' i : {i // B < w i}, (w i : ℝ) * p i := by
      apply Summable.tsum_le_tsum
      · intro i
        have hi : (B + 1 : ℝ) ≤ (w i : ℝ) := by exact_mod_cast i.property
        nlinarith [hp i]
      · exact (hs.subtype _).mul_right _
      · exact hws.subtype _
    _ ≤ ∑' i, (w i : ℝ) * p i := by
      exact Summable.tsum_subtype_le _ _ (fun i => mul_nonneg (Nat.cast_nonneg _) (hp i)) hws
    _ ≤ M := hM

theorem hasSum_one_of_tendsto_of_tight
    {ι α : Type*} {l : Filter α} [l.NeBot]
    {p : α → ι → ℝ} {q : ι → ℝ}
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hp_sum : ∀ n, HasSum (p n) 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i)))
    (htight : ∀ ε : ℝ, 0 < ε → ∃ s : Finset ι, ∀ n, 1 - ε ≤ ∑ i ∈ s, p n i) :
    HasSum q 1 := by
  have hq_nonneg (i : ι) : 0 ≤ q i :=
    ge_of_tendsto (hpoint i) (Filter.Eventually.of_forall fun n => hp_nonneg n i)
  have hfinite (s : Finset ι) : ∑ i ∈ s, q i ≤ 1 := by
    apply le_of_tendsto (tendsto_finsetSum s fun i _ => hpoint i)
    exact Filter.Eventually.of_forall fun n => by
      simpa only [(hp_sum n).tsum_eq] using
        (hp_sum n).summable.sum_le_tsum s (fun i _ => hp_nonneg n i)
  have hq_summable : Summable q := summable_of_sum_le hq_nonneg hfinite
  have hq_le : (∑' i, q i) ≤ 1 := hq_summable.tsum_le_of_sum_le hfinite
  have hq_ge : 1 ≤ ∑' i, q i := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨s, hs⟩ := htight ε hε
    have hlim : 1 - ε ≤ ∑ i ∈ s, q i :=
      ge_of_tendsto (tendsto_finsetSum s fun i _ => hpoint i)
        (Filter.Eventually.of_forall hs)
    have hsum := hq_summable.sum_le_tsum s (fun i _ => hq_nonneg i)
    linarith
  simpa only [le_antisymm hq_le hq_ge] using hq_summable.hasSum

theorem profile_tight_of_moment
    {ι α : Type*} (w : ι → ℕ)
    (hfinite : ∀ B, Set.Finite {i | w i ≤ B})
    {p : α → ι → ℝ} {M : ℝ}
    (hp : ∀ n i, 0 ≤ p n i) (hs : ∀ n, HasSum (p n) 1)
    (hws : ∀ n, Summable (fun i => (w i : ℝ) * p n i))
    (hM : ∀ n, (∑' i, (w i : ℝ) * p n i) ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ s : Finset ι, ∀ n, 1 - ε ≤ ∑ i ∈ s, p n i := by
  classical
  intro ε hε
  obtain ⟨B, hB⟩ := exists_nat_gt (M / ε)
  let s := (hfinite B).toFinset
  have hset : (↑s : Set ι)ᶜ = {i | B < w i} := by
    ext i
    simp [s, not_le]
  have hratio : M / (B + 1 : ℝ) ≤ ε := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < B + 1)).2
    have haux := (div_lt_iff₀ hε).1 hB
    nlinarith
  refine ⟨s, fun n => ?_⟩
  have htail := profile_tail_le_of_moment w (p n) M B (hp n)
    (hs n).summable (hws n) (hM n)
  have hsum := (hs n).summable.sum_add_tsum_compl (s := s)
  rw [hset, (hs n).tsum_eq] at hsum
  change (∑ i ∈ s, p n i) + (∑' i : {i // B < w i}, p n i) = 1 at hsum
  linarith

theorem profile_moment_le_of_tendsto
    {ι α : Type*} {l : Filter α} [l.NeBot] (w : ι → ℕ)
    {p : α → ι → ℝ} {q : ι → ℝ} {M : ℝ}
    (hp : ∀ n i, 0 ≤ p n i)
    (hws : ∀ n, Summable (fun i => (w i : ℝ) * p n i))
    (hM : ∀ n, (∑' i, (w i : ℝ) * p n i) ≤ M)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i))) :
    Summable (fun i => (w i : ℝ) * q i) ∧
      (∑' i, (w i : ℝ) * q i) ≤ M := by
  have hq (i : ι) : 0 ≤ q i :=
    ge_of_tendsto (hpoint i) (Filter.Eventually.of_forall fun n => hp n i)
  have hpartial (s : Finset ι) : ∑ i ∈ s, (w i : ℝ) * q i ≤ M := by
    apply le_of_tendsto (tendsto_finsetSum s fun i _ =>
      (tendsto_const_nhds (x := (w i : ℝ))).mul (hpoint i))
    exact Filter.Eventually.of_forall fun n =>
      ((hws n).sum_le_tsum s (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hp n i))).trans (hM n)
  have hnonneg : ∀ i, 0 ≤ (w i : ℝ) * q i :=
    fun i => mul_nonneg (Nat.cast_nonneg _) (hq i)
  exact ⟨summable_of_sum_le hnonneg hpartial,
    Real.tsum_le_of_sum_le hnonneg hpartial⟩

theorem tendsto_selected_mass_of_probability_mass
    {ι α : Type*} {l : Filter α} {p : α → ι → ℝ} {q : ι → ℝ}
    (S : Set ι)
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i))) :
    Tendsto (fun n => ∑' i : S, p n i) l (𝓝 (∑' i : S, q i)) := by
  have hbound (n : α) :
      ‖(∑' i : S, p n i) - ∑' i : S, q i‖ ≤ ∑' i, |p n i - q i| := by
    have hsub := (hp_sum n).summable.sub hq_sum.summable
    have hdiff := ((hp_sum n).summable.subtype S).tsum_sub (hq_sum.summable.subtype S)
    simp only [Function.comp_apply] at hdiff
    calc
      ‖(∑' i : S, p n i) - ∑' i : S, q i‖ =
          ‖∑' i : Subtype S, (p n i.val - q i.val)‖ := congrArg norm hdiff.symm
      _ ≤ ∑' i : Subtype S, ‖p n i.val - q i.val‖ :=
        norm_tsum_le_tsum_norm ((hsub.subtype S).norm)
      _ ≤ ∑' i, |p n i - q i| := by
        convert! Summable.tsum_subtype_le (fun i => ‖p n i - q i‖) S
          (fun i => norm_nonneg _) hsub.norm using 1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) hbound
    (tendsto_tsum_abs_sub_of_probability_mass hp_nonneg hq_nonneg hp_sum hq_sum hpoint)

end Balanced

end OAI
