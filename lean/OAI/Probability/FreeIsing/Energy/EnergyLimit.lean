import Mathlib

namespace OAI

noncomputable section

open Filter Finset
open scoped Topology

namespace Problem367

theorem hasSum_of_uniform_energy_tails
    {ι : Type*} {a : ℕ → ι → ℝ} {b : ι → ℝ} {energy : ℕ → ℝ} {total : ℝ}
    (ha : ∀ n i, 0 ≤ a n i)
    (hpartial : ∀ n (s : Finset ι), ∑ i ∈ s, a n i ≤ energy n)
    (hcoordinate : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (b i)))
    (henergy : Tendsto energy atTop (𝓝 total))
    (htail : ∀ ε > 0, ∃ s : Finset ι,
      ∀ n, energy n - ∑ i ∈ s, a n i ≤ ε) :
    HasSum b total := by
  classical
  have hb : ∀ i, 0 ≤ b i := fun i =>
    ge_of_tendsto (hcoordinate i) (Eventually.of_forall fun n => ha n i)
  have hsumlim (s : Finset ι) :
      Tendsto (fun n => ∑ i ∈ s, a n i) atTop (𝓝 (∑ i ∈ s, b i)) :=
    tendsto_finsetSum s (fun i _ => hcoordinate i)
  have hbound (s : Finset ι) : ∑ i ∈ s, b i ≤ total :=
    le_of_tendsto_of_tendsto (hsumlim s) henergy
      (Eventually.of_forall fun n => hpartial n s)
  have hsummable : Summable b := summable_of_sum_le hb hbound
  have hle : ∑' i, b i ≤ total := hsummable.tsum_le_of_sum_le hbound
  have hge : total ≤ ∑' i, b i := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨s, hs⟩ := htail ε hε
    have hrem : total - ∑ i ∈ s, b i ≤ ε :=
      le_of_tendsto (henergy.sub (hsumlim s)) (Eventually.of_forall hs)
    have hfinite : ∑ i ∈ s, b i ≤ ∑' i, b i :=
      hsummable.sum_le_tsum s (fun i _ => hb i)
    linarith
  simpa only [le_antisymm hle hge] using hsummable.hasSum

theorem uniform_energy_tails_of_two_stage_bound
    {ι : Type*} {a : ℕ → ι → ℝ} {energy : ℕ → ℝ}
    {sets : ℕ → Finset ι} {early : ℕ → ℝ} {late : ℕ → ℕ → ℝ}
    (hearly : Tendsto early atTop (𝓝 0))
    (hlate : ∀ k, Tendsto (late k) atTop (𝓝 0))
    (hbound : ∀ n k L,
      energy n - ∑ i ∈ sets L, a n i ≤ early k + late k L) :
    ∀ ε > 0, ∃ s : Finset ι, ∀ n, energy n - ∑ i ∈ s, a n i ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hearly).2 (ε / 2) hhalf).exists
  obtain ⟨L, hL⟩ := ((tendsto_order.1 (hlate k)).2 (ε / 2) hhalf).exists
  refine ⟨sets L, fun n => ?_⟩
  have := hbound n k L
  linarith

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_sq_residual_of_testing (x y : H)
    (htest : inner ℝ x y = ‖y‖ ^ 2) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
  rw [norm_sub_sq_real, htest]
  ring

theorem tendsto_of_testing_and_energy
    {α : Type*} {l : Filter α} {s : α → H} {x : H}
    (htest : ∀ n, inner ℝ x (s n) = ‖s n‖ ^ 2)
    (henergy : Tendsto (fun n => ‖s n‖ ^ 2) l (𝓝 (‖x‖ ^ 2))) :
    Tendsto s l (𝓝 x) := by
  have hres (n : α) : ‖s n - x‖ ^ 2 = ‖x‖ ^ 2 - ‖s n‖ ^ 2 := by
    rw [norm_sub_rev]
    exact norm_sq_residual_of_testing x (s n) (htest n)
  have hsq : Tendsto (fun n => ‖s n - x‖ ^ 2) l (𝓝 0) := by
    simpa only [hres, sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : α => ‖x‖ ^ 2) l (𝓝 (‖x‖ ^ 2))).sub henergy
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt

theorem norm_sq_sum_of_pairwise_orthogonal
    {ι : Type*} (u : ι → H)
    (hortho : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0)
    (s : Finset ι) : ‖∑ i ∈ s, u i‖ ^ 2 = ∑ i ∈ s, ‖u i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum, Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq (u i)
  · intro j hj hji
    exact hortho i j hji.symm
  · intro hnot
    exact (hnot hi).elim

theorem hasSum_of_orthogonal_testing_and_energy
    {ι : Type*} {u : ι → H} {x : H}
    (hortho : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0)
    (htest : ∀ i, inner ℝ x (u i) = ‖u i‖ ^ 2)
    (henergy : HasSum (fun i => ‖u i‖ ^ 2) (‖x‖ ^ 2)) :
    HasSum u x := by
  classical
  apply tendsto_of_testing_and_energy
  · intro s
    rw [inner_sum, norm_sq_sum_of_pairwise_orthogonal u hortho s]
    exact Finset.sum_congr rfl fun i _ => htest i
  · simpa only [HasSum, norm_sq_sum_of_pairwise_orthogonal u hortho] using henergy

theorem hasSum_of_uniform_energy_tails_and_testing
    {ι : Type*} {a : ℕ → ι → ℝ} {energy : ℕ → ℝ} {u : ι → H} {x : H}
    (ha : ∀ n i, 0 ≤ a n i)
    (hpartial : ∀ n (s : Finset ι), ∑ i ∈ s, a n i ≤ energy n)
    (hcoordinate : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (‖u i‖ ^ 2)))
    (henergy : Tendsto energy atTop (𝓝 (‖x‖ ^ 2)))
    (htail : ∀ ε > 0, ∃ s : Finset ι,
      ∀ n, energy n - ∑ i ∈ s, a n i ≤ ε)
    (hortho : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0)
    (htest : ∀ i, inner ℝ x (u i) = ‖u i‖ ^ 2) :
    HasSum u x :=
  hasSum_of_orthogonal_testing_and_energy hortho htest
    (hasSum_of_uniform_energy_tails ha hpartial hcoordinate henergy htail)

end Hilbert

end Problem367

end

end OAI
