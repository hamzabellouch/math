import OAI.MeasureTheory.Falconer.Angular.AngularBinKernel
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Int.Interval

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set Filter
open scoped ContDiff Topology

noncomputable def angularBinSelection (p : ℤ → Prop) (t : ℝ) : ℝ := by
  classical
  exact ∑' k : ℤ, if p k then angularBinKernel (t-k) else 0

theorem angularBinSelection_two_terms (p : ℤ → Prop) (t : ℝ) :
    angularBinSelection p t =
      (if p ⌊t⌋ then angularBinKernel (t-(⌊t⌋ : ℤ)) else 0) +
      (if p (⌊t⌋+1) then angularBinKernel (t-(⌊t⌋+1 : ℤ)) else 0) := by
  classical
  unfold angularBinSelection
  rw [tsum_eq_sum (s := {⌊t⌋, ⌊t⌋+1})]
  · simp [show ⌊t⌋ ≠ ⌊t⌋+1 by omega]
  · intro k hk
    have hz := angularBinKernel_translate_zero t k (by simpa using hk)
    simp [hz]

theorem angularBinSelection_bounds (p : ℤ → Prop) (t : ℝ) :
    0 ≤ angularBinSelection p t ∧ angularBinSelection p t ≤ 1 := by
  classical
  rw [angularBinSelection_two_terms]
  have h0 := angularBinKernel_nonneg (t-(⌊t⌋ : ℤ))
  have h1 := angularBinKernel_nonneg (t-(⌊t⌋+1 : ℤ))
  have he := angularBinKernel_floor_partition t
  split_ifs <;> constructor <;> linarith

theorem angularBinSelection_local (p : ℤ → Prop) (t : ℝ) :
    angularBinSelection p =ᶠ[𝓝 t] (fun u =>
      ∑ k ∈ Finset.Icc (⌊t⌋-2) (⌊t⌋+3), if p k then angularBinKernel (u-k) else 0) := by
  classical
  filter_upwards [Ioo_mem_nhds (show t-1 < t by linarith) (show t < t+1 by linarith)] with u hu
  unfold angularBinSelection
  apply tsum_eq_sum
  intro k hk
  have hz : angularBinKernel (u-k) = 0 := by
    have hk : k < ⌊t⌋-2 ∨ ⌊t⌋+3 < k := by simpa only [Finset.mem_Icc, not_and_or, not_le] using hk
    rcases hk with hk | hk
    · apply angularBinKernel_zero_right
      have hc : (k : ℝ) < (⌊t⌋ : ℝ)-2 := by exact_mod_cast hk
      linarith [Int.floor_le t, hu.1]
    · apply angularBinKernel_zero_left
      have hc : (⌊t⌋ : ℝ)+3 < (k : ℝ) := by exact_mod_cast hk
      linarith [Int.lt_floor_add_one t, hu.2]
  simp [hz]

theorem angularBinSelection_contDiff (p : ℤ → Prop) : ContDiff ℝ ∞ (angularBinSelection p) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro t
  apply ContDiffAt.congr_of_eventuallyEq _ (angularBinSelection_local p t)
  apply ContDiff.contDiffAt
  apply ContDiff.sum
  intro k _
  by_cases hk : p k
  · simp only [hk, ↓reduceIte]
    exact angularBinKernel_contDiff.comp (contDiff_id.sub contDiff_const)
  · simp only [hk, ↓reduceIte]
    exact contDiff_const

theorem angularBinKernel_derivative_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖iteratedDeriv j angularBinKernel t‖ ≤ C := by
  have hc : HasCompactSupport (iteratedDeriv j angularBinKernel) :=
    angularBinKernel_compact.of_isClosed_subset isClosed_closure (iteratedDeriv_tsupport j)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous
    (angularBinKernel_contDiff.continuous_iteratedDeriv j (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

theorem angularBinSelection_derivative_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℤ → Prop) (t : ℝ),
      ‖iteratedDeriv j (angularBinSelection p) t‖ ≤ C := by
  classical
  obtain ⟨C, hC0, hC⟩ := angularBinKernel_derivative_bound j
  refine ⟨6*C, by positivity, ?_⟩
  intro p t
  rw [EventuallyEq.iteratedDeriv_eq j (angularBinSelection_local p t)]
  have hf (k : ℤ) : ContDiff ℝ ∞ (fun u => if p k then angularBinKernel (u-k) else 0) := by
    by_cases hk : p k
    · simp only [hk, ↓reduceIte]
      exact angularBinKernel_contDiff.comp (contDiff_id.sub contDiff_const)
    · simp only [hk, ↓reduceIte]
      exact contDiff_const
  rw [iteratedDeriv_fun_sum (fun k _ => ((hf k).of_le
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt)]
  calc
    _ ≤ ∑ k ∈ Finset.Icc (⌊t⌋-2) (⌊t⌋+3), C := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : p k
      · simp only [hk, ↓reduceIte, iteratedDeriv_comp_sub_const]
        exact hC _
      · simpa only [hk, ↓reduceIte, iteratedDeriv_fun_const_zero, norm_zero] using hC0
    _ = _ := by
      have hcard : (Finset.Icc (⌊t⌋-2) (⌊t⌋+3)).card = 6 := by
        rw [Int.card_Icc]
        omega
      simp [hcard]

end PlanarFalconer

end OAI
