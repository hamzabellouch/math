import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

noncomputable section
namespace SequentialApproximateUnit
open Filter Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [TopologicalSpace.SeparableSpace A]

theorem exists_sequence : ∃ u : ℕ → A, (∀ n, 0≤u n) ∧ (∀ n, ‖u n‖≤1) ∧
    ∀ a : A, Tendsto (fun n => u n*a) atTop (𝓝 a) ∧ Tendsto (fun n => a*u n) atTop (𝓝 a) := by
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  let e : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have he (n : ℕ) : 0<e n := by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let l := CStarAlgebra.approximateUnit A
  have hl := CStarAlgebra.increasingApproximateUnit A
  have hf (n : ℕ) : ∃ u : A, 0≤u ∧ ‖u‖≤1 ∧ ∀ m≤n, ‖u*a m-a m‖<e n := by
    have h (m : ℕ) : ∀ᶠ u in l, ‖u*a m-a m‖<e n := by
      simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp (hl.tendsto_mul_right (a m))) (e n) (he n)
    have hh := (eventually_all_finset (Finset.range (n+1))).mpr (fun m _ => h m)
    obtain ⟨u,hup,hun,hu⟩ := (hl.eventually_nonneg.and (hl.eventually_norm.and hh)).exists
    exact ⟨u,hup,hun,fun m hm => hu m (Finset.mem_range.mpr (by omega))⟩
  choose u hup hun hu using hf
  have hlu (b : A) : Tendsto (fun n => u n*b) atTop (𝓝 b) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨m,hm⟩ := ha.exists_dist_lt b (show 0<ε/4 by positivity)
    have hE := (tendsto_order.mp he0).2 (ε/2) (half_pos hε)
    filter_upwards [hE,eventually_ge_atTop m] with n hn hmn
    rw [dist_eq_norm]
    have hnorm : ‖b-a m‖<ε/4 := by simpa only [dist_eq_norm] using hm
    calc
      ‖u n*b-b‖ = ‖u n*(b-a m)+(u n*a m-a m)+(a m-b)‖ := by congr 1; noncomm_ring
      _ ≤ ‖u n*(b-a m)‖+‖u n*a m-a m‖+‖a m-b‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖b-a m‖+‖u n*a m-a m‖+‖a m-b‖ := by
        gcongr
        exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (b-a m),hun n])
      _ < ε := by rw [norm_sub_rev (a m) b]; linarith [hu n m hmn]
  refine ⟨u,hup,hun,fun b => ⟨hlu b,?_⟩⟩
  have h := (hlu (star b)).star
  simpa only [star_mul,star_star,(hup _).isSelfAdjoint.star_eq] using h

end SequentialApproximateUnit

end
end

end OAI
