import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ExpandingArrayGate
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivativesNormSumLeSparse

namespace OAI

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses UniformDerivatives
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ)

theorem gate_jet_zero_outside (hν : 0 < ν) (n d : ℕ)
    (c : Active hb table (capacity b m n)) (q : ℝ × Coord 2) (i : Fin 2)
    (hq : ∃ j, 3 * radius ν (K₀ N b m) (D b) n <
      |q.2 j - path hb table terminal ν m n c q.1 j|) :
    iteratedFDeriv ℝ d (fun q => gate hb table terminal ν m n c q i) q = 0 := by
  obtain ⟨j, hj⟩ := hq
  have hcont : Continuous (fun p : ℝ × Coord 2 =>
      |p.2 j - path hb table terminal ν m n c p.1 j|) :=
    ((continuous_apply j).comp continuous_snd |>.sub
      ((continuous_apply j).comp ((contDiff_path hb table terminal ν m n c).continuous.comp
        continuous_fst))).abs
  have heq : (fun p => gate hb table terminal ν m n c p i) =ᶠ[𝓝 q] 0 := by
    filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds hj] with p hp
    have h := TranslationGates.field_zero_outside
      (lt_of_lt_of_le zero_lt_one (radius_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) n))
      (path hb table terminal ν m n c p.1) (deriv (path hb table terminal ν m n c) p.1) p.2 ⟨j, hp.le⟩
    exact congrFun h i
  simpa using (heq.iteratedFDeriv ℝ d).eq_of_nhds

theorem gate_jets_disjoint (hν : 0 < ν) (hm : 1 ≤ m)
    (hdir : IncomingDirection table) (hin : IncomingRule table) (n d : ℕ)
    (c e : Active hb table (capacity b m n)) (hce : c ≠ e) (q : ℝ × Coord 2) (i : Fin 2) :
    iteratedFDeriv ℝ d (fun q => gate hb table terminal ν m n c q i) q = 0 ∨
      iteratedFDeriv ℝ d (fun q => gate hb table terminal ν m n e q i) q = 0 := by
  obtain ⟨j, hj⟩ := paths_separated hb table terminal ν m hν hm hdir hin n c e hce q.1
  have hR : 0 < radius ν (K₀ N b m) (D b) n :=
    lt_of_lt_of_le zero_lt_one (radius_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) n)
  by_cases hc : 3 * radius ν (K₀ N b m) (D b) n <
      |q.2 j - path hb table terminal ν m n c q.1 j|
  · exact Or.inl (gate_jet_zero_outside hb table terminal ν m hν n d c q i ⟨j, hc⟩)
  · right
    apply gate_jet_zero_outside hb table terminal ν m hν n d e q i
    refine ⟨j, ?_⟩
    have htri : |path hb table terminal ν m n c q.1 j - path hb table terminal ν m n e q.1 j| ≤
        |q.2 j - path hb table terminal ν m n c q.1 j| +
          |q.2 j - path hb table terminal ν m n e q.1 j| := by
      simpa only [abs_sub_comm (path hb table terminal ν m n c q.1 j) (q.2 j)]
        using abs_sub_le (path hb table terminal ν m n c q.1 j) (q.2 j)
          (path hb table terminal ν m n e q.1 j)
    linarith

theorem stages_uniformly_bounded (hν : 0 < ν) (hm : 1 ≤ m)
    (hdir : IncomingDirection table) (hin : IncomingRule table) (i : Fin 2) :
    Bounded (fun n (q : ℝ × Coord 2) => stage hb table terminal ν m n q.1 q.2 i) := by
  intro d
  obtain ⟨C, hC, hc⟩ := gates_uniformly_bounded hb table terminal ν m hν hm i d
  refine ⟨C, hC, fun n q => ?_⟩
  have heq : (fun q : ℝ × Coord 2 => stage hb table terminal ν m n q.1 q.2 i) =
      ∑ c : Active hb table (capacity b m n), fun q => gate hb table terminal ν m n c q i := by
    ext q
    simp only [stage, gate, Finset.sum_apply]
  change ‖iteratedFDeriv ℝ d (fun q : ℝ × Coord 2 => stage hb table terminal ν m n q.1 q.2 i) q‖ ≤ C
  rw [heq, iteratedFDeriv_sum_apply]
  · apply norm_sum_le_sparse _ _ hC
    · intro c _
      exact hc ⟨n, c⟩ q
    · intro c _ e _ hce
      exact gate_jets_disjoint hb table terminal ν m hν hm hdir hin n d c e hce q i
  · intro c _
    exact (contDiff_infty.mp ((contDiff_apply ℝ ℝ i).comp
      (contDiff_gate hb table terminal ν m n c)) d).contDiffAt

theorem stage_jet_zero_before (hν : 0 < ν) (n d : ℕ) (q : ℝ × Coord 2) (i : Fin 2)
    (hq : q.1 ≤ startTime ν (K₀ N b m) (D b) n) :
    iteratedFDeriv ℝ d (fun q => stage hb table terminal ν m n q.1 q.2 i) q = 0 := by
  exact jet_zero_before ((contDiff_apply ℝ ℝ i).comp (contDiff_stage hb table terminal ν m n))
    (fun t ht X => congrFun (stage_zero_before hb table terminal ν m hν n ht X) i) d hq q.2

theorem stage_jet_zero_after (hν : 0 < ν) (n d : ℕ) (q : ℝ × Coord 2) (i : Fin 2)
    (hq : startTime ν (K₀ N b m) (D b) (n + 1) ≤ q.1) :
    iteratedFDeriv ℝ d (fun q => stage hb table terminal ν m n q.1 q.2 i) q = 0 := by
  exact jet_zero_after ((contDiff_apply ℝ ℝ i).comp (contDiff_stage hb table terminal ν m n))
    (fun t ht X => congrFun (stage_zero_after hb table terminal ν m hν n ht X) i) d hq q.2

theorem stage_jets_disjoint (hν : 0 < ν) (n k d : ℕ) (hnk : n ≠ k) (q : ℝ × Coord 2) (i : Fin 2) :
    iteratedFDeriv ℝ d (fun q => stage hb table terminal ν m n q.1 q.2 i) q = 0 ∨
      iteratedFDeriv ℝ d (fun q => stage hb table terminal ν m k q.1 q.2 i) q = 0 := by
  wlog hnk' : n < k generalizing n k
  · exact (this k n hnk.symm (by omega)).symm
  by_cases hq : q.1 ≤ startTime ν (K₀ N b m) (D b) k
  · exact Or.inr (stage_jet_zero_before hb table terminal ν m hν k d q i hq)
  · left
    apply stage_jet_zero_after hb table terminal ν m hν n d q i
    have hm := (startTime_strictMono hν (K₀_nonneg N b m) (D_ge_one hb)).monotone (show n + 1 ≤ k by omega)
    linarith

theorem field_uniformly_bounded (hν : 0 < ν) (hm : 1 ≤ m)
    (hdir : IncomingDirection table) (hin : IncomingRule table) (i : Fin 2) :
    Bounded (fun _ : Unit => fun q : ℝ × Coord 2 => field hb table terminal ν m q.1 q.2 i) := by
  intro d
  obtain ⟨C, hC, hc⟩ := stages_uniformly_bounded hb table terminal ν m hν hm hdir hin i d
  refine ⟨C, hC, fun _ q => ?_⟩
  obtain ⟨Q, hQ⟩ := exists_nat_gt q.1
  have heq : (fun q : ℝ × Coord 2 => field hb table terminal ν m q.1 q.2 i) =ᶠ[𝓝 q]
      ∑ n ∈ Finset.range Q, fun q => stage hb table terminal ν m n q.1 q.2 i := by
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hQ] with p hp
    simpa only [Finset.sum_apply] using congrFun (field_eq_finite hb table terminal ν m hν hp p.2) i
  rw [(heq.iteratedFDeriv ℝ d).eq_of_nhds, iteratedFDeriv_sum_apply]
  · apply norm_sum_le_sparse _ _ hC
    · intro n _
      exact hc n q
    · intro n _ k _ hnk
      exact stage_jets_disjoint hb table terminal ν m hν n k d hnk q i
  · intro n _
    exact (contDiff_infty.mp ((contDiff_apply ℝ ℝ i).comp
      (contDiff_stage hb table terminal ν m n)) d).contDiffAt

end VelocityDetection.ExpandingArray
end

end OAI
