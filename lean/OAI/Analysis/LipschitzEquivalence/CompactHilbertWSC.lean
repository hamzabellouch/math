import OAI.Analysis.LipschitzEquivalence.WUCOperator

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local instance : NormedAddCommGroup (Space H) := inferInstance
local instance : NormedSpace ℝ (Space H) := inferInstance
local instance (K : Set H) : NormedAddCommGroup (supported K) := inferInstance
local instance (K : Set H) : NormedSpace ℝ (supported K) := inferInstance
local instance (K : Set H) : NormedAddCommGroup ((supported K) →L[ℝ] ℝ) := inferInstance
local instance (K : Set H) : NormedSpace ℝ ((supported K) →L[ℝ] ℝ) := inferInstance

theorem compact_supported_wsc (K : Set H) (hK : IsCompact K) (h0 : (0:H) ∈ K) :
    WeakSequences.WeakSequentiallyComplete (supported K) := by
  intro u hu
  by_contra hno
  let : CompleteSpace (supported K) := (supported_isClosed K).completeSpace_coe
  obtain ⟨φ,d,hd,hφ,hfar⟩ := WeakSequences.nonconvergent_biddual_gap hu hno
  obtain ⟨B,hB⟩ := hu.bounded
  let C := max B 1
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have huC (n : ℕ) : ‖u n‖ ≤ C := (hB n).trans (le_max_left _ _)
  let α := d/32
  let ρ := α/16
  have hα : 0 < α := div_pos hd (by norm_num)
  have hρ : 0 < ρ := div_pos hα (by norm_num)
  have hρα : ρ ≤ α/4 := by dsimp [ρ]; linarith
  have hαd : 32*α ≤ d := by dsimp [α]; linarith
  have hRich := triangularRows_rich h0 u φ hφ hd hC hρ hα hρα hαd huC hfar
  let Q := closure (convexHull ℝ K)
  have hQ : IsCompact Q := (hK.totallyBounded.convexHull.closure).isCompact_of_isClosed isClosed_closure
  have hQc : Convex ℝ Q := (convex_convexHull ℝ K).closure
  have hKQ : K ⊆ Q := (subset_convexHull ℝ K).trans subset_closure
  obtain ⟨T,a,hT,hdiag,hWUC⟩ := exists_wuc_duals h0 hQ hQc hKQ hC.le hα hRich
  let S : ℕ → supported K →L[ℝ] ℝ := fun i => (T i).comp (supported K).subtypeL
  have hS : ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ x : supported K,
      |∑ i ∈ Finset.range n, c i*S i x| ≤ 2*‖x‖ :=
    fun n c hc x => hWUC n c hc x.val x.property
  obtain ⟨N,hN⟩ := WeakSequences.uniform_small_of_wuc S hS hu (show 0<α/4 by positivity)
  obtain ⟨k,hk⟩ := (a N).close
  have hclose : |T N (u k)-T N (a N).a.vector| < 2*ρ := by
    rw [← map_sub,← Real.norm_eq_abs]
    exact ((T N).le_opNorm _).trans_lt (by nlinarith [hT N,norm_nonneg (T N),norm_nonneg ((u k : Space H)-(a N).a.vector)])
  have hsmall : |T N (u k)| < α/4 := hN N le_rfl k
  have hlarge := hdiag N
  have hl := (abs_lt.mp hclose).1
  have hs := (abs_lt.mp hsmall).2
  dsimp [ρ] at hl
  linarith

theorem hilbert_free_wsc : WeakSequences.WeakSequentiallyComplete (Space H) :=
  FreeSpace.wsc_of_compact_supported compact_supported_wsc

end LipschitzCounterexample.CompactWSC
end

end OAI
