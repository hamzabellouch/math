import OAI.Probability.SLE.LoewnerCharts
import Mathlib.Topology.Order.ProjIcc

namespace OAI

/-! The finite trace is a locally connected compact continuum, supplying
 the boundary geometry needed for continuous inverse extensions. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology NNReal

namespace SLEExactGauge

lemma finiteTrace_locallyConnected {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (T : ℝ≥0) :
    LocallyConnectedSpace (γ '' Icc 0 T) := by
  have : LocallyConnectedSpace (Icc (0:ℝ) (T:ℝ)) :=
    (isQuotientMap_projIcc (a := (0:ℝ)) (b := (T:ℝ)) (h := T.coe_nonneg)).isCoinducing.locallyConnectedSpace
  let p : Icc (0:ℝ) (T:ℝ) → γ '' Icc 0 T := fun t =>
    ⟨γ t.1.toNNReal,⟨t.1.toNNReal,⟨by simp,(Real.toNNReal_le_iff_le_coe).mpr t.2.2⟩,rfl⟩⟩
  have hp : Continuous p := (hγ.comp (continuous_real_toNNReal.comp continuous_subtype_val)).subtype_mk _
  have hs : Surjective p := by
    rintro ⟨z,t,ht,rfl⟩
    refine ⟨⟨t,⟨t.coe_nonneg,by exact_mod_cast ht.2⟩⟩,?_⟩
    apply Subtype.ext
    simp [p]
  exact (hp.isClosedMap.isQuotientMap hp hs).isCoinducing.locallyConnectedSpace

lemma finiteTrace_isCompact {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (T : ℝ≥0) :
    IsCompact (γ '' Icc 0 T) := isCompact_Icc.image hγ

lemma finiteTrace_isConnected {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (T : ℝ≥0) :
    IsConnected (γ '' Icc 0 T) :=
  (isConnected_Icc (show (0:ℝ≥0)≤T from bot_le)).image γ hγ.continuousOn

lemma finiteTrace_small_connected_neighborhood {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (T : ℝ≥0) (z : γ '' Icc 0 T) (ε : ℝ) (hε : 0<ε) :
    ∃ V : Set (γ '' Icc 0 T), V ∈ 𝓝 z ∧ IsPreconnected V ∧
      ∀ w∈V, dist (w:ℂ) (z:ℂ)<ε := by
  have := finiteTrace_locallyConnected hγ T
  obtain ⟨V,hV,hconn,hsub⟩ := (locallyConnectedSpace_iff_connected_subsets.mp this)
    z (ball z ε) (ball_mem_nhds z hε)
  exact ⟨V,hV,hconn,fun w hw => mem_ball.mp (hsub hw)⟩

end SLEExactGauge

end

end OAI
