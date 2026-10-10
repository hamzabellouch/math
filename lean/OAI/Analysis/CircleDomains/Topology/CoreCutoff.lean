import OAI.Analysis.CircleDomains.Sobolev.SmallEnergyCore
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace OAI

/-!
# The actual cutoff used in grid modification

A compact retained core in the open physical domain admits a globally
smooth cutoff, zero near the core and one off a larger compact subset of
the domain. Its gradient is square-integrable without an extra premise.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Manifold

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem continuous_planarGradient
    {f : (ℝ × ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) : Continuous (planarGradient f) := by
  have hd : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := ∞) (by simp)).continuous
  exact (hd.clm_apply continuous_const).prodMk (hd.clm_apply continuous_const)

theorem hasCompactSupport_planarGradient
    {f : (ℝ × ℝ) → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (planarGradient f) := by
  apply hf.mono'
  intro z hz
  by_contra hzf
  have hd : fderiv ℝ f z = 0 := fderiv_of_notMem_tsupport ℝ hzf
  exact hz (by simp [planarGradient, hd])

theorem planarGradient_const_sub (f : (ℝ × ℝ) → ℝ) (c : ℝ) :
    planarGradient (fun z => c - f z) = fun z => -planarGradient f z := by
  ext z <;> simp [planarGradient, fderiv_const_sub]

/-- The cutoff and its L² differential are constructed, rather than
supplied to the subsequent random-grid argument. -/
theorem exists_core_cutoff
    {G K : Set (ℝ × ℝ)} (hG : IsOpen G) (hK : IsCompact K) (hKG : K ⊆ G) :
    ∃ (χ : (ℝ × ℝ) → ℝ) (L : Set (ℝ × ℝ)),
      ContDiff ℝ ∞ χ ∧ IsCompact L ∧ L ⊆ G ∧
      (∀ z, χ z ∈ Icc 0 1) ∧ (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧
      (∀ z ∉ L, χ z = 1) ∧ MemLp (planarGradient χ) 2 volume := by
  obtain ⟨V, hV, hKV, hVG, hVc⟩ := exists_open_between_and_isCompact_closure hK hG hKG
  obtain ⟨ψ, hzero, hone, hrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, ℝ × ℝ)) hV.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKV) (n := (⊤ : ℕ∞))
  have hψ : ContDiff ℝ ∞ (ψ : (ℝ × ℝ) → ℝ) := contMDiff_iff_contDiff.mp ψ.contMDiff
  have hsupport : support (ψ : (ℝ × ℝ) → ℝ) ⊆ V := by
    intro z hz
    by_contra hzV
    exact hz (hzero.self_of_nhdsSet z hzV)
  have hψc : HasCompactSupport (ψ : (ℝ × ℝ) → ℝ) :=
    hVc.of_isClosed_subset isClosed_closure (closure_mono hsupport)
  have hψ2 : MemLp (planarGradient (ψ : (ℝ × ℝ) → ℝ)) 2 volume :=
    (continuous_planarGradient hψ).memLp_of_hasCompactSupport (hasCompactSupport_planarGradient hψc)
  refine ⟨fun z => 1 - ψ z, closure V, contDiff_const.sub hψ, hVc, hVG, ?_, ?_, ?_, ?_⟩
  · intro z
    have hz := hrange z
    constructor <;> linarith [hz.1, hz.2]
  · filter_upwards [hone] with z hz
    simp only [hz, sub_self]
  · intro z hz
    change 1 - ψ z = 1
    rw [hzero.self_of_nhdsSet z (fun hv => hz (subset_closure hv)), sub_zero]
  · rw [planarGradient_const_sub]
    exact hψ2.neg

end CircleDomainRigidity.FiniteTransfer

end

end OAI
