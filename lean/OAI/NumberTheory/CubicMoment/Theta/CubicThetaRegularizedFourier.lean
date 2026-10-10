import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierPoleIsolation
import Mathlib.Analysis.Meromorphic.NormalForm

namespace OAI

/-! A single holomorphic representative of the pole-cleared arithmetic
Fourier coefficient on Re(s)>1, including its actual residue value. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

private lemma regularized_analytic {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U)
    (hg : ∀ s∈U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ f=ᶠ[𝓝[≠] s] g) :
    AnalyticOnNhd ℂ (toMeromorphicNFOn f U) U := by
  intro s hs
  have hn : 0 ≤ meromorphicOrderAt f s := (hf s hs).meromorphicOrderAt_nonneg_iff.mpr (hg s hs)
  have ha := (hf s hs).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp hn
  rw [analyticAt_congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hs)]
  exact ha

def cubicThetaRegularizedFrequency (h : Eisenstein) : ℂ → ℂ :=
  toMeromorphicNFOn (fun s => (s-4/3)*cubicThetaFrequencyContinuation h s) {s : ℂ | 1<s.re}

lemma cubicThetaClearedFrequency_meromorphic {h : Eisenstein} (hh : h≠0) :
    MeromorphicOn (fun s => (s-4/3)*cubicThetaFrequencyContinuation h s) {s : ℂ | 1<s.re} := by
  intro s hs
  exact (analyticAt_id.sub analyticAt_const).meromorphicAt.mul
    (cubicThetaFrequencyContinuation_meromorphic hh hs)

theorem cubicThetaRegularizedFrequency_analytic {h : Eisenstein} (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedFrequency h) {s : ℂ | 1<s.re} := by
  apply regularized_analytic (cubicThetaClearedFrequency_meromorphic hh)
  intro s hs
  by_cases he : s=4/3
  · subst s
    have ht := cubicThetaFrequencyContinuation_residue hh (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat,smul_eq_mul] at ht
    have hf := cubicThetaClearedFrequency_meromorphic hh (4/3) (by norm_num)
    exact hf.meromorphicOrderAt_nonneg_iff.mp
      ((tendsto_nhds_iff_meromorphicOrderAt_nonneg hf).mp ⟨_,ht⟩)
  · obtain ⟨g,hg,hfg⟩ := cubicThetaFrequencyContinuation_analytic_germ hh hs he
    refine ⟨fun z => (z-4/3)*g z,(analyticAt_id.sub analyticAt_const).mul hg,?_⟩
    filter_upwards [hfg] with z hz
    rw [hz]

theorem cubicThetaRegularizedFrequency_germ {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1<s.re) :
    cubicThetaRegularizedFrequency h=ᶠ[𝓝[≠] s]
      (fun z => (z-4/3)*cubicThetaFrequencyContinuation h z) :=
  (cubicThetaClearedFrequency_meromorphic hh).toMeromorphicNFOn_eq_self_on_nhdsNE hs

theorem cubicThetaRegularizedFrequency_residue {h : Eisenstein} (hh : h≠0) :
    cubicThetaRegularizedFrequency h (4/3)=cubicThetaArithmeticFourierResidue h (4/3) := by
  have ha := cubicThetaRegularizedFrequency_analytic hh (4/3) (by norm_num)
  have ht := cubicThetaFrequencyContinuation_residue hh (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat,smul_eq_mul] at ht
  have hg := cubicThetaRegularizedFrequency_germ hh (s:=(4/3:ℂ)) (by norm_num)
  exact tendsto_nhds_unique (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (ht.congr' hg.symm)

end CubicFirstMoment

end

end OAI
