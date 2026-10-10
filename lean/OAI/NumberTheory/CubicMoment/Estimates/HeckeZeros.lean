import OAI.NumberTheory.CubicMoment.Estimates.IdealLogDerivativeTwist
import Mathlib.Analysis.Analytic.Order

namespace OAI

/-! Zeros of the actual entire Hecke continuations: none occur right of
one, bounded sets contain finitely many, and local multiplicities are
positive finite integers. -/
noncomputable section
open Set Filter
open scoped Topology
namespace CubicFirstMoment

theorem heckeSeries_ne_zero {χ : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {L : ℂ → ℂ}
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {s : ℂ} (hs1 : 1 < s.re) : L s ≠ 0 := by
  rw [hs s hs1]
  exact idealDirichlet_ne_zero χ hχ hχ0 hχadd hs1

theorem heckeZero_real_le_one {χ : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {L : ℂ → ℂ}
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {ρ : ℂ} (hρ : L ρ=0) : ρ.re ≤ 1 := by
  by_contra h
  exact heckeSeries_ne_zero hχ hχ0 hχadd hs (lt_of_not_ge h) hρ

lemma entire_zeros_finite_on_compact {L : ℂ → ℂ}
    (hL : Differentiable ℂ L) {s : ℂ} (hs : L s ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) : {z ∈ K | L z=0}.Finite := by
  have ha : AnalyticOnNhd ℂ L univ := fun z _ => hL.analyticAt z
  have hd := ha.preimage_zero_mem_codiscrete hs
  have hdK : L ⁻¹' {0}ᶜ ∈ codiscreteWithin K :=
    (codiscreteWithin_mono (subset_univ K)) hd
  have hf := hK.finite_sdiff_of_mem_codiscreteWithin hdK
  simpa only [Set.sdiff_eq,Set.preimage_compl,compl_compl,Set.inter_def,
    Set.mem_preimage,Set.mem_singleton_iff] using hf

lemma entire_zero_local_factor {L : ℂ → ℂ}
    (hL : Differentiable ℂ L) {s : ℂ} (hs : L s ≠ 0)
    {ρ : ℂ} (hρ : L ρ=0) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
        L =ᶠ[𝓝 ρ] fun z => (z-ρ)^n*g z := by
  have hfinite : analyticOrderAt L ρ ≠ ⊤ := by
    intro htop
    have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ
      (fun z => hL.analyticAt z)).mp htop
    exact hs (congrFun he s)
  obtain ⟨g,hg,hg0,heq⟩ := (hL.analyticAt ρ).analyticOrderAt_ne_top.mp hfinite
  have heq' : L =ᶠ[𝓝 ρ] fun z => (z-ρ)^(analyticOrderAt L ρ).toNat*g z := by
    simpa only [smul_eq_mul,analyticOrderNatAt] using heq
  refine ⟨(analyticOrderAt L ρ).toNat,?_,g,hg,hg0,heq'⟩
  by_contra hn
  have hn0 := Nat.eq_zero_of_not_pos hn
  have he := heq'.self_of_nhds
  dsimp only at he
  rw [hρ,hn0,pow_zero,one_mul] at he
  exact hg0 he.symm

end CubicFirstMoment

end

end OAI
