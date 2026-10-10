import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace OAI

/-! A boundary maximum principle requiring only upper limits of the
real part. The holomorphic function itself need not extend continuously
to the boundary. This is used before constructing boundary extensions. -/
open Set Function Filter Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma real_part_le_of_boundary_upper_limits {U : Set ℂ} {f : ℂ → ℂ} {C : ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hcompact : IsCompact (closure U))
    (hboundary : (frontier U).Nonempty) (hd : DifferentiableOn ℂ f U)
    (hb : ∀p∈frontier U,∀ε:ℝ,0<ε →
      ∀ᶠ z in 𝓝[U] p,(f z).re<C+ε) : ∀z∈U,(f z).re≤C := by
  intro z hz
  by_contra hzC
  have hCz : C<(f z).re := lt_of_not_ge hzC
  let r : ℝ := (C+(f z).re)/2
  have hCr : C<r := by dsimp [r]; linarith
  have hrz : r<(f z).re := by dsimp [r]; linarith
  let S : Set ℂ := {w∈U | r≤(f w).re}
  have hzS : z∈S := ⟨hz,hrz.le⟩
  have hSU : S⊆U := fun _ hw => hw.1
  have hcl : closure S⊆U := by
    intro p hp
    by_contra hpU
    have hpbd : p∈frontier U := by
      rw [hU.frontier_eq]
      exact ⟨closure_mono hSU hp,hpU⟩
    have : NeBot (𝓝[S] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
    have he := (hb p hpbd ((r-C)/2) (by linarith)).filter_mono (nhdsWithin_mono p hSU)
    have hSmem : ∀ᶠ w in 𝓝[S] p,w∈S := self_mem_nhdsWithin
    obtain ⟨w,hw,hew⟩ := (hSmem.and he).exists
    have hwr : r≤(f w).re := hw.2
    linarith
  have hSc : IsCompact (closure S) := hcompact.of_isClosed_subset isClosed_closure (closure_mono hSU)
  have hcont : ContinuousOn (fun w => (f w).re) (closure S) :=
    continuous_re.comp_continuousOn (hd.continuousOn.mono hcl)
  obtain ⟨a,ha,hamax⟩ := hSc.exists_isMaxOn ⟨z,subset_closure hzS⟩ hcont
  have haU := hcl ha
  have hza : (f z).re≤(f a).re := hamax (subset_closure hzS)
  have hmax : IsMaxOn (fun w => (f w).re) U a := by
    intro w hw
    by_cases hwS : w∈S
    · exact hamax (subset_closure hwS)
    · have hwr : (f w).re<r := lt_of_not_ge (fun hrw => hwS ⟨hw,hrw⟩)
      exact hwr.le.trans (hrz.le.trans hza)
  have hexp : DifferentiableOn ℂ (fun w => exp (f w)) U :=
    differentiable_exp.comp_differentiableOn hd
  have hexpmax : IsMaxOn (norm ∘ fun w => exp (f w)) U a := by
    intro w hw
    change ‖exp (f w)‖≤‖exp (f a)‖
    simpa only [norm_exp] using Real.exp_le_exp.mpr (hmax hw)
  have hconst := norm_eqOn_of_isPreconnected_of_isMaxOn hconn hU hexp haU hexpmax
  have hre (w : ℂ) (hw : w∈U) : (f w).re=(f a).re := by
    apply Real.exp_injective
    simpa only [Function.comp_apply,Function.const_apply,norm_exp] using hconst hw
  obtain ⟨p,hp⟩ := hboundary
  have : NeBot (𝓝[U] p) := mem_closure_iff_nhdsWithin_neBot.mp hp.1
  have hgap : 0<((f a).re-C)/2 := by linarith
  have hUmem : ∀ᶠ w in 𝓝[U] p,w∈U := self_mem_nhdsWithin
  obtain ⟨w,hw,hwb⟩ := (hUmem.and (hb p hp _ hgap)).exists
  rw [hre w hw] at hwb
  linarith

end CircleDomainRigidity

end

end OAI
