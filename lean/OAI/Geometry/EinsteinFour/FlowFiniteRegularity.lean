import OAI.Geometry.EinsteinFour.FlowGermUniqueness
import OAI.Geometry.EinsteinFour.FlowVariationalRegularity

namespace OAI

/-! Finite smooth dependence of actual local ODE solutions on initial data.
The induction applies the existing first-variation construction to its own
variational field, and uses uniqueness to identify the resulting derivatives. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set Metric Filter
open scoped ContDiff Topology

noncomputable section

universe u

theorem local_flow_contDiffAt_finite (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (f : E → E) (α : E × ℝ → E) (p : E),
      ContDiffAt ℝ (n + 2 : ℕ) f p →
      ContDiffAt ℝ 0 α (p, 0) →
      (∀ᶠ q in 𝓝 p, α (q, 0) = q) →
      (∀ᶠ z in 𝓝 (p, (0 : ℝ)),
        HasDerivAt (fun t => α (z.1, t)) (f (α z)) z.2) →
      ContDiffAt ℝ n α (p, 0) := by
  induction n with
  | zero =>
    intro E _ _ _ f α p _ hc _ _
    exact hc
  | succ n ih =>
    intro E _ _ _ f α p hf hc hi hs
    have hf2 : ContDiffAt ℝ 2 f p := hf.of_le (by exact_mod_cast Nat.le_add_left 2 (n + 1))
    obtain ⟨r, hr, ε, hε, A, V, hAc, hVc, hAV⟩ :=
      exists_jointly_differentiable_local_flow f p hf2
    let U := ball p r ×ˢ Ioo (-ε) ε
    have hz : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    have hU : U ∈ 𝓝 (p, (0 : ℝ)) :=
      (isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨mem_ball_self hr, hz⟩
    have hA0 : ∀ᶠ q in 𝓝 p, A (q, 0) = q := by
      filter_upwards [ball_mem_nhds p hr] with q hq
      exact (hAV q hq).1
    have hAs : ∀ᶠ z in 𝓝 (p, (0 : ℝ)),
        HasDerivAt (fun t => A (z.1, t)) (f (A z)) z.2 := by
      filter_upwards [hU] with z hz
      exact ((hAV z.1 hz.1).2.2 z.2 hz.2).1
    have hAeq : α =ᶠ[𝓝 (p, (0 : ℝ))] A := by
      have hiA : ∀ᶠ q in 𝓝 p, α (q, 0) = A (q, 0) := by
        filter_upwards [hi, hA0] with q hq hAq
        exact hq.trans hAq.symm
      apply local_solution_family_eventuallyEq f α A p hc.continuousAt
        (hAc.continuousAt hU) hiA hs hAs
      simpa only [hi.self_of_nhds] using hf2.of_le (by norm_num)
    let B : E × ℝ → VariationSpace E := fun z => (A z, V z)
    let p₀ : VariationSpace E := (p, ContinuousLinearMap.id ℝ E)
    have hB0 : ∀ᶠ q in 𝓝 p, B (q, 0) = (q, ContinuousLinearMap.id ℝ E) := by
      filter_upwards [ball_mem_nhds p hr] with q hq
      exact Prod.ext (hAV q hq).1 (hAV q hq).2.1
    have hBc : ContinuousAt B (p, 0) :=
      (hAc.continuousAt hU).prodMk (hVc.continuousAt hU)
    have hBs : ∀ᶠ z in 𝓝 (p, (0 : ℝ)),
        HasDerivAt (fun t => B (z.1, t)) (variationalField f (B z)) z.2 := by
      filter_upwards [hU] with z hz
      exact (((hAV z.1 hz.1).2.2 z.2 hz.2).1).prodMk
        (((hAV z.1 hz.1).2.2 z.2 hz.2).2.1)
    have hf3 : ContDiffAt ℝ 3 f p := hf.of_le (by exact_mod_cast Nat.le_add_left 3 n)
    have hg2 : ContDiffAt ℝ 2 (variationalField f) p₀ :=
      variationalField_contDiffAt_order 2 f p₀ hf3
    obtain ⟨r₁, hr₁, ε₁, hε₁, G, W, hGc, _, hGW⟩ :=
      exists_jointly_differentiable_local_flow (variationalField f) p₀ hg2
    let U₁ := ball p₀ r₁ ×ˢ Ioo (-ε₁) ε₁
    have hz₁ : (0 : ℝ) ∈ Ioo (-ε₁) ε₁ := ⟨by linarith, hε₁⟩
    have hU₁ : U₁ ∈ 𝓝 (p₀, (0 : ℝ)) :=
      (isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨mem_ball_self hr₁, hz₁⟩
    have hG0 : ∀ᶠ q in 𝓝 p₀, G (q, 0) = q := by
      filter_upwards [ball_mem_nhds p₀ hr₁] with q hq
      exact (hGW q hq).1
    have hGs : ∀ᶠ z in 𝓝 (p₀, (0 : ℝ)),
        HasDerivAt (fun t => G (z.1, t)) (variationalField f (G z)) z.2 := by
      filter_upwards [hU₁] with z hz
      exact ((hGW z.1 hz.1).2.2 z.2 hz.2).1
    have hg : ContDiffAt ℝ (n + 2 : ℕ) (variationalField f) p₀ :=
      variationalField_contDiffAt_order (n + 2) f p₀ (by simpa [Nat.add_assoc] using hf)
    have hGn : ContDiffAt ℝ n G (p₀, 0) := ih (VariationSpace E)
      (variationalField f) G p₀ hg (contDiffAt_zero.mpr ⟨U₁, hU₁, hGc⟩) hG0 hGs
    let H : E × ℝ → VariationSpace E × ℝ :=
      fun z => ((z.1, ContinuousLinearMap.id ℝ E), z.2)
    have hH : ContDiff ℝ ∞ H :=
      (contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd
    have hH0 : H (p, 0) = (p₀, 0) := rfl
    have hHq : Continuous (fun q : E => (q, ContinuousLinearMap.id ℝ E)) :=
      continuous_id.prodMk continuous_const
    have hGHn : ContDiffAt ℝ n (G ∘ H) (p, 0) :=
      hGn.comp (p, 0) (hH.contDiffAt.of_le (by simp))
    have hGH0 : ∀ᶠ q in 𝓝 p,
        (G ∘ H) (q, 0) = (q, ContinuousLinearMap.id ℝ E) := by
      have ht : Tendsto (fun q : E => (q, ContinuousLinearMap.id ℝ E))
          (𝓝 p) (𝓝 p₀) := hHq.continuousAt
      exact ht.eventually hG0
    have hGHs : ∀ᶠ z in 𝓝 (p, (0 : ℝ)),
        HasDerivAt (fun t => (G ∘ H) (z.1, t))
          (variationalField f ((G ∘ H) z)) z.2 := by
      have ht : Tendsto H (𝓝 (p, 0)) (𝓝 (p₀, 0)) := hH.continuous.continuousAt
      exact ht.eventually hGs
    have hBGeq : B =ᶠ[𝓝 (p, (0 : ℝ))] (G ∘ H) := by
      apply local_solution_family_eventuallyEq (variationalField f) B (G ∘ H) p hBc
        hGHn.continuousAt
      · filter_upwards [hB0, hGH0] with q hBq hGq
        exact hBq.trans hGq.symm
      · exact hBs
      · exact hGHs
      · simpa only [hB0.self_of_nhds] using hg2.of_le (by norm_num)
    have hBn : ContDiffAt ℝ n B (p, 0) :=
      hGHn.congr_of_eventuallyEq hBGeq
    let D : E × ℝ → E × ℝ →L[ℝ] E := fun z =>
      (V z).coprod (ContinuousLinearMap.toSpanSingleton ℝ (f (A z)))
    have hfn : ContDiffAt ℝ n f p := hf.of_le (by exact_mod_cast Nat.le_add_right n 3)
    have hvel : ContDiffAt ℝ n (fun z => f (A z)) (p, 0) := by
      have hAinit : A (p, 0) = p := hA0.self_of_nhds
      have hfp : ContDiffAt ℝ n f (A (p, 0)) := by rwa [hAinit]
      exact hfp.comp (p, 0) hBn.fst
    have hspan : ContDiffAt ℝ n
        (fun z => ContinuousLinearMap.toSpanSingleton ℝ (f (A z))) (p, 0) :=
      (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).contDiff.contDiffAt.comp
        (p, 0) hvel
    have hDn : ContDiffAt ℝ n D (p, 0) := by
      change ContDiffAt ℝ n (fun z =>
        (V z).comp (ContinuousLinearMap.fst ℝ E ℝ) +
        (ContinuousLinearMap.toSpanSingleton ℝ (f (A z))).comp
          (ContinuousLinearMap.snd ℝ E ℝ)) (p, 0)
      exact (hBn.snd.clm_comp contDiffAt_const).add (hspan.clm_comp contDiffAt_const)
    have hAn : ContDiffAt ℝ (n + 1 : ℕ) A (p, 0) := by
      apply contDiffAt_succ_iff_hasFDerivAt.mpr
      refine ⟨D, ⟨U, hU, ?_⟩, hDn⟩
      intro z hz
      exact (((hAV z.1 hz.1).2.2 z.2 hz.2).2.2).hasFDerivAt
    exact hAn.congr_of_eventuallyEq hAeq

end
end PositiveEinsteinFour.FlowCalculus

end OAI
