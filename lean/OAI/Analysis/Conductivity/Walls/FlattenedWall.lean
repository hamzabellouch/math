import Mathlib
import OAI.Analysis.Conductivity.Walls.SimpleWallGraph
import OAI.Analysis.Conductivity.Variational.ParametricDiffeomorph
import OAI.Analysis.Conductivity.Variational.SmoothNormalizedEndFamily

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

theorem exists_flat_parametric_root
    {g : (P×Q)×ℝ → ℝ} (hg : ContDiff ℝ (↑(⊤:ℕ∞)) g)
    (p : P) (q : Q) (hz : ∀ y,g ((p,y),0)=0)
    (hne : wallDerivative g ((p,q),0)≠0) :
    ∃ ρ : P×Q → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) ρ ∧
      (∀ y,ρ (p,y)=0) ∧ ∀ᶠ z in 𝓝 (p,q),g (z,ρ z)=0 := by
  let z : P×Q := (p,q)
  have hd : (fderiv ℝ (fun t => g (z,t)) 0) 1≠0 := by
    have he := (real_section_hasDeriv (hg.differentiable (by simp)) z 0).hasFDerivAt.fderiv
    simpa [he,ContinuousLinearMap.toSpanSingleton_apply,z] using hne
  obtain ⟨L,hL⟩ := realCLM_invertible hd
  obtain ⟨Y,hYs,_,hY,hsm,hinv⟩ := exists_parametric_diffeomorph hg z 0 L hL.symm isOpen_univ (mem_univ _)
  have hf (a : P×Q) (t : ℝ) : (Y (a,t)).1=a := by rw [hY]
  have hYt : (z,0)∈Y.target := by
    simpa only [hY,z,hz] using Y.map_source hYs
  let N : Set (P×Q) := {a | (a,(0:ℝ))∈Y.source∩Y.target}
  have hN : IsOpen N := (Y.open_source.inter Y.open_target).preimage (continuous_id.prodMk continuous_const)
  have hzN : z∈N := ⟨hYs,hYt⟩
  let ψ : P×Q → ℝ := fun a => (Y.symm (a,0)).2
  have hψ : ContDiffOn ℝ (↑(⊤:ℕ∞)) ψ N :=
    contDiff_snd.contDiffOn.comp (hinv.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun _ ha => ha.2)) (fun _ _ => mem_univ _)
  have hroot (a : P×Q) (ha : a∈N) : g (a,ψ a)=0 := by
    have he := congrArg Prod.snd (Y.right_inv ha.2)
    rw [hY] at he
    rw [fiberInverse_fst Y hf ha.2] at he
    exact he
  have hflat (y : Q) (hy : (p,y)∈N) : ψ (p,y)=0 := by
    have he := congrArg Prod.snd (Y.left_inv hy.1)
    simpa only [hY,hz,ψ] using he
  let Ω := N∩Metric.ball z 1
  have hΩ : IsOpen Ω := hN.inter Metric.isOpen_ball
  have hzΩ : z∈Ω := ⟨hzN,Metric.mem_ball_self zero_lt_one⟩
  obtain ⟨χ,hχ,_,hχs,_,hχone⟩ := exists_smooth_core_cutoff isCompact_singleton hΩ
    (Metric.isBounded_ball.subset inter_subset_right) (singleton_subset_iff.mpr hzΩ)
  refine ⟨fun a => χ a*ψ a,?_,?_,?_⟩
  · exact smooth_mul_of_support_in_open hN hψ hχ (hχs.trans inter_subset_left)
  · intro y
    change χ (p,y)*ψ (p,y)=0
    by_cases hh : χ (p,y)=0
    · rw [hh,zero_mul]
    · rw [hflat y (hχs (subset_tsupport χ hh)).1,mul_zero]
  · filter_upwards [hN.mem_nhds hzN,hχone z (mem_singleton z)] with a ha hχa
    simpa only [hχa,one_mul] using hroot a ha

end ScalarConductivity

end
end

end OAI
