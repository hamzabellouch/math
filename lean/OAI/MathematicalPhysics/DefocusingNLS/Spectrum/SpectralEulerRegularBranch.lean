import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEulerInvariants
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialOriginDecay

namespace OAI

/-! Weighted H¹ regularity removes the singular branch of the core Euler equation. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralEuler_reconstruct (n : ℕ) (g P : ℝ → ℂ) (r : ℝ) (hr : r ≠ 0) :
    (2*(n : ℂ)+10)*g r=spectralEulerGrowing n g P r*(r : ℂ)^n+
      spectralEulerSingular n g P r/(r : ℂ)^(n+10) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  dsimp only [spectralEulerGrowing,spectralEulerSingular]
  field_simp
  ring

theorem spectralEuler_regular_branch (n : ℕ) (L : ℝ) (hL : 0 < L) (g P : ℝ → ℂ)
    (hg : ∀ x ∈ Ioo 0 L, HasDerivAt g (P x/(x : ℂ)^11) x)
    (hP : ∀ x ∈ Ioo 0 L,
      HasDerivAt P ((n : ℂ)*((n : ℂ)+10)*(x : ℂ)^9*g x) x)
    (hdec : Tendsto (fun r : ℝ => (r : ℂ)^(n+10)*g r) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∃ C : ℂ, ∀ r ∈ Ioo 0 L, g r=C*(r : ℂ)^n := by
  let t := L/2
  have ht : t ∈ Ioo 0 L := by dsimp only [t]; constructor <;> linarith
  let A := spectralEulerGrowing n g P t
  let B := spectralEulerSingular n g P t
  have he (r : ℝ) (hr : r ∈ Ioo 0 L) :
      (2*(n : ℂ)+10)*(r : ℂ)^(n+10)*g r-A*(r : ℂ)^(2*n+10)=B := by
    have h := spectralEuler_reconstruct n g P r hr.1.ne'
    obtain ⟨ha,hb⟩ := spectralEuler_invariants_constant n L g P hg hP r t hr ht
    rw [ha,hb] at h
    change (2*(n : ℂ)+10)*g r=A*(r : ℂ)^n+B/(r : ℂ)^(n+10) at h
    have hn : (r : ℂ)^(n+10) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hr.1.ne')
    have hp : (r : ℂ)^n*(r : ℂ)^(n+10)=(r : ℂ)^(2*n+10) := by
      rw [← pow_add]
      congr 1
      omega
    have hm := congrArg (fun z : ℂ => z*(r : ℂ)^(n+10)) h
    rw [add_mul (A*(r : ℂ)^n) (B/(r : ℂ)^(n+10)),div_mul_cancel₀ _ hn,
      mul_assoc A ((r : ℂ)^n) ((r : ℂ)^(n+10)),hp] at hm
    linear_combination hm
  have hlim : Tendsto (fun r : ℝ =>
      (2*(n : ℂ)+10)*(r : ℂ)^(n+10)*g r-A*(r : ℂ)^(2*n+10))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hp : Tendsto (fun r : ℝ => A*(r : ℂ)^(2*n+10))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h : Tendsto (fun r : ℝ => A*(r : ℂ)^(2*n+10))
          (𝓝 (0 : ℝ)) (𝓝 (A*(0 : ℂ)^(2*n+10))) :=
        (show Continuous (fun r : ℝ => A*(r : ℂ)^(2*n+10)) by fun_prop).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero,sub_zero,mul_assoc] using (hdec.const_mul (2*(n : ℂ)+10)).sub hp
  have hevent : (fun r : ℝ =>
      (2*(n : ℂ)+10)*(r : ℂ)^(n+10)*g r-A*(r : ℂ)^(2*n+10)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun _ => B := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hL).filter_mono nhdsWithin_le_nhds] with r hr hrL
    exact he r ⟨hr,hrL⟩
  have hB : B=0 := tendsto_nhds_unique tendsto_const_nhds (hlim.congr' hevent)
  have hn : 2*(n : ℂ)+10 ≠ 0 := by
    exact_mod_cast (show 2*(n : ℝ)+10 ≠ 0 by positivity)
  refine ⟨A/(2*(n : ℂ)+10),fun r hr => ?_⟩
  have h := spectralEuler_reconstruct n g P r hr.1.ne'
  obtain ⟨ha,hb⟩ := spectralEuler_invariants_constant n L g P hg hP r t hr ht
  rw [ha,hb] at h
  change (2*(n : ℂ)+10)*g r=A*(r : ℂ)^n+B/(r : ℂ)^(n+10) at h
  rw [hB,zero_div,add_zero] at h
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using h

end DefocusingNLS

end OAI
