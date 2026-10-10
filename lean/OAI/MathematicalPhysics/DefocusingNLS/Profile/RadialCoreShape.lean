import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoreCompactness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialLimitFreeEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTransition
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTailDecrease

namespace OAI

/-! The actual large-power inner profiles limit to one plateau and one decreasing free tail. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_coupled_core_shape (R : ℝ) (P : ℕ → RadialInnerData)
    (hR : ∀ n, (P n).R=R) (H : ℕ → ℝ → ℝ)
    (hH : ∀ n, RadialInnerOutputSpec (P n).p R (P n).lo (P n).c (P n).b (H n) (H n))
    (hp : Tendsto (fun n => (P n).p) atTop atTop)
    (c b h₀ : ℝ) (hc : c ∈ Icc (599/100 : ℝ) 6) (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (hcT : Tendsto (fun n => (P n).c) atTop (𝓝 c))
    (hbT : Tendsto (fun n => (P n).b) atTop (𝓝 b))
    (hloT : Tendsto (fun n => (P n).lo) atTop (𝓝 h₀)) (hlo1 : h₀ < 1) :
    ∃ A D : ℝ → ℝ, Continuous A ∧ Continuous D ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformlyOn (fun n => H (φ n)) A atTop (Icc 0 R) ∧
      TendstoUniformlyOn (fun n => deriv (H (φ n))) D atTop (Icc 0 R) ∧
      A R=h₀ ∧ ∃ ρ ∈ Ico (R-7/10000) R,
        EqOn A (fun _ => 1) (Icc 0 ρ) ∧ D ρ=0 ∧
        (∀ r ∈ Ioc ρ R, A r < 1) ∧ StrictAntiOn A (Icc ρ R) ∧
        (∀ r ∈ Ioo ρ R, HasDerivAt A (D r) r ∧ HasDerivAt D
          (-11/r*D r-radialAmplitudePotential c b A r*A r) r) := by
  obtain ⟨A,D,hA,hD,φ,hφ,hTA,hTD,hAD,hD0,hcore,hBounds⟩ :=
    radial_coupled_core_subsequence R P hR H hH hp
  have hR1 : 1 ≤ R := by simpa only [hR 0] using (P 0).hR
  have hR2 : R^2 ≤ 11 := by simpa only [hR 0] using (P 0).hR2
  have hAR : A R=h₀ := by
    have hleft := hTA.tendsto_at (show R ∈ Icc 0 R from ⟨by linarith,le_rfl⟩)
    have hright := hloT.comp hφ.tendsto_atTop
    have heq : (fun n => H (φ n) R)=(fun n => (P (φ n)).lo) :=
      funext (fun n => (hH (φ n)).2.2.1)
    change Tendsto (fun n => (P (φ n)).lo) atTop (𝓝 h₀) at hright
    rw [← heq] at hright
    exact tendsto_nhds_unique hleft hright
  let V := radialAmplitudePotential c b A
  have hAI : ∀ r ∈ Icc 0 R, A r ∈ Ioc 0 1 := by
    intro r hr
    have h := (hBounds r hr).1
    exact ⟨lt_of_lt_of_le (by norm_num) h.1,h.2⟩
  have hV : ∀ r ∈ Ioo 0 R, 0 < V r := by
    intro r hr
    have h := radialAmplitudePotential_bounds c b R hc hb hR2 A hA
      (fun t ht => (hBounds t ht).1) r ⟨hr.1.le,hr.2.le⟩
    exact lt_of_lt_of_le (by norm_num) h.1
  have hFree := radial_inner_limit_free_equation R (fun n => P (φ n)) (fun n => hR (φ n))
    (fun n => H (φ n)) (fun n => hH (φ n)) (hp.comp hφ.tendsto_atTop)
    c b hc (hcT.comp hφ.tendsto_atTop) (hbT.comp hφ.tendsto_atTop)
    A D hA hD (fun r hr => (hBounds r hr).1) hTA hTD
  obtain ⟨ρ,hρ,hplat,hsub,hDρ⟩ := radial_limit_single_transition R (R-7/10000)
    (by linarith) (by linarith) A D V hA hAI hAD
    (fun r hr hlt => (hFree r hr hlt).2) hV hcore (by rw [hAR]; exact hlo1)
  have hρ0 : 0 < ρ := by linarith [hρ.1]
  have htail := radial_free_tail_decreasing ρ R hρ0 hρ.2 A D V hA hD
    (fun r hr => (hAI r ⟨by linarith [hr.1],hr.2.le⟩).1)
    (fun r hr => hV r ⟨by linarith [hr.1],hr.2⟩)
    (fun r hr => hAD r ⟨by linarith [hr.1],hr.2⟩)
    (fun r hr => (hFree r ⟨by linarith [hr.1],hr.2⟩ (hsub r ⟨hr.1,hr.2.le⟩)).2) hDρ
  refine ⟨A,D,hA,hD,φ,hφ,hTA,hTD,hAR,ρ,hρ,hplat,hDρ,hsub,htail.2,?_⟩
  intro r hr
  exact hFree r ⟨by linarith [hr.1],hr.2⟩ (hsub r ⟨hr.1,hr.2.le⟩)

end DefocusingNLS

end OAI
