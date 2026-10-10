import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerCoreLimit

namespace OAI

/-! C¹ compactness and a nonempty flat core for the actual coupled inner profiles. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_coupled_core_subsequence (R : ℝ) (P : ℕ → RadialInnerData)
    (hR : ∀ n, (P n).R=R) (H : ℕ → ℝ → ℝ)
    (hH : ∀ n, RadialInnerOutputSpec (P n).p R (P n).lo (P n).c (P n).b (H n) (H n))
    (hp : Tendsto (fun n => (P n).p) atTop atTop) :
    ∃ A D : ℝ → ℝ, Continuous A ∧ Continuous D ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformlyOn (fun n => H (φ n)) A atTop (Icc 0 R) ∧
      TendstoUniformlyOn (fun n => deriv (H (φ n))) D atTop (Icc 0 R) ∧
      (∀ r ∈ Ioo 0 R, HasDerivAt A (D r) r) ∧ D 0=0 ∧
      EqOn A (fun _ => 1) (Icc 0 (R-7/10000)) ∧
      (∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1 ∧ ‖D r‖ ≤ r/24) := by
  obtain ⟨A,D,hA,hD,φ,hφ,hTA,hTD,hDeriv,hD0⟩ := radial_coupled_C1_subsequence R P hR H hH
  refine ⟨A,D,hA,hD,φ,hφ,hTA,hTD,hDeriv,hD0,?_,?_⟩
  · exact radial_inner_limit_plateau R (fun n => P (φ n)) (fun n => hR (φ n))
      (fun n => H (φ n)) (fun n => hH (φ n)) (hp.comp hφ.tendsto_atTop)
      A (fun r hr => hTA.tendsto_at hr)
  · intro r hr
    have hlow : ∀ n, (999/1000 : ℝ) ≤ H (φ n) r := fun n =>
      (P (φ n)).lo_lower.trans ((hH (φ n)).2.2.2.2.1 r hr).1.1
    have hupp : ∀ n, H (φ n) r ≤ 1 := fun n => ((hH (φ n)).2.2.2.2.1 r hr).1.2
    refine ⟨⟨ge_of_tendsto' (hTA.tendsto_at hr) hlow,
      le_of_tendsto' (hTA.tendsto_at hr) hupp⟩,?_⟩
    apply le_of_tendsto' (hTD.tendsto_at hr).norm
    intro n
    have hs : RadialInnerOutputSpec (P (φ n)).p (P (φ n)).R (P (φ n)).lo
        (P (φ n)).c (P (φ n)).b (H (φ n)) (H (φ n)) := by
      simpa only [hR (φ n)] using hH (φ n)
    apply (radial_inner_derivative_bounds (P (φ n)) (H (φ n)) hs).1
    simpa only [hR (φ n)] using hr

end DefocusingNLS

end OAI
