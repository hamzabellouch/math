import OAI.Dynamics.EntropyCounterexample.ConcreteErasure
import OAI.Dynamics.EntropyCounterexample.MapFiniteOrbit

namespace OAI

noncomputable section

open Filter
open scoped OnePoint

namespace Problem340.ConcreteErasure

open Construction

theorem norm_tendsto_atTop_of_coe_tendsto_infty (z : ℕ → ℂ)
    (hz : Tendsto (fun n => (z n : Sphere)) atTop (nhds ∞)) :
    Tendsto (fun n => ‖z n‖) atTop atTop := by
  have hc : Tendsto z atTop
      (Filter.comap (fun w : ℂ => (w : Sphere)) (nhds ∞)) := by
    exact tendsto_comap_iff.mpr hz
  have hz' : Tendsto z atTop (cocompact ℂ) := by
    simpa only [OnePoint.comap_coe_nhds_infty, coclosedCompact_eq_cocompact] using hc
  exact tendsto_norm_cocompact_atTop.comp hz'

theorem concreteMap_registers_eventually_zero_of_main_tendsto_infty
    (L : ℝ) (hL : 2 < L) (x : RawManifold)
    (hmain : Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1)
      atTop (nhds ∞)) :
    ∀ᶠ n in atTop, ∀ i : Fin 3,
      ((concreteMap L hL)^[n] x).2.2 i = ((0 : ℂ) : Sphere) := by
  by_cases hx : x.2.1 = ∞
  · have heq : (x.1, ∞, x.2.2) = x := by
      rcases x with ⟨t, z, v⟩
      simp_all
    have h := concreteMap_infty_eventually_zero L hL x.1 x.2.2
    rw [heq] at h
    filter_upwards [h] with n hn
    exact hn.2
  · obtain ⟨z, hz, _⟩ := exists_finiteMainOrbit (concreteData L hL) x hx
    apply concreteMap_registers_eventually_zero_of_escape L hL x z hz
    apply norm_tendsto_atTop_of_coe_tendsto_infty
    exact hmain.congr (fun n => (hz n).symm)

theorem concreteMap_mainRegisters_tendsto_of_main_tendsto_infty
    (L : ℝ) (hL : 2 < L) (x : RawManifold)
    (hmain : Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1)
      atTop (nhds ∞)) :
    Tendsto (fun n => ((concreteMap L hL)^[n] x).2) atTop
      (nhds (∞, fun _ : Fin 3 => ((0 : ℂ) : Sphere))) := by
  have herase := concreteMap_registers_eventually_zero_of_main_tendsto_infty L hL x hmain
  have hv : Tendsto (fun n => ((concreteMap L hL)^[n] x).2.2) atTop
      (nhds (fun _ : Fin 3 => ((0 : ℂ) : Sphere))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [herase] with n hn
    exact (funext hn).symm
  exact hmain.prodMk_nhds hv

end Problem340.ConcreteErasure

end

end OAI
