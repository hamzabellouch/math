import OAI.Dynamics.EntropyCounterexample.MapErasure
import OAI.Dynamics.EntropyCounterexample.MapData
import OAI.Dynamics.EntropyCounterexample.MapOrbitLift

namespace OAI

noncomputable section

open Filter
open scoped OnePoint

namespace Problem340.ConcreteErasure

open Construction ConstructionErasure

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem concreteMap_registers_eventually_zero_of_norm_escape
    (L : ℝ) (hL : 2 < L) (x : RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (hclock : ∀ n, ((concreteMap L hL)^[n] x).1 = (t n : AddCircle (100 : ℝ)))
    (hmain : ∀ n, ((concreteMap L hL)^[n] x).2.1 = (z n : Sphere))
    (ht : Monotone t) (htop : Tendsto t atTop atTop)
    (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    (hz : Tendsto (fun n => ‖z n‖) atTop atTop) :
    ∀ᶠ n in atTop, ∀ i : Fin 3,
      ((concreteMap L hL)^[n] x).2.2 i = ((0 : ℂ) : Sphere) := by
  apply rawMap_registers_eventually_zero_of_norm_escape (concreteData L hL) x t z
    (concrete_saturation_zero L hL)
  · intro s hs
    exact gainProfile_eq_zero L hs
  · exact hclock
  · exact hmain
  · exact ht
  · exact htop
  · exact hstep
  · exact SphereCutoffs.hasCompactSupport_affinePreparationCutoff
  · exact hz

theorem concreteMap_infty_eventually_zero
    (L : ℝ) (hL : 2 < L) (t : AddCircle (100 : ℝ)) (v : Fin 3 → Sphere) :
    ∀ᶠ n in atTop,
      ((concreteMap L hL)^[n] (t, ∞, v)).2.1 = ∞ ∧
      ∀ i : Fin 3, ((concreteMap L hL)^[n] (t, ∞, v)).2.2 i = ((0 : ℂ) : Sphere) := by
  obtain ⟨t₀, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hreg := rawMap_infty_registers_eventually_zero (concreteData L hL) t₀ v
    (concrete_gate_infty L hL) rfl (concrete_saturation_zero L hL)
    (fun s hs => gainProfile_eq_zero L hs)
  filter_upwards [hreg] with n hn
  exact ⟨(rawMap_orbit_infty (concreteData L hL) (concrete_gate_infty L hL) t₀ v n).2, hn⟩

private theorem tendsto_atTop_of_eventually_unit_steps (t : ℕ → ℝ)
    (hstep : ∀ᶠ n in atTop, t (n + 1) = t n + 1) : Tendsto t atTop atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hstep
  have hformula : ∀ m : ℕ, t (m + N) = t N + m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          t (m + 1 + N) = t (m + N + 1) := by congr 1; omega
          _ = t (m + N) + 1 := hN (m + N) (by omega)
          _ = t N + (m + 1 : ℕ) := by rw [ih]; push_cast; ring
  apply (tendsto_add_atTop_iff_nat N).mp
  simp_rw [hformula]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => t N) atTop (nhds (t N))).add_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ))

theorem concreteMap_registers_eventually_zero_of_escape
    (L : ℝ) (hL : 2 < L) (x : RawManifold) (z : ℕ → ℂ)
    (hmain : ∀ n, (z n : Sphere) = ((concreteMap L hL)^[n] x).2.1)
    (hz : Tendsto (fun n => ‖z n‖) atTop atTop) :
    ∀ᶠ n in atTop, ∀ i : Fin 3,
      ((concreteMap L hL)^[n] x).2.2 i = ((0 : ℂ) : Sphere) := by
  obtain ⟨t₀, ht₀⟩ := QuotientAddGroup.mk_surjective x.1
  let t := rawClockLift (concreteData L hL) x t₀
  have hunit : ∀ᶠ n in atTop, t (n + 1) = t n + 1 := by
    filter_upwards [hz.eventually_ge_atTop 1] with n hn
    have hgate : (concreteData L hL).gate (((rawMap (concreteData L hL))^[n] x).2.1) = 1 := by
      change (concreteData L hL).gate (((concreteMap L hL)^[n] x).2.1) = 1
      rw [← hmain n]
      apply SphereCutoffs.affineClockGate_eq_one
      linarith
    change rawClockLift _ _ _ (n + 1) = _
    rw [rawClockLift_succ _ _ _ ht₀, hgate, Clock.increment_one]
  apply concreteMap_registers_eventually_zero_of_norm_escape L hL x t z
  · intro n
    exact (coe_rawClockLift _ _ _ ht₀ n).symm
  · intro n
    exact (hmain n).symm
  · exact monotone_rawClockLift _ (concrete_gate_mem_Icc L hL) x t₀
  · exact tendsto_atTop_of_eventually_unit_steps t hunit
  · intro n
    have hs := (rawClockLift_step_bounds _ (concrete_gate_mem_Icc L hL) x t₀ n).2
    change t (n + 1) - t n ≤ 1 at hs
    linarith
  · exact hz

end Problem340.ConcreteErasure

end

end OAI
