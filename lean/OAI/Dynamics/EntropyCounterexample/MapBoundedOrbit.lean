import OAI.Dynamics.EntropyCounterexample.MapData
import OAI.Dynamics.EntropyCounterexample.MapOrbitLift
import OAI.Dynamics.EntropyCounterexample.ClockOrbit

namespace OAI

noncomputable section
open Filter Set
open scoped Topology OnePoint

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem rawClockLift_liftedOrbit (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ) (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) :
    Clock.LiftedOrbit (rawClockLift D x t₀)
      (fun n => D.gate (((rawMap D)^[n] x).2.1)) where
  cutoff_nonneg _ := (hgate _).1
  cutoff_le_one _ := (hgate _).2
  update := rawClockLift_succ D x t₀ h₀

theorem periodicReadout_coe_periodic (i : Fin 3) :
    Function.Periodic (fun t : ℝ => periodicReadout i (t : AddCircle (100 : ℝ))) 100 := by
  intro t
  change periodicReadout i ((t + 100 : ℝ) : AddCircle (100 : ℝ)) = _
  rw [AddCircle.coe_add_period]

theorem periodicReadout_coe_eq_zero_near_fifty (i : Fin 3) {t : ℝ}
    (ht : t ∈ Set.Ioo (48 : ℝ) 52) :
    periodicReadout i (t : AddCircle (100 : ℝ)) = 0 := by
  rw [periodicReadout, AddCircle.liftIco_coe_apply (show t ∈ Set.Ico (0 : ℝ) (0 + 100) by
    constructor <;> linarith [ht.1, ht.2])]
  by_contra hn
  have hs : t ∈ Function.support (readoutCoeff i) := hn
  rw [readoutCoeff_support] at hs
  have hread := readoutInterval_subset i hs
  linarith [ht.2, hread.1]

theorem readout_eq_sum_smul (D : SphereData) (t : AddCircle (100 : ℝ))
    (v : Fin 3 → Sphere) :
    readout D t v = ∑ i : Fin 3, periodicReadout i t • (20 * D.saturation (v i)) := by
  unfold readout
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.real_smul]
  ring

theorem raw_clock_tendsto_of_bounded (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ) (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hbounded : BddAbove (Set.range (rawClockLift D x t₀))) :
    Tendsto (fun n => ((rawMap D)^[n] x).1) atTop
      (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) := by
  have hclock := rawClockLift_liftedOrbit D hgate x t₀ h₀
  exact (hclock.bounded_circle_limit hbounded).congr (coe_rawClockLift D x t₀ h₀)

theorem raw_main_tendsto_zero_of_bounded (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (hgate_infty : D.gate ∞ = 1)
    (hgate_large : ∀ w : ℂ, 3 / 4 ≤ ‖w‖ → D.gate (w : Sphere) = 1)
    (x : RawManifold) (t₀ : ℝ) (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hbounded : BddAbove (Set.range (rawClockLift D x t₀))) :
    Tendsto (fun n => ((rawMap D)^[n] x).2.1) atTop (𝓝 ((0 : ℂ) : Sphere)) := by
  have hclock := rawClockLift_liftedOrbit D hgate x t₀ h₀
  apply hclock.onePoint_main_tendsto_zero_of_readouts hbounded
    (β := fun i t => periodicReadout i (t : AddCircle (100 : ℝ)))
    (u := fun n i => 20 * D.saturation (((rawMap D)^[n] x).2.2 i))
  · intro n hn
    rw [Function.iterate_succ_apply']
    change perturbedSquare _ (((rawMap D)^[n] x).2.1) = ∞
    rw [hn, perturbedSquare_infty]
  · intro n hn
    rw [hn, hgate_infty]
  · intro n w hn hw
    rw [hn]
    exact hgate_large w hw
  · exact periodicReadout_coe_periodic
  · intro i t ht
    exact periodicReadout_coe_eq_zero_near_fifty i ht
  · intro n w hn
    rw [Function.iterate_succ_apply']
    change perturbedSquare _ (((rawMap D)^[n] x).2.1) = _
    rw [hn, perturbedSquare_coe]
    apply OnePoint.coe_injective
    congr 1
    rw [readout_eq_sum_smul]
    simp only [coe_rawClockLift D x t₀ h₀ n]

theorem concrete_bounded_clock_limits (L : ℝ) (hL : 2 < L)
    (x : RawManifold) (t₀ : ℝ) (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hbounded : BddAbove (Set.range (rawClockLift (concreteData L hL) x t₀))) :
    Tendsto (fun n => ((concreteMap L hL)^[n] x).1) atTop
      (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
    Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
      (𝓝 ((0 : ℂ) : Sphere)) := by
  refine ⟨raw_clock_tendsto_of_bounded _ (concrete_gate_mem_Icc L hL) x t₀ h₀ hbounded, ?_⟩
  apply raw_main_tendsto_zero_of_bounded _ (concrete_gate_mem_Icc L hL)
    (concrete_gate_infty L hL) _ x t₀ h₀ hbounded
  intro w hw
  exact SphereCutoffs.affineClockGate_eq_one hw

end Problem340.Construction

end

end OAI
