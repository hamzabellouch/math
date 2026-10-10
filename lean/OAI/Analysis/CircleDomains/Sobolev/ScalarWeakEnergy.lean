import OAI.Analysis.CircleDomains.Sobolev.ScalarWeakLimits
import OAI.Analysis.CircleDomains.Sobolev.WeakPairEnergy

namespace OAI

/-! The combined energy of the weak derivative limit is bounded by the
original source energy, without the finite-stage error. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem filled_weak_energy_le (i : Fin m) (F : ∀ n, R.HoleFilling i n)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (G₁ G₂ : Lp ℝ 2 (volume : Measure ℂ))
    (h₁ : ∀ w : Lp ℝ 2 (volume : Measure ℂ),
      Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z 1 * w z)
        atTop (𝓝 (∫ z, G₁ z * w z)))
    (h₂ : ∀ w : Lp ℝ 2 (volume : Measure ℂ),
      Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z Complex.I * w z)
        atTop (𝓝 (∫ z, G₂ z * w z))) :
    (∫ z, G₁ z ^ 2 + G₂ z ^ 2) ≤
      ∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hσ.tendsto_atTop.eventually (R.eventually_filled_global_energy i))
  have ht : StrictMono (fun n : ℕ => N + n) :=
    fun a b hab => Nat.add_lt_add_left hab N
  let u₁ : ℕ → ℂ → ℝ := fun n z => fderiv ℝ (F (σ (N + n))).filled z 1
  let u₂ : ℕ → ℂ → ℝ := fun n z => fderiv ℝ (F (σ (N + n))).filled z Complex.I
  have hi (n : ℕ) := memLp_partials_of_integrable_euclidean_energy
    (hN (N + n) (Nat.le_add_right N n) (F (σ (N + n)))).1
  apply paired_L2_energy_le (u₁ := u₁) (u₂ := u₂)
    (fun n => (hi n).1) (fun n => (hi n).2) G₁ G₂
    (modelError_tendsto.comp (hσ.comp ht).tendsto_atTop)
  · exact Eventually.of_forall fun n =>
      (hN (N + n) (Nat.le_add_right N n) (F (σ (N + n)))).2.le
  · exact (h₁ G₁).comp ht.tendsto_atTop
  · exact (h₂ G₂).comp ht.tendsto_atTop

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
