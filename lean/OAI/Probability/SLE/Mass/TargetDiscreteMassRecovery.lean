import OAI.Probability.SLE.Mass.MassCompensatorRecovery
import OAI.Probability.SLE.Gauge.MomentCoefficientConvergence

namespace OAI

/-! The exact finite sum in the prescribed coefficient formula agrees
with the stopped predictable compensator once its potential increments
have been identified. The endpoint is allowed to be infinite. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma compensator_before_extended_sum (n : ℕ) (T : ℝ≥0∞) (q : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n*2^n),
      if (compensatorMeshTime n (i+1):ℝ≥0∞) ≤ T then q i else 0) =
      ∑ i ∈ Finset.range (compensatorStopIndex n T), q i := by
  by_cases hT : T=∞
  · simp [hT,compensatorStopIndex]
  · have he : T=(T.toNNReal:ℝ≥0∞) := (ENNReal.coe_toNNReal hT).symm
    conv_lhs => rw [he]
    simp only [ENNReal.coe_le_coe]
    rw [compensator_before_sum,compensatorStopIndex,ite_eq_right hT]

lemma target_mesh_time (n i : ℕ) :
    ENNReal.ofReal (((i:ℝ)+1)*Target.mesh n) =
      (compensatorMeshTime n (i+1):ℝ≥0∞) := by
  have he : (compensatorMeshTime n (i+1):ℝ)=((i:ℝ)+1)*Target.mesh n := by
    simp [compensatorMeshTime,Target.mesh]
  rw [← he,ENNReal.ofReal_coe_nnreal]

lemma target_discreteMass_eq_sum (κ θ : ℝ) (W : Target.WienerLaw)
    (b : Target.Driver) (ℓ : ℝ) (n : ℕ) :
    Target.discreteMass κ θ W b ℓ n =
      ∑ i ∈ Finset.range (compensatorStopIndex n (Target.levelTime κ θ b ℓ)),
        Target.potentialDifference κ θ W b n i := by
  unfold Target.discreteMass
  simp_rw [target_mesh_time]
  exact compensator_before_extended_sum n _ _

theorem target_discreteMass_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ θ : ℝ) (W : Target.WienerLaw) (b : Ω → Target.Driver) (ℓ : ℝ)
    (ℱ : ℕ → Filtration ℕ mΩ) (A : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ)
    (hA : ∀ t, Measurable (A t))
    (hgrid : ∀ n i, StronglyMeasurable[ℱ n i] (A (compensatorMeshTime n i)))
    (hL : MemLp L 2 P)
    (hp : ∀ᵐ ω ∂P, Monotone (fun t => A t ω) ∧ A 0 ω=0 ∧
      Continuous (fun t => A t ω) ∧ Tendsto (fun t => A t ω) atTop (𝓝 (L ω)) ∧
      ∀ t, A t ω ≤ L ω)
    (hT : Measurable (fun ω => Target.levelTime κ θ (b ω) ℓ))
    (hq : ∀ n i, (fun ω => Target.potentialDifference κ θ W (b ω) n i) =ᵐ[P]
      condExp (ℱ n i) P (meshMassIncrement A n i)) :
    TendstoInMeasure P (fun n ω => Target.discreteMass κ θ W (b ω) ℓ n) atTop
      (fun ω => massAtExtendedTime (fun t => A t ω) (L ω)
        (Target.levelTime κ θ (b ω) ℓ)) := by
  have h := meshMassCompensator_stopped_tendstoInMeasure P ℱ A L hA hgrid hL hp
    (fun ω => Target.levelTime κ θ (b ω) ℓ) hT
  apply h.congr _ (Filter.EventuallyEq.refl _ _)
  intro n
  filter_upwards [ae_all_iff.mpr (hq n)] with ω hω
  rw [target_discreteMass_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => (hω i).symm)

end SLEExactGauge

end

end OAI
