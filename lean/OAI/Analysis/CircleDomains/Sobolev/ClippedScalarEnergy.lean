import OAI.Analysis.CircleDomains.Transfer.BoundedScalarFillings
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace OAI

/-! Clipping the transferred scalar preserves its source values and does
not increase its actual differential energy, including on the clipping levels. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem clipScalar_of_nonpos {t : ℝ} (ht : t ≤ 0) : clipScalar t = 0 := by
  rw [clipScalar, min_eq_right (ht.trans zero_le_one), max_eq_left ht]

theorem clipScalar_of_one_le {t : ℝ} (ht : 1 ≤ t) : clipScalar t = 1 := by
  rw [clipScalar, min_eq_left ht, max_eq_right zero_le_one]

theorem fderiv_clipScalar_comp {u : ℂ → ℝ} {z : ℂ} (hu : ContinuousAt u z) :
    fderiv ℝ (clipScalar ∘ u) z = 0 ∨
      fderiv ℝ (clipScalar ∘ u) z = fderiv ℝ u z := by
  by_cases h0 : u z ≤ 0
  · left
    apply IsLocalMin.fderiv_eq_zero
    exact Eventually.of_forall fun y => by
      change clipScalar (u z) ≤ clipScalar (u y)
      rw [clipScalar_of_nonpos h0]
      exact (clipScalar_mem _).1
  · by_cases h1 : 1 ≤ u z
    · left
      apply IsLocalMax.fderiv_eq_zero
      exact Eventually.of_forall fun y => by
        change clipScalar (u y) ≤ clipScalar (u z)
        rw [clipScalar_of_one_le h1]
        exact (clipScalar_mem _).2
    · right
      apply EventuallyEq.fderiv_eq
      have h := hu.tendsto (Ioo_mem_nhds (lt_of_not_ge h0) (lt_of_not_ge h1))
      filter_upwards [h] with y hy
      exact clipScalar_eq ⟨hy.1.le, hy.2.le⟩

theorem euclideanGradientEnergy_clipScalar_le {u : ℂ → ℝ} {z : ℂ}
    (hu : ContinuousAt u z) :
    euclideanGradientEnergy (clipScalar ∘ u) z ≤ euclideanGradientEnergy u z := by
  rcases fderiv_clipScalar_comp hu with h | h
  · simp only [euclideanGradientEnergy, h, zero_apply, zero_pow (by decide : 2 ≠ 0), zero_add]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · simp only [euclideanGradientEnergy, h, le_refl]

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel.HoleFilling
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
  {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)

theorem filled_gradient_le {z : ℂ} (hz : (z : Sphere) ∈ (R.model.stages n).domain) :
    euclideanGradientEnergy F.filled z ≤ euclideanGradientEnergy (R.transferred i n) z := by
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  have hz' : z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain := hz
  have heq : F.filled =ᶠ[𝓝 z] clipScalar ∘ R.transferred i n := by
    filter_upwards [hU.mem_nhds hz'] with y hy
    exact F.filled_on_domain hy
  have hd := heq.fderiv_eq (𝕜 := ℝ)
  have h := euclideanGradientEnergy_clipScalar_le
    ((R.transferred_continuousOn i n).continuousAt (hU.mem_nhds hz'))
  simpa only [euclideanGradientEnergy, ← hd] using h

end RetainedRealCircleModel.HoleFilling
end CircleDomainRigidity

end

end OAI
