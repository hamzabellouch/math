import OAI.Analysis.CircleDomains.Sobolev.ThreeL2WeakLimits
import OAI.Analysis.CircleDomains.Modulus.FilledScalarNormBounds
import OAI.Analysis.CircleDomains.Sobolev.FiniteSphericalArea

namespace OAI

/-! A common subsequence of the actual finite scalar fillings and their
two differentials. The scalar is bounded in spherical L²; the differentials
are bounded in ordinary planar L². -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def planarSphericalArea : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (sphericalAreaDensity z))

instance finitePlanarSphericalArea : IsFiniteMeasure planarSphericalArea :=
  isFiniteMeasure_withDensity integrable_sphericalAreaDensity.lintegral_lt_top.ne

instance separablePlanarSphericalArea : IsSeparable planarSphericalArea := by
  unfold planarSphericalArea
  infer_instance

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem exists_filled_weak_limits (i : Fin m) (F : ∀ n, R.HoleFilling i n) :
    ∃ (V : Lp ℝ 2 planarSphericalArea) (G₁ G₂ : Lp ℝ 2 (volume : Measure ℂ))
      (σ : ℕ → ℕ), StrictMono σ ∧
      (∃ τ : ℕ → ℕ, StrictMono τ ∧ σ = R.limit.subsequence ∘ τ) ∧
      (∀ w : Lp ℝ 2 planarSphericalArea,
        Tendsto (fun n => ∫ z, (F (σ n)).filled z * w z ∂planarSphericalArea)
          atTop (𝓝 (∫ z, V z * w z ∂planarSphericalArea))) ∧
      (∀ w : Lp ℝ 2 (volume : Measure ℂ),
        Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z 1 * w z)
          atTop (𝓝 (∫ z, G₁ z * w z))) ∧
      (∀ w : Lp ℝ 2 (volume : Measure ℂ),
        Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z Complex.I * w z)
          atTop (𝓝 (∫ z, G₂ z * w z))) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (R.limit.strict.tendsto_atTop.eventually (R.eventually_filled_partial_norm_bounds i))
  choose h₁ h₂ hb₁ hb₂ using fun n => hN (N + n) (Nat.le_add_right N n) (F (R.limit.subsequence (N + n)))
  let u₀ : ℕ → ℂ → ℝ := fun n => (F (R.limit.subsequence (N + n))).filled
  let u₁ : ℕ → ℂ → ℝ := fun n z => fderiv ℝ (F (R.limit.subsequence (N + n))).filled z 1
  let u₂ : ℕ → ℂ → ℝ := fun n z => fderiv ℝ (F (R.limit.subsequence (N + n))).filled z Complex.I
  have h₀ (n : ℕ) : MemLp (u₀ n) 2 planarSphericalArea := (F (R.limit.subsequence (N + n))).filled_memLp
  obtain ⟨V, G₁, G₂, τ, hτ, hv, hg₁, hg₂⟩ :=
    exists_three_L2_weak_limits planarSphericalArea volume volume u₀ u₁ u₂ h₀ h₁ h₂
      _ _ _ (fun n => (F (R.limit.subsequence (N + n))).filled_norm_bound R) hb₁ hb₂
  refine ⟨V, G₁, G₂, fun n => R.limit.subsequence (N + τ n),
    R.limit.strict.comp (fun a b hab => Nat.add_lt_add_left (hτ hab) N),
    ⟨fun n => N + τ n, fun a b hab => Nat.add_lt_add_left (hτ hab) N, rfl⟩,
    hv, hg₁, hg₂⟩

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
