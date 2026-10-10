import OAI.Analysis.CircleDomains.Topology.FiniteCircleGreen

namespace OAI

/-! Regular Jordan circuits with either orientation. The absolute Stokes
estimate does not need a choice of orientation. -/

open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

structure RegularJordanParametrization (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) γ
  periodic : Function.Periodic γ 1
  injective : InjOn γ (Ico 0 1)
  regular : ∀ t, deriv γ t ≠ 0
  boundary : γ '' Icc 0 1 = frontier (jordanInterior H)

 theorem PositiveJordanParametrization.toRegular
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : PositiveJordanParametrization H γ) :
    RegularJordanParametrization H γ :=
  ⟨hγ.smooth, hγ.periodic, hγ.injective, hγ.regular, hγ.boundary⟩

 theorem RegularJordanParametrization.mem_frontier
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (t : ℝ) :
    γ t ∈ frontier (jordanInterior H) := by
  have he : γ (Int.fract t) = γ t := by
    simpa only [Int.fract, mul_one] using hγ.periodic.sub_int_mul_eq (x := t) ⌊t⌋
  rw [← he]
  exact hγ.boundary ▸ mem_image_of_mem γ
    (show Int.fract t ∈ Icc (0 : ℝ) 1 from ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩)

end CircleDomainRigidity

end

end OAI
