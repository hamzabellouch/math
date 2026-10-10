import OAI.NumberTheory.Ostmann.Characters.PolynomialKernelCoordinates

namespace OAI

/-! # Linear maps for the concrete finite kernel blocks -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def centeredSupportLinearMap {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) where
  toFun := centeredSupportProjection S
  map_add' f g := by
    funext x
    unfold centeredSupportProjection finiteSupportMean
    simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
    split_ifs <;> ring
  map_smul' c f := by
    funext x
    change centeredSupportProjection S (fun x => c * f x) x = c * centeredSupportProjection S f x
    rw [centeredSupportProjection_const_mul]

noncomputable def rawKernelLinearMap {p : ℕ} [NeZero p]
    (k : ZMod p → ℂ) : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) where
  toFun := rawAdditiveKernelAction k
  map_add' f g := rawAdditiveKernelAction_add_input k f g
  map_smul' c f := by
    funext x
    change (∑ y, (c * f y) * k (x - y)) = c * ∑ y, f y * k (x - y)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring

noncomputable def residueLowerLinearMap {p : ℕ} [NeZero p]
    (S T : Finset (ZMod p)) (k : ZMod p → ℂ) : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) :=
  (centeredSupportLinearMap S).comp ((rawKernelLinearMap k).comp (centeredSupportLinearMap T))

noncomputable def polydiscLowerLinearMap {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (c d : ℂ) : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) :=
  c • residueLowerLinearMap S T (localSparseKernel E) +
    d • residueLowerLinearMap S T (localSparseSquare E)

theorem polydiscLowerLinearMap_apply {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (c d : ℂ) (f : ZMod p → ℂ) :
    polydiscLowerLinearMap S T E c d f = polydiscSparseLower S T E c d f := rfl

theorem residuePointVector_expansion {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    f = ∑ y, f y • residuePointVector y := by
  funext x
  simp [residuePointVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem finiteLinearMap_point_expansion {p : ℕ} [NeZero p]
    (L : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ)) (f : ZMod p → ℂ) (x : ZMod p) :
    L f x = ∑ y, L (residuePointVector y) x * f y := by
  have he := congrArg (fun g : ZMod p → ℂ => L g x) (residuePointVector_expansion f)
  rw [map_sum] at he
  simpa only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using he

end Ostmann

end OAI
