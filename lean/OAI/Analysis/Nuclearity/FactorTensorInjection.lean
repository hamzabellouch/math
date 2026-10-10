import OAI.Analysis.CharacterCriterion.FactorIndependence

namespace OAI

/-! Algebraic injectivity for commuting faithful factor restrictions. This
is the factor-representation step in Tomiyama's Theorem 5, specialized to
the product representation needed for tensor-ideal separation. -/

noncomputable section
open scoped TensorProduct BigOperators

namespace WeakPureInfiniteness

open KirchbergRordam.GenericRW

variable {A B H : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem factor_tensor_lift_injective (M : VonNeumannAlgebra H)
    (hM : FactorIndependence.IsFactor M)
    (φ : A →ₐ[ℂ] (H →L[ℂ] H)) (ψ : B →ₐ[ℂ] (H →L[ℂ] H))
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφM : ∀ a, φ a ∈ M) (hψM : ∀ b, ψ b ∈ M.commutant)
    (hc : ∀ a b, Commute (φ a) (ψ b)) :
    Function.Injective (Algebra.TensorProduct.lift φ ψ hc) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let b := Module.Free.chooseBasis ℂ B
  obtain ⟨a, rfl⟩ := TensorProduct.eq_repr_basis_right b z
  have hr : ∑ i ∈ a.support, φ (a i) * ψ (b i) = 0 := by
    simpa only [Finsupp.sum, map_sum, Algebra.TensorProduct.lift_tmul] using hz
  have hli : LinearIndependent ℂ (fun i : a.support => ψ (b i.val)) :=
    (b.linearIndependent.map' ψ.toLinearMap (LinearMap.ker_eq_bot.mpr hψ)).comp
      Subtype.val Subtype.val_injective
  have hrel : ∑ i : a.support, φ (a i.val) * ψ (b i.val) = 0 := by
    exact (Finset.sum_coe_sort a.support (fun i => φ (a i) * ψ (b i))).trans hr
  have hzero := FactorIndependence.relation_coefficients_zero M hM
    (fun i : a.support => φ (a i.val)) (fun i : a.support => ψ (b i.val))
    (fun i => hφM (a i.val)) (fun i => hψM (b i.val)) hli hrel
  change ∑ i ∈ a.support, a i ⊗ₜ[ℂ] b i = 0
  apply Finset.sum_eq_zero
  intro i hi
  have hi0 : a i = 0 := hφ (by simpa only [map_zero] using hzero ⟨i, hi⟩)
  rw [hi0, TensorProduct.zero_tmul]

end WeakPureInfiniteness

end

end OAI
