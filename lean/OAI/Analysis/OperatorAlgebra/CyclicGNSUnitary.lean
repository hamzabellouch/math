import OAI.Analysis.OperatorAlgebra.CyclicStateNorm

namespace OAI

/-! The concrete cyclic vector realization of a positive functional is
unitarily equivalent to its GNS space. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder
open UniformSpace

namespace WeakPureInfiniteness

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (φ : A →ₚ[ℂ] ℂ) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hφ : ∀ a, φ a = inner ℂ ξ (π a ξ))

def cyclicPreGNSIsometry : φ.PreGNS →ₗᵢ[ℂ] H where
  toFun x := π (φ.ofPreGNS x) ξ
  map_add' x y := by simp only [map_add, add_apply]
  map_smul' c x := by simp only [map_smul, smul_apply, RingHom.id_apply]
  norm_map' x := by
    change ‖π (φ.ofPreGNS x) ξ‖ = ‖x‖
    have h := cyclic_vector_norm_eq_preGNS π (StarAlgHom.id ℂ A) φ ξ
      (fun a => hφ a) (φ.ofPreGNS x)
    change ‖π (φ.ofPreGNS x) ξ‖ = ‖φ.toPreGNS (φ.ofPreGNS x)‖ at h
    simpa only [PositiveLinearMap.toPreGNS_ofPreGNS] using h

def cyclicGNSIsometry : φ.GNS →ₗᵢ[ℂ] H :=
  (cyclicPreGNSIsometry φ π ξ hφ).fromCompletion

@[simp] lemma cyclicGNSIsometry_coe (x : φ.PreGNS) :
    cyclicGNSIsometry φ π ξ hφ (x : φ.GNS) = π (φ.ofPreGNS x) ξ := by
  rw [cyclicGNSIsometry, LinearIsometry.fromCompletion_apply_coe]
  rfl

@[simp] lemma cyclicGNSIsometry_vector (a : A) :
    cyclicGNSIsometry φ π ξ hφ (φ.toPreGNS a : φ.GNS) = π a ξ := by
  rw [cyclicGNSIsometry_coe, PositiveLinearMap.ofPreGNS_toPreGNS]

theorem cyclicGNSIsometry_surjective (hξ : DenseRange (fun a => π a ξ)) :
    Function.Surjective (cyclicGNSIsometry φ π ξ hφ) := by
  let V := cyclicGNSIsometry φ π ξ hφ
  have hc : IsClosed (Set.range V) := V.isometry.isClosedEmbedding.isClosed_range
  have hr : Set.range (fun a => π a ξ) ⊆ Set.range V := by
    rintro _ ⟨a, rfl⟩
    exact ⟨(φ.toPreGNS a : φ.GNS), cyclicGNSIsometry_vector φ π ξ hφ a⟩
  have hall : Set.univ ⊆ Set.range V := by
    rw [← hξ.closure_range]
    exact closure_minimal hr hc
  intro x
  exact hall (Set.mem_univ x)

def cyclicGNSUnitary (hξ : DenseRange (fun a => π a ξ)) : φ.GNS ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (cyclicGNSIsometry φ π ξ hφ)
    (cyclicGNSIsometry_surjective φ π ξ hφ hξ)

theorem cyclicGNSIsometry_intertwines (a : A) (η : φ.GNS) :
    cyclicGNSIsometry φ π ξ hφ (φ.gnsStarAlgHom a η) =
      π a (cyclicGNSIsometry φ π ξ hφ η) := by
  induction η using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    change cyclicGNSIsometry φ π ξ hφ (φ.gnsNonUnitalStarAlgHom a x) = _
    rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,
      cyclicGNSIsometry_coe, cyclicGNSIsometry_coe]
    simp only [PositiveLinearMap.leftMulMapPreGNS_apply,
      PositiveLinearMap.ofPreGNS_toPreGNS, map_mul, mul_apply_eq_comp]

theorem cyclicGNSUnitary_conjugates (hξ : DenseRange (fun a => π a ξ)) (a : A) :
    (cyclicGNSUnitary φ π ξ hφ hξ).conjStarAlgEquiv (φ.gnsStarAlgHom a) = π a := by
  ext η
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change cyclicGNSIsometry φ π ξ hφ
    (φ.gnsStarAlgHom a ((cyclicGNSUnitary φ π ξ hφ hξ).symm η)) = π a η
  rw [cyclicGNSIsometry_intertwines]
  change π a ((cyclicGNSUnitary φ π ξ hφ hξ)
    ((cyclicGNSUnitary φ π ξ hφ hξ).symm η)) = π a η
  rw [LinearIsometryEquiv.apply_symm_apply]

end WeakPureInfiniteness

end

end OAI
