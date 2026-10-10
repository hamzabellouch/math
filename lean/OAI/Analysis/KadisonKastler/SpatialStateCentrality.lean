import OAI.Analysis.KadisonKastler.ProductBicentralizer

namespace OAI

/-! # State-central sequences in the first tensor leg

The product-state commutator is bounded by the original state commutator.
Thus bicentralizer membership of a first-leg operator implies membership
in the original algebra. Together with the independent-swap argument,
this is the needed product-leg specialization of AHHM, Proposition7.1.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def spatialLeftAlgebraHom (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    Algebra M →⋆ₐ[ℂ] Algebra (spatialProductAlgebra M D) :=
  (spatialLeft.comp M.toStarSubalgebra.subtype).codRestrict _
    (fun a => spatialLeft_mem_product M D a.property)

@[simp] theorem spatialLeftAlgebraHom_val (M : VonNeumannAlgebra H)
    (D : VonNeumannAlgebra K) (a : Algebra M) :
    (spatialLeftAlgebraHom M D a).val=spatialLeft (K := K) a.val := rfl

theorem spatialLeftAlgebraHom_tensorVector (M : VonNeumannAlgebra H)
    (D : VonNeumannAlgebra K) (a : Algebra M) (Ω : K) (ξ : H) :
    (spatialLeftAlgebraHom M D a).val (tensorVector Ω ξ)=tensorVector Ω (a.val ξ) :=
  congrArg (fun V : H →L[ℂ] SpatialHilbert H K => V ξ) (spatialLeft_tensorVector Ω a.val)

theorem tensorVectorSlice_mul_left (Ω : K) (a : H →L[ℂ] H)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :
    tensorVectorSlice Ω (spatialLeft a*T)=a*tensorVectorSlice Ω T := by
  ext ξ
  exact congrArg (fun V : SpatialHilbert H K →L[ℂ] H => V (T (tensorVector Ω ξ)))
    (tensorVector_adjoint_spatialLeft Ω a)

theorem tensorVectorSlice_mul_right (Ω : K) (a : H →L[ℂ] H)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :
    tensorVectorSlice Ω (T*spatialLeft a)=tensorVectorSlice Ω T*a := by
  ext ξ
  change (tensorVector Ω).adjoint (T (spatialLeft a (tensorVector Ω ξ)))=
    (tensorVector Ω).adjoint (T (tensorVector Ω (a ξ)))
  rw [show spatialLeft a (tensorVector Ω ξ)=tensorVector Ω (a ξ) from
    congrArg (fun V : H →L[ℂ] SpatialHilbert H K => V ξ) (spatialLeft_tensorVector Ω a)]

theorem spatialLeft_stateCommutator_apply (M : VonNeumannAlgebra H)
    (D : VonNeumannAlgebra K) (ξ : H) (Ω : K) (a : Algebra M)
    (b : Algebra (spatialProductAlgebra M D)) :
    vectorStateCommutator (tensorVector Ω ξ) (spatialLeftAlgebraHom M D a) b=
      vectorStateCommutator ξ a
        ⟨tensorVectorSlice Ω b.val,tensorVectorSlice_mem M D Ω b.val b.property⟩ := by
  simp only [vectorStateCommutator_apply,vectorFunctional_apply,AddSubgroupClass.coe_sub,
    MulMemClass.coe_mul,spatialLeftAlgebraHom_val]
  rw [← tensorVectorSlice_mul_left,← tensorVectorSlice_mul_right,← map_sub]
  exact ((tensorVector Ω).adjoint_inner_right ξ _).symm

theorem spatialLeft_stateCommutator_norm_le (M : VonNeumannAlgebra H)
    (D : VonNeumannAlgebra K) (ξ : H) (Ω : K) (hΩ : ‖Ω‖=1) (a : Algebra M) :
    ‖vectorStateCommutator (tensorVector Ω ξ) (spatialLeftAlgebraHom M D a)‖ ≤
      ‖vectorStateCommutator ξ a‖ := by
  apply (vectorStateCommutator (tensorVector Ω ξ) (spatialLeftAlgebraHom M D a)).opNorm_le_bound
    (norm_nonneg (vectorStateCommutator ξ a))
  intro b
  rw [spatialLeft_stateCommutator_apply]
  let c : Algebra M := ⟨tensorVectorSlice Ω b.val,tensorVectorSlice_mem M D Ω b.val b.property⟩
  have hc : ‖c‖ ≤ ‖b‖ := norm_tensorVectorSlice_le Ω hΩ b.val
  exact ((vectorStateCommutator ξ a).le_opNorm c).trans
    (mul_le_mul_of_nonneg_left hc (norm_nonneg (vectorStateCommutator ξ a)))

theorem stateBicentralizerMember_spatialLeft_pullback (M : VonNeumannAlgebra H)
    (D : VonNeumannAlgebra K) (ξ : H) (Ω : K) (hΩ : ‖Ω‖=1) (a : Algebra M)
    (ha : stateBicentralizerMember (tensorVector Ω ξ) (spatialLeftAlgebraHom M D a)) :
    stateBicentralizerMember ξ a := by
  apply (stateBicentralizerMember_iff_unitary_tests ξ a).mpr
  intro u hu η
  let L := spatialLeftAlgebraHom M D
  let v (n : ℕ) : unitary (Algebra (spatialProductAlgebra M D)) :=
    Unitary.map (StarMonoidHom.ofClass L) (u n)
  have hv : Tendsto (fun n => ‖vectorStateCommutator (tensorVector Ω ξ) (v n).val‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun n => spatialLeft_stateCommutator_norm_le M D ξ Ω hΩ (u n).val) hu
  have ht := ((stateBicentralizerMember_iff_unitary_tests _ _).mp ha v hv
    (tensorVector Ω η)).norm
  have he (n : ℕ) :
      ‖(L a*(v n).val-(v n).val*L a).val (tensorVector Ω η)‖=
        ‖(a*(u n).val-(u n).val*a).val η‖ := by
    change ‖(L a*L (u n).val-L (u n).val*L a).val (tensorVector Ω η)‖=_
    rw [← map_mul L,← map_mul L,← map_sub L]
    rw [spatialLeftAlgebraHom_tensorVector,norm_tensorVector_apply,hΩ,mul_one]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  change Tendsto (fun n => ‖(L a*(v n).val-(v n).val*L a).val (tensorVector Ω η)‖)
    atTop (𝓝 ‖(0 : SpatialHilbert H K)‖) at ht
  simpa only [he,norm_zero] using ht

theorem spatial_bicentralizer_mem_left_bicentralizer
    (hK : PublishedKaplanskyDensity.{u}) (M : VonNeumannAlgebra H)
    (P : ProductMatrixStages (H := K)) (ξ : H)
    (a : Algebra (spatialProductAlgebra M P.algebra))
    (ha : stateBicentralizerMember (tensorVector P.vector ξ) a) :
    ∃ b : Algebra M, stateBicentralizerMember ξ b ∧ a.val=spatialLeft (K := K) b.val := by
  obtain ⟨b,hb⟩ := spatial_bicentralizer_mem_left hK M P ξ a ha
  refine ⟨b,?_,hb⟩
  apply stateBicentralizerMember_spatialLeft_pullback M P.algebra ξ P.vector P.unit_vector b
  have he : spatialLeftAlgebraHom M P.algebra b=a := Subtype.ext hb.symm
  rwa [he]

end

end KadisonKastler

end OAI
