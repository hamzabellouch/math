import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeGroup
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualConjugation

namespace OAI

/-! # The actual Cartan automorphisms preserve the cone ideal -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

theorem map_mixedWordIdeal_mem {I L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤)
    (F : L →ₗ⁅ℝ⁆ L) (J : LieIdeal ℝ L)
    (hout : ∀ i, outside i → F (X i) ∈ J)
    (v : L) (hv : v ∈ mixedWordIdeal X outside hgen) : F v ∈ J := by
  change F v ∈ J.toSubmodule
  change v ∈ mixedWordSpan X outside at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [evalBracketWord_map]
    exact eval_mixed_mem_ideal (fun i => F (X i)) outside J hout w hw
  | zero => simpa only [map_zero] using J.toSubmodule.zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using J.add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using J.smul_mem r hx

/-- In finite dimension an invariant subspace is also invariant under the
inverse automorphism. -/
theorem mem_submodule_equiv_iff_of_invariant
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (J : Submodule ℝ V) (e : V ≃ₗ[ℝ] V) (he : ∀ v ∈ J, e v ∈ J) (v : V) :
    e v ∈ J ↔ v ∈ J := by
  let f : J →ₗ[ℝ] J := (e.toLinearMap.comp J.subtype).codRestrict J (fun x => he x x.property)
  have hf : Function.Injective f := fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := (LinearMap.injective_iff_surjective).mp hf
  refine ⟨fun hv => ?_, he v⟩
  obtain ⟨x, hx⟩ := hsurj ⟨e v, hv⟩
  have hx' : e x = e v := congrArg Subtype.val hx
  exact e.injective hx' ▸ x.property

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

theorem coneWordIdeal_adjoint_mem
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (h : H) (v : cartanRootIdeal H) (hv : v ∈ M.coneWordIdeal C) :
    cartanIdealAdjointAutomorphism T H h v ∈ M.coneWordIdeal C := by
  apply map_mixedWordIdeal_mem M.letter
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates
    (cartanIdealAdjointAutomorphism T H h).toLieHom (M.coneWordIdeal C) ?_ v hv
  intro i hi
  have hr := cartanIdealResidualAutomorphism_root_mem T H h (M.weight i)
    (M.letter i) (M.letter_root i)
  have he : cartanIdealAdjointAutomorphism T H h (M.letter i) =
      Real.exp (M.weight i h) • cartanIdealResidualAutomorphism T H h (M.letter i) := by
    apply Subtype.ext
    exact cartanWeightScale_apply_root T H h (M.weight i) hr
  apply M.outside_genWeightSpace_le_coneWordIdeal C hadd (M.weight i) hi
  let ι : cartanRootIdeal H →ₗ⁅ℝ,H⁆ L := ((cartanRootIdeal H).restr H).incl
  rw [← comap_genWeightSpace_eq_of_injective (f := ι)
    ((cartanRootIdeal H).restr H).injective_incl]
  change (cartanIdealAdjointAutomorphism T H h (M.letter i) : L) ∈ rootSpace H (M.weight i)
  rw [he]
  exact (rootSpace H (M.weight i)).smul_mem _ hr

theorem coneWordIdeal_adjoint_mem_iff
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (h : H) (v : cartanRootIdeal H) :
    cartanIdealAdjointAutomorphism T H h v ∈ M.coneWordIdeal C ↔ v ∈ M.coneWordIdeal C :=
  mem_submodule_equiv_iff_of_invariant (M.coneWordIdeal C).toSubmodule
    (cartanIdealAdjointAutomorphism T H h).toLinearEquiv
    (M.coneWordIdeal_adjoint_mem T C hadd h) v

end CartanWordModel
end PolycyclicRecognition

end

end OAI
