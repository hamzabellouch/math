import OAI.Analysis.KadisonKastler.TypeIIICyclicSeparating
import OAI.Analysis.KadisonKastler.IsometricStateBicentralizer

namespace OAI

/-! # A separating state has a cyclic vector in the same type III representation -/

namespace KadisonKastler
open Generator Generator.Tracial
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem TypeIIIFactor.exists_cyclic_vector_same_state
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    {M : VonNeumannAlgebra H} (hM : TypeIIIFactor M) (ξ : H) (hξ : ‖ξ‖=1)
    (hs : Function.Injective (algebraVectorMap M ξ)) :
    ∃ Ω : H, ‖Ω‖=1 ∧ DenseRange (algebraVectorMap M Ω) ∧
      Function.Injective (algebraVectorMap M Ω) ∧
      vectorFunctional (M := M) Ω=vectorFunctional ξ := by
  obtain ⟨v,hv,hproper⟩ := hM.exists_proper_isometry
  let q : AlgebraProjection M.commutant :=
    ⟨⟨(cyclicOrbitSpace M ξ).starProjection,cyclicOrbitProjection_mem M ξ⟩,
      ⟨Subtype.ext (Submodule.isIdempotentElem_starProjection _).eq,
        Subtype.ext (isSelfAdjoint_starProjection _).star_eq⟩⟩
  have hq : ¬ FiniteProjectionIn M.commutant q.val :=
    cyclicOrbitProjection_not_finite M ξ hs v hv hproper
  have he := projection_equivalent_one_of_not_finite
    (scalarCenter_commutant M hM.factor) q hq
  obtain ⟨u,hu,hut⟩ := AlgebraProjection.equivalent_symm he
  let w : Algebra M.commutant := u.val
  have hw : star w * w = 1 := u.initial.trans (congrArg Subtype.val hu)
  have hwq : w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val := by
    have ht : w * star w = q.val := congrArg Subtype.val hut
    have ht' := congrArg Subtype.val ht
    change w.val * star w.val = (cyclicOrbitSpace M ξ).starProjection at ht'
    simpa only [vectorSupportProjection,VonNeumannAlgebra.commutant_commutant,
      cyclicOrbitSpace] using ht'
  have hp : (vectorSupportProjection M ξ).val = 1 := by
    apply hs
    change (vectorSupportProjection M ξ).val.val ξ = (1 : H →L[ℂ] H) ξ
    exact (vectorSupportProjection_apply M ξ).trans (one_apply_eq_self ξ).symm
  have hp' : (1 : H →L[ℂ] H) * star 1 = (vectorSupportProjection M ξ).val.val := by
    simp only [star_one,mul_one,hp,OneMemClass.coe_one]
  let Ω := star ((1 : Algebra M).val * w.val) ξ
  have hcyc : DenseRange (algebraVectorMap M Ω) :=
    support_transfer_cyclic M ξ 1 w hw hwq (by simp)
  have hsep : Function.Injective (algebraVectorMap M Ω) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply support_transfer_separating M ξ 1 w (by simp) hp'
      (by rw [hwq,vectorSupportProjection_apply]) (a-b)
    change a.val Ω - b.val Ω = 0
    exact sub_eq_zero.mpr hab
  have hn := support_transfer_norm M ξ 1 w (by simp) hw hp' hwq
  have hfix : w.val Ω=ξ := by
    change w.val (star ((1 : Algebra M).val*w.val) ξ)=ξ
    simp only [OneMemClass.coe_one,one_mul,← mul_apply_eq_comp,hwq,
      vectorSupportProjection_apply]
  have hstate : vectorFunctional (M := M) Ω=vectorFunctional ξ := by
    ext a
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp w.property a.val a.property
    have he : w.val (a.val Ω)=a.val ξ := by
      change (w.val*a.val) Ω=a.val ξ
      rw [← hc,mul_apply_eq_comp,hfix]
    change inner ℂ Ω (a.val Ω)=inner ℂ ξ (a.val ξ)
    have hi (x y : H) : inner ℂ (w.val x) (w.val y)=inner ℂ x y := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
      change inner ℂ x ((star w.val*w.val) y)=inner ℂ x y
      rw [show star w.val*w.val=1 from congrArg Subtype.val hw,one_apply_eq_self]
    rw [← hi Ω (a.val Ω),hfix,he]
  exact ⟨Ω,hn.trans hξ,hcyc,hsep,hstate⟩


end
end KadisonKastler

end OAI
