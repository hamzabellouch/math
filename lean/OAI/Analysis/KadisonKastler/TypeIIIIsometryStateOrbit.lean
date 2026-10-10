import OAI.Analysis.KadisonKastler.TypeIIIPartialUnitaryExtension
import OAI.Analysis.KadisonKastler.FullCopyProjectionCut
import OAI.Analysis.KadisonKastler.ProjectionPinchedState
import OAI.Analysis.KadisonKastler.CornerStateConjugation

namespace OAI

/-! # Isometric state compressions are in the norm closure of the unitary orbit -/

namespace KadisonKastler
open Generator.Tracial
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.approximate_isometry_on_vector (hM : TypeIIIFactor M)
    (v : Algebra M) (hv : star v*v=1) (ξ : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : unitary (Algebra M), ‖u.val.val ξ-v.val ξ‖<ε := by
  obtain ⟨w,hw,hproper⟩ := hM.exists_proper_isometry
  have hInf := properlyInfiniteIdentity_of_proper_isometry hM.factor w hw hproper
  let oneP : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  have hfull : (centralSupport oneP).val=1 := by
    have he := le_centralSupport oneP
    change (centralSupport oneP).val*1=1 at he
    simpa only [mul_one] using he
  obtain ⟨C⟩ := exists_countable_projection_copies hInf oneP hfull
  obtain ⟨F,hF⟩ := C.exists_finiteCut_approx ξ (half_pos hε)
  let p := C.finiteCut F
  let z : PartialIsometry M := {
    support := p
    val := v*p.val
    initial := by
      rw [star_mul,p.property.isSelfAdjoint.star_eq]
      calc
        (p.val*star v)*(v*p.val)=p.val*(star v*v)*p.val := by simp only [mul_assoc]
        _ = p.val := by rw [hv,mul_one,p.property.isIdempotentElem.eq] }
  have htarget : z.target.val≠1 := by
    intro hz
    have he := congrArg (fun a : Algebra M => star v*a*v) hz
    change star v*((v*p.val)*star (v*p.val))*v=star v*1*v at he
    rw [star_mul,p.property.isSelfAdjoint.star_eq] at he
    have hh : star v*((v*p.val)*(p.val*star v))*v=p.val := by
      calc
        _ = (star v*v)*(p.val*p.val)*(star v*v) := by simp only [mul_assoc]
        _ = p.val := by rw [hv,one_mul,mul_one,p.property.isIdempotentElem.eq]
    rw [hh,mul_one,hv] at he
    exact C.finiteCut_ne_one F he
  obtain ⟨u,hu⟩ := hM.extend_partialIsometry z (C.finiteCut_ne_one F) htarget
  refine ⟨u,?_⟩
  have hb := unitary_isometry_error_of_agree v hv u p hu ξ
  change ‖ξ-p.val.val ξ‖<ε/2 at hF
  linarith

/-- The final unitary replacement needed after an isometric state comparison. -/
theorem TypeIIIFactor.unitary_state_close_to_isometry (hM : TypeIIIFactor M)
    (v : Algebra M) (hv : star v*v=1) (ξ : H) (hξ : ‖ξ‖=1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : unitary (Algebra M),
      ‖sandwichFunctional (vectorFunctional ξ) u.val-
        sandwichFunctional (vectorFunctional ξ) v‖<ε := by
  obtain ⟨u,hu⟩ := hM.approximate_isometry_on_vector v hv ξ
    (show 0 < ε/2 by positivity)
  refine ⟨u,?_⟩
  rw [sandwichFunctional_vectorFunctional,sandwichFunctional_vectorFunctional]
  have hn := vectorFunctional_norm_sub_le (M := M) (u.val.val ξ) (v.val ξ)
  have huNorm : ‖u.val.val ξ‖=‖ξ‖ := Unitary.norm_map (ambientAlgebraUnitary u) ξ
  have hvNorm : ‖v.val ξ‖=‖ξ‖ :=
    norm_apply_of_operator_isometry v.val (congrArg Subtype.val hv) ξ
  rw [huNorm,hvNorm,hξ] at hn
  linarith

end
end KadisonKastler

end OAI
