import Mathlib
import OAI.Analysis.FreeWords.FactorCorners
import OAI.Analysis.FreeWords.PartialIsoChain
import OAI.Analysis.FreeWords.PartialIsoResidual
import OAI.Analysis.FreeWords.PolarBounds

namespace OAI

noncomputable section

namespace KKProjectionSupport

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem concrete_projection_coe {M : VonNeumannAlgebra H} {p : ConcreteAlgebra M}
    (hp : IsStarProjection p) : IsStarProjection (p : H →L[ℂ] H) :=
  ⟨congrArg Subtype.val hp.1, congrArg Subtype.val hp.2⟩

theorem exists_maximal_concrete_partialIso (M : VonNeumannAlgebra H)
    (p q : ConcreteAlgebra M) : ∃ v : PartialIso (ConcreteAlgebra M),
      Maximal (fun v : PartialIso (ConcreteAlgebra M) => v.value*p=v.value ∧ q*v.value=v.value) v := by
  obtain ⟨V,hV⟩ := exists_maximal_partialIso M (p : H →L[ℂ] H) (q : H →L[ℂ] H)
  let v : PartialIso (ConcreteAlgebra M) :=
    ⟨⟨V.value,hV.1.1⟩, by apply Subtype.ext; exact V.isPartial⟩
  refine ⟨v, ⟨Subtype.ext hV.1.2.1, Subtype.ext hV.1.2.2⟩, ?_⟩
  intro w hw hvw
  let W : PartialIso (H →L[ℂ] H) :=
    ⟨(w.value : H →L[ℂ] H), congrArg Subtype.val w.isPartial⟩
  have hW : W.value ∈ M ∧ W.value*(p : H →L[ℂ] H)=W.value ∧ (q : H →L[ℂ] H)*W.value=W.value :=
    ⟨w.value.property, congrArg Subtype.val hw.1, congrArg Subtype.val hw.2⟩
  have hVW : V ≤ W := ⟨congrArg Subtype.val hvw.1, congrArg Subtype.val hvw.2⟩
  have hWV := hV.2 hW hVW
  exact ⟨Subtype.ext hWV.1, Subtype.ext hWV.2⟩

theorem factor_partial_in_corner {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (hM : IsFactor M) {p q : ConcreteAlgebra M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    ∃ v : ConcreteAlgebra M, Partial v ∧ v*p=v ∧ q*v=v ∧ v ≠ 0 := by
  obtain ⟨a,ha⟩ := factor_nonzero_corner τ hM hp hp0 hq0
  let b : ConcreteAlgebra M := q*a*p
  have hbp : b*p=b := by dsimp [b]; rw [mul_assoc, hp.isIdempotentElem.eq]
  have hqb : q*b=b := by dsimp [b]; rw [← mul_assoc, ← mul_assoc, hq.isIdempotentElem.eq]
  obtain ⟨v,hvM,hv,hvp,hqv,hv0⟩ := KKPolarSupport.polar_decomposition_bounds M
    (b : H →L[ℂ] H) b.property (p : H →L[ℂ] H) (q : H →L[ℂ] H)
    (concrete_projection_coe hp) (concrete_projection_coe hq)
    (congrArg Subtype.val hbp) (congrArg Subtype.val hqb)
  refine ⟨⟨v,hvM⟩, Subtype.ext hv, Subtype.ext hvp, Subtype.ext hqv, ?_⟩
  intro h0
  exact ha (Subtype.ext (hv0 (congrArg Subtype.val h0)))

theorem projection_comparable_by_trace (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M) (hM : IsFactor M) (p q : ConcreteAlgebra M)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ v : ConcreteAlgebra M, Partial v ∧ v*p=v ∧ q*v=v ∧
      (star v*v=p ∨ v*star v=q) := by
  obtain ⟨V,hV⟩ := exists_maximal_concrete_partialIso M p q
  let v : ConcreteAlgebra M := V.value
  have hv : Partial v := V.isPartial
  have hvp : v*p=v := hV.1.1
  have hqv : q*v=v := hV.1.2
  have hpi := initial_bound hp hvp
  have hqi := final_bound hq hqv
  have hpr := projection_sub hp (partial_initial hv) hpi.1
  have hqr := projection_sub hq (partial_final hv) hqi.1
  refine ⟨v,hv,hvp,hqv,?_⟩
  by_contra! hne
  have hp0 : p-star v*v ≠ 0 := fun h => hne.1 (sub_eq_zero.mp h).symm
  have hq0 : q-v*star v ≠ 0 := fun h => hne.2 (sub_eq_zero.mp h).symm
  obtain ⟨w,hw,hwp,hqw,hw0⟩ := factor_partial_in_corner τ hM hpr hqr hp0 hq0
  have hcross := orthogonal_of_residual hv hp hq hvp hqv hwp hqw
  have hsum := partial_add_orthogonal hv hw hcross.1 hcross.2
  have hwp' : w*p=w := by
    calc
      w*p = (w*(p-star v*v))*p := by rw [hwp]
      _ = w*((p-star v*v)*p) := mul_assoc _ _ _
      _ = w*(p-star v*v) := by rw [sub_mul, hp.isIdempotentElem.eq, hpi.1]
      _ = w := hwp
  have hqw' : q*w=w := by
    calc
      q*w = q*((q-v*star v)*w) := by rw [hqw]
      _ = (q*(q-v*star v))*w := (mul_assoc _ _ _).symm
      _ = (q-v*star v)*w := by rw [mul_sub, hq.isIdempotentElem.eq, hqi.2]
      _ = w := hqw
  let W : PartialIso (ConcreteAlgebra M) := ⟨v+w,hsum.1⟩
  have hW : W.value*p=W.value ∧ q*W.value=W.value := by
    exact ⟨by change (v+w)*p=v+w; rw [add_mul,hvp,hwp'],
      by change q*(v+w)=v+w; rw [mul_add,hqv,hqw']⟩
  have he : V=W := hV.eq_of_le hW hsum.2
  have he' : v=v+w := congrArg PartialIso.value he
  exact hw0 (add_left_cancel (show v+w=v+0 by rw [← he',add_zero]))

theorem projection_equivalent_of_trace (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M) (hM : IsFactor M) (p q : ConcreteAlgebra M)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hτ : τ.map p = τ.map q) :
    ∃ v : ConcreteAlgebra M, star v*v = p ∧ v*star v = q := by
  obtain ⟨v,hv,hvp,hqv,he⟩ := projection_comparable_by_trace M τ hM p q hp hq
  have hpr := projection_sub hp (partial_initial hv) (initial_bound hp hvp).1
  have hqr := projection_sub hq (partial_final hv) (final_bound hq hqv).1
  have hτr : τ.map (p-star v*v)=τ.map (q-v*star v) := by
    rw [map_sub,map_sub,hτ,τ.tracial]
  have hzero {e : ConcreteAlgebra M} (he : IsStarProjection e) (ht : τ.map e=0) : e=0 := by
    by_contra hz
    exact trace_projection_ne_zero τ he hz ht
  rcases he with he | he
  · have ht : τ.map (q-v*star v)=0 := by rw [← hτr,he,sub_self,map_zero]
    exact ⟨v,he,(sub_eq_zero.mp (hzero hqr ht)).symm⟩
  · have ht : τ.map (p-star v*v)=0 := by rw [hτr,he,sub_self,map_zero]
    exact ⟨v,(sub_eq_zero.mp (hzero hpr ht)).symm,he⟩

end

end KKProjectionSupport
end

end OAI
