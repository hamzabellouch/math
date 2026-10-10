import OAI.Analysis.PureInfiniteness.NonunitalFunctionalRepresentation

namespace OAI

/-! The simultaneous representing operators lie in a genuine closed
commutant C*-algebra. This is the second tensor factor in KR02 7.18. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {D H : Type*} [CStarAlgebra D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def representationCommutant (π : D →⋆ₐ[ℂ] (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  StarSubalgebra.centralizer ℂ (Set.range π)

instance representationCommutant_closed (π : D →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    IsClosed (representationCommutant π : Set (H →L[ℂ] H)) :=
  Set.isClosed_centralizer _

instance representationCommutant_cstar (π : D →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    CStarAlgebra (representationCommutant π) :=
  StarSubalgebra.cstarAlgebra _

lemma mem_representationCommutant (π : D →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hc : ∀ a, Commute T (π a)) : T ∈ representationCommutant π := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  rintro _ ⟨a, rfl⟩
  refine ⟨(hc a).eq.symm, ?_⟩
  simpa only [map_star] using (hc (star a)).eq.symm

lemma representationCommutant_commute (π : D →⋆ₐ[ℂ] (H →L[ℂ] H))
    (a : D) (c : representationCommutant π) : Commute (π a) (c : H →L[ℂ] H) :=
  (StarSubalgebra.mem_centralizer_iff ℂ |>.mp c.property (π a) (Set.mem_range_self a)).1

lemma gns_vector_cyclic [PartialOrder D] [StarOrderedRing D] (f : D →ₚ[ℂ] ℂ) :
    DenseRange (fun a => f.gnsStarAlgHom a (Pureness.stateGNSVector f)) := by
  simp only [Pureness.stateGNS_apply_vector]
  exact UniformSpace.Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

variable {A I : Type*} [NonUnitalCStarAlgebra A] [Fintype I]

local instance commutantUnitizationOrder : PartialOrder (Unitization ℂ A) :=
  CStarAlgebra.spectralOrder _
local instance commutantUnitizationOrdered : StarOrderedRing (Unitization ℂ A) :=
  CStarAlgebra.spectralOrderedRing _

theorem finite_functionals_in_commutant (l : I → selfAdjoint A →L[ℝ] ℝ) :
    ∃ f : Unitization ℂ A →ₚ[ℂ] ℂ, f 1 = 1 ∧
      ∃ c : I → representationCommutant f.gnsStarAlgHom,
        (∀ i, IsSelfAdjoint (c i)) ∧
        ∀ i (a : selfAdjoint A), l i a =
          (⟪Pureness.stateGNSVector f,
            f.gnsStarAlgHom (a : Unitization ℂ A)
              ((c i : f.GNS →L[ℂ] f.GNS) (Pureness.stateGNSVector f))⟫_ℂ).re := by
  obtain ⟨f, hf, T, hT, hc, hv⟩ := finite_nonunital_functional_representation l
  let c (i : I) : representationCommutant f.gnsStarAlgHom :=
    ⟨T i, mem_representationCommutant f.gnsStarAlgHom (T i) (hc i)⟩
  refine ⟨f, hf, c, ?_, ?_⟩
  · intro i
    exact Subtype.ext (hT i)
  · intro i a
    rw [hv]
    have he := congrArg (fun S : f.GNS →L[ℂ] f.GNS => S (Pureness.stateGNSVector f)) (hc i (a : Unitization ℂ A)).eq
    exact congrArg (fun v => (⟪Pureness.stateGNSVector f, v⟫_ℂ).re) he

end WeakPureInfiniteness

end

end OAI
