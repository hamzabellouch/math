import OAI.Analysis.KadisonKastler.ConjugationFunctionalCalculus
import OAI.Analysis.KadisonKastler.PublishedSimpleDerivation

namespace OAI

/-! # Simplicity under Hilbert conjugation

A conjugate-linear Hilbert involution gives an isometric ring equivalence on
its concrete algebra image. Closed two-sided ideals therefore correspond.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def conjugateAlgebraRingEquiv (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (M : VonNeumannAlgebra H) :
    Algebra M ≃+* Algebra (conjugateRightAlgebra J hJ M) where
  toFun a := ⟨conjugationOperator J a, a,a.property,rfl⟩
  invFun a := ⟨conjugationOperator J a,by
    rcases a.property with ⟨b,hb,hba⟩
    rw [← hba,conjugationOperator_twice J hJ]
    exact hb⟩
  left_inv a := Subtype.ext (conjugationOperator_twice J hJ a)
  right_inv a := Subtype.ext (conjugationOperator_twice J hJ a)
  map_mul' a b := Subtype.ext (conjugationOperator_mul J hJ a b)
  map_add' a b := Subtype.ext (conjugationOperator_add J a b)

theorem conjugateAlgebraRingEquiv_isometry (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (M : VonNeumannAlgebra H) :
    Isometry (conjugateAlgebraRingEquiv J hJ M) := by
  apply Isometry.of_dist_eq
  intro a b
  change dist (conjugationOperator J a) (conjugationOperator J b)=dist a.val b.val
  exact (conjugationRealStarAlgEquiv_isometry J hJ).dist_eq a b

theorem cstarSimple_conjugateAlgebra (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (M : VonNeumannAlgebra H)
    (hM : CStarSimple (Algebra M)) :
    CStarSimple (Algebra (conjugateRightAlgebra J hJ M)) := by
  let e := conjugateAlgebraRingEquiv J hJ M
  intro I hI
  let K := I.comap e.toRingHom
  have hKeq : (K : Set (Algebra M)) = e ⁻¹' (I : Set _) := by
    ext a
    exact TwoSidedIdeal.mem_comap (f:=e.toRingHom)
  have hK : IsClosed (K : Set (Algebra M)) := by
    rw [hKeq]
    exact hI.preimage (conjugateAlgebraRingEquiv_isometry J hJ M).continuous
  rcases hM K hK with hb | ht
  · left
    apply le_antisymm _ bot_le
    intro a ha
    have hmem : e.symm a ∈ K := by
      apply (TwoSidedIdeal.mem_comap (f:=e.toRingHom)).mpr
      change e (e.symm a) ∈ I
      rwa [e.apply_symm_apply]
    rw [hb,TwoSidedIdeal.mem_bot] at hmem
    have he : a=0 := by
      calc
        a = e (e.symm a) := (e.apply_symm_apply a).symm
        _ = 0 := by rw [hmem,map_zero]
    simpa only [TwoSidedIdeal.mem_bot] using he
  · right
    apply I.eq_top
    have hmem : (1 : Algebra M) ∈ K := by rw [ht]; exact Set.mem_univ _
    have hm : e 1 ∈ I := (TwoSidedIdeal.mem_comap (f:=e.toRingHom)).mp hmem
    simpa only [map_one] using hm

end

end KadisonKastler

end OAI
