import OAI.Analysis.KadisonKastler.CuntzChangeOfBasis
import OAI.Analysis.KadisonKastler.RelativeMatrixFactorEquiv
import OAI.Analysis.KadisonKastler.ConcreteUCP

namespace OAI

/-! # Spatially identifying a type III factor with its matrix relative algebra

The isometry onto one matrix corner gives a finite Cuntz family in the
factor. Its conjugate family lies in the commutant. Changing between the
two families spatially implements the corner-amplification isomorphism.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι] {M : VonNeumannAlgebra H}

private def cornerIsometryFamily (E : MatrixUnitSystem ι (Algebra M)) (o : ι)
    (v : Algebra M) (hv : star v*v=1) (hp : v*star v=E.entry o o) : CuntzFamily ι H where
  entry i := (E.entry i o*v).val
  orthogonal i j := by
    change star (M.toStarSubalgebra.subtype (E.entry i o*v))*
      M.toStarSubalgebra.subtype (E.entry j o*v) = _
    simp only [map_mul]
    have he : star (E.entry i o*v)*(E.entry j o*v)=if i=j then 1 else 0 := by
      rw [star_mul,E.star_entry]
      calc
        _ = star v*(E.entry o i*E.entry j o)*v := by simp only [mul_assoc]
        _ = _ := by
          rw [E.mul_entry]
          split_ifs with h
          · rw [← hp]
            calc
              _ = (star v*v)*(star v*v) := by simp only [mul_assoc]
              _ = 1 := by rw [hv,one_mul]
          · simp
    simpa only [map_mul,map_star,apply_ite,map_one,map_zero] using
      congrArg M.toStarSubalgebra.subtype he
  total := by
    have he (i : ι) : (E.entry i o*v)*star (E.entry i o*v)=E.entry i i := by
      rw [star_mul,E.star_entry]
      calc
        _ = E.entry i o*(v*star v)*E.entry o i := by simp only [mul_assoc]
        _ = E.entry i i := by
          rw [hp,E.mul_entry,ite_eq_left rfl,E.mul_entry,ite_eq_left rfl]
    change (∑ i, M.toStarSubalgebra.subtype ((E.entry i o*v)*star (E.entry i o*v)))=1
    simp only [he,← map_sum,E.total,map_one]

theorem TypeIIIFactor.exists_relative_matrix_spatial_equiv
    [TopologicalSpace.SeparableSpace H] (hM : TypeIIIFactor M) (E : FiniteMatrixStage M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant) :
    ∃ (e : Algebra M ≃⋆ₐ[ℂ] Algebra E.units.relativeVonNeumann)
      (u : unitary (H →L[ℂ] H)), ∀ a : Algebra M, unitaryConj u a.val=(e a).val := by
  let : Nontrivial (Algebra M) := nontrivial_of_ne (1 : Algebra M) 0
    (fun h => hM.nonzero (congrArg Subtype.val h))
  let o : Fin E.size := ⟨0,E.positive⟩
  have hpo : IsStarProjection (E.units.entry o o) := ⟨by
    change E.units.entry o o*E.units.entry o o=E.units.entry o o
    rw [E.units.mul_entry,ite_eq_left rfl],by rw [IsSelfAdjoint,E.units.star_entry]⟩
  obtain ⟨v,hv,hp⟩ := hM.exists_isometry_onto_projection (E.units.entry o o) hpo
    (E.units.diagonal_ne_zero o)
  let S := cornerIsometryFamily E.units o v hv hp
  let T := S.conjugate J hJ
  let u := S.changeBasis T
  let e := (E.units.isometricCommutantEquiv o v hv hp).trans E.units.relativeEquiv
  have hcomm (a : Algebra M) (i : Fin E.size) : Commute a.val (T.entry i) := by
    exact VonNeumannAlgebra.mem_commutant_iff.mp (hright (E.units.entry i o*v))
      a.val a.property
  have he (a : Algebra M) : unitaryConj u a.val=(e a).val := by
    rw [S.changeBasis_conjugate T a.val (hcomm a)]
    change (∑ i, (E.units.entry i o*v).val*a.val*star (E.units.entry i o*v).val) =
      M.toStarSubalgebra.subtype (E.units.amplify o (v*a*star v))
    simp only [MatrixUnitSystem.amplify,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change ((E.units.entry i o*v)*a*star (E.units.entry i o*v)).val =
      (E.units.entry i o*(v*a*star v)*E.units.entry o i).val
    congr 1
    rw [star_mul,E.units.star_entry]
    simp only [mul_assoc]
  exact ⟨e,u,he⟩

theorem TypeIIIFactor.exists_relative_matrix_spatial
    [TopologicalSpace.SeparableSpace H] (hM : TypeIIIFactor M) (E : FiniteMatrixStage M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M E.units.relativeVonNeumann := by
  obtain ⟨e,u,he⟩ := hM.exists_relative_matrix_spatial_equiv E J hJ hright
  exact ⟨u,conjugates_of_starEquiv e u he⟩

end

end KadisonKastler

end OAI
