import OAI.Analysis.GroupDeterminants.ComplexRepresentation

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section RegularStar
variable {G : Type} [Group G] {n : ℕ}

theorem complexOperator_smul (z : ℂ)
    (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    complexOperator (z • A) = z • complexOperator A := by
  classical
  unfold complexOperator
  simp only [Matrix.smul_apply, MonoidAlgebra.coeff_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finsupp.sum_smul_index (fun g => zero_smul ℂ (elementaryOperator i j g)),
    Finsupp.smul_sum]
  simp only [smul_smul]

def complexAlgebraRepresentation : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G) →ₐ[ℂ]
    (Hilbert G n →L[ℂ] Hilbert G n) :=
  AlgHom.ofLinearMap
    { toFun := complexOperator
      map_add' := complexOperator_add
      map_smul' := complexOperator_smul }
    complexOperator_one complexOperator_mul

theorem elementaryOperator_star (i j : Fin n) (g : G) :
    star (elementaryOperator i j g) = elementaryOperator j i g⁻¹ := by
  classical
  rw [eq_comm, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.eq_adjoint_iff]
  intro ξ η
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  let e : Fin n × G ≃ Fin n × G :=
    Equiv.prodCongr (Equiv.swap i j) (Equiv.mulLeft g)
  rw [← e.tsum_eq (fun a => inner ℂ (ξ a) (elementaryOperator i j g η a))]
  apply tsum_congr
  rintro ⟨a, h⟩
  simp only [elementaryOperator_apply, e, Equiv.prodCongr_apply]
  by_cases ha : a = j
  · subst a
    simp [elementaryOperator_apply]
  · have hs : Equiv.swap i j a ≠ i := by
      intro hsi
      have := (Equiv.swap i j).injective (hsi.trans (Equiv.swap_apply_right i j).symm)
      exact ha this
    simp [elementaryOperator_apply, ha, hs]

theorem groupTrace_star (T : Hilbert G n →L[ℂ] Hilbert G n) :
    groupTrace (star T) = star (groupTrace T) := by
  simp only [groupTrace, star_sum, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  apply Finset.sum_congr rfl
  intro i _
  exact (inner_conj_symm (T (identityVector i)) (identityVector i)).symm

end RegularStar

end GroupRingDeterminant

end

end OAI
