import OAI.Analysis.KadisonKastler.RelativeCentralStandardSpace
import OAI.Analysis.KadisonKastler.PositiveConeReference

namespace OAI

/-! # Finite-matrix coefficients on the relative standard space

The central-vector projection retains the normalized matrix trace on
matrix entries. The conjugate relative action preserves this same space.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E : MatrixUnitSystem ι (Algebra M))

omit [Nonempty ι] in
private theorem amplify_matrix_entry (k i j : ι) :
    E.amplify k (E.entry i j) = if k = i then if j = k then 1 else 0 else 0 := by
  by_cases hki : k = i
  · subst k
    by_cases hji : j = i
    · subst j
      simpa [MatrixUnitSystem.amplify,E.mul_entry] using E.total
    · simp [MatrixUnitSystem.amplify,E.mul_entry,hji]
  · simp [MatrixUnitSystem.amplify,E.mul_entry,hki]

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ hright in
theorem centralProjection_matrix_entry {ξ : H}
    (hξ : ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J) (i j : ι) :
    (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection ((E.entry i j).val ξ) =
      if i = j then (Fintype.card ι : ℂ)⁻¹ • ξ else 0 := by
  rw [matrixCentralProjection_algebraVector E J hJ hright ξ hξ]
  have ha : matrixRelativeAverage E (E.entry i j) =
      if i = j then (Fintype.card ι : ℂ)⁻¹ • (1 : Algebra E.relativeVonNeumann) else 0 := by
    apply Subtype.ext
    change ((Fintype.card ι : ℂ)⁻¹ •
      M.toStarSubalgebra.subtype (E.commutant.subtype
        (∑ k, (⟨E.amplify k (E.entry i j),E.amplify_mem k _⟩ : E.commutant)))) = _
    rw [map_sum E.commutant.subtype,map_sum M.toStarSubalgebra.subtype]
    simp only [amplify_matrix_entry]
    by_cases hij : i = j
    · subst j
      simp [apply_ite]
    · simp [apply_ite,hij,Ne.symm hij]
  rw [ha]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

include hJ hright in
omit [Nonempty ι] in
theorem relative_conjugate_preserves_central {ξ : H}
    (hξ : ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (a : Algebra E.relativeVonNeumann) :
    conjugationOperator J a.val ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J := by
  exact centralVectorSpace_conjugate _ J hJ
    (relative_algebra_orbit_mem_central E J hright (J ξ)
      (centralVectorSpace_conjugate _ J hJ hξ) a)

include hJ hright in
theorem centralProjection_mixed_coefficient {ξ : H}
    (hξ : ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (c d : E.commutant) (i j k l : ι) :
    (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection
      ((c.val * E.entry i j).val
        (conjugationOperator J (d.val * E.entry k l).val ξ)) =
      if j = l then if i = k then (Fintype.card ι : ℂ)⁻¹ •
        (c.val.val (conjugationOperator J d.val.val ξ)) else 0 else 0 := by
  let v := c.val.val (conjugationOperator J d.val.val ξ)
  have hv : v ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J :=
    relative_algebra_orbit_mem_central E J hright _
      (relative_conjugate_preserves_central E J hJ hright hξ (E.relativeEquiv d))
      (E.relativeEquiv c)
  have he : conjugationOperator J (E.entry k l).val ξ = (E.entry l k).val ξ := by
    have h := (mem_centralVectorSpace_matrix_iff E J ξ).mp hξ l k
    have hs : star (E.entry l k).val = (E.entry k l).val := congrArg Subtype.val (E.star_entry l k)
    rw [hs] at h
    exact h.symm
  have hr (a b : Algebra M) : a.val * conjugationOperator J b.val =
      conjugationOperator J b.val * a.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp (hright b) a.val a.property
  have hreduce : (c.val * E.entry i j).val
      (conjugationOperator J (d.val * E.entry k l).val ξ) =
      if j = l then (E.entry i k).val v else 0 := by
    change (c.val.val * (E.entry i j).val)
      (conjugationOperator J (d.val.val * (E.entry k l).val) ξ) = _
    rw [conjugationOperator_mul J hJ]
    change c.val.val ((E.entry i j).val
      (conjugationOperator J d.val.val (conjugationOperator J (E.entry k l).val ξ))) = _
    rw [he]
    have hcomm := congrArg (fun T : H →L[ℂ] H => T ((E.entry l k).val ξ)) (hr (E.entry i j) d.val)
    change (E.entry i j).val (conjugationOperator J d.val.val ((E.entry l k).val ξ)) =
      conjugationOperator J d.val.val ((E.entry i j).val ((E.entry l k).val ξ)) at hcomm
    rw [hcomm]
    change c.val.val (conjugationOperator J d.val.val ((E.entry i j * E.entry l k).val ξ)) = _
    rw [E.mul_entry]
    by_cases hjl : j = l
    · rw [ite_eq_left hjl,ite_eq_left hjl]
      have hcomm' := congrArg (fun T : H →L[ℂ] H => T ξ) (hr (E.entry i k) d.val)
      change (E.entry i k).val (conjugationOperator J d.val.val ξ) =
        conjugationOperator J d.val.val ((E.entry i k).val ξ) at hcomm'
      rw [← hcomm']
      exact congrArg (fun T : H →L[ℂ] H => T (conjugationOperator J d.val.val ξ))
        (congrArg Subtype.val (c.property i k).eq).symm
    · simp [hjl]
  rw [hreduce]
  by_cases hjl : j = l
  · rw [ite_eq_left hjl,ite_eq_left hjl,centralProjection_matrix_entry E J hJ hright hv]
  · simp [hjl]

omit [Nonempty ι] [CompleteSpace H] in
private theorem conjugationOperator_sum {κ : Type*} (s : Finset κ)
    (a : κ → H →L[ℂ] H) :
    conjugationOperator J (∑ k ∈ s, a k) = ∑ k ∈ s, conjugationOperator J (a k) := by
  ext x
  simp only [conjugationOperator_apply,sum_apply,map_sum]

private theorem modularQuadratic_sum_apply {κ : Type*} (s : Finset κ)
    (a : κ → Algebra M) (ξ : H) :
    modularQuadratic J (∑ k ∈ s, a k) ξ =
      ∑ i ∈ s, ∑ j ∈ s, (a i).val (conjugationOperator J (a j).val ξ) := by
  change (M.toStarSubalgebra.subtype (∑ k ∈ s,a k) *
    conjugationOperator J (M.toStarSubalgebra.subtype (∑ k ∈ s,a k))) ξ = _
  simp only [map_sum,conjugationOperator_sum,Finset.sum_mul,Finset.mul_sum,sum_apply,
    mul_apply_eq_comp]
  exact Finset.sum_comm

include hJ hright in
theorem centralProjection_quadratic_coefficients {ξ : H}
    (hξ : ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (c : Matrix ι ι E.commutant) :
    (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection
      (modularQuadratic J (E.coefficientHom c) ξ) =
      (Fintype.card ι : ℂ)⁻¹ • ∑ i, ∑ j, modularQuadratic J (c i j).val ξ := by
  let a : ι × ι → Algebra M := fun p => (c p.1 p.2).val * E.entry p.1 p.2
  have he : E.coefficientHom c = ∑ p, a p := by
    change (∑ i,∑ j,(c i j).val * E.entry i j) = ∑ p, a p
    rw [Fintype.sum_prod_type]
  rw [he,modularQuadratic_sum_apply J, map_sum]
  simp only [map_sum,Fintype.sum_prod_type]
  simp only [a,centralProjection_mixed_coefficient E J hJ hright hξ]
  simp [Finset.smul_sum,modularQuadratic,mul_apply_eq_comp]

include hJ hright in
theorem centralProjection_mem_relative_positiveCone {ξ η : H}
    (hξ : ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection η ∈
      modularPositiveCone (M := E.relativeVonNeumann) J ξ := by
  classical
  let K := centralVectorSpace (matrixUnitConcreteAlgebra E) J
  let C := modularPositiveCone (M := E.relativeVonNeumann) J ξ
  have hgen (a : Algebra M) : K.starProjection (modularQuadratic J a ξ) ∈ C := by
    let o : ι := Classical.choice inferInstance
    obtain ⟨c,rfl⟩ := E.coefficientHom_surjective o a
    rw [centralProjection_quadratic_coefficients E J hJ hright hξ]
    have hs : (∑ i,∑ j,modularQuadratic J (c i j).val ξ) ∈ C :=
      modularPositiveCone_sum_mem J ξ Finset.univ _ (fun i _ =>
        modularPositiveCone_sum_mem J ξ Finset.univ _ (fun j _ =>
          modularQuadratic_mem_positiveCone J ξ (E.relativeEquiv (c i j))))
    have hp : 0 < (Fintype.card ι : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    have hh := C.smul_mem hp hs
    have he := IsScalarTower.algebraMap_smul ℂ ((Fintype.card ι : ℝ)⁻¹)
      (∑ i,∑ j,modularQuadratic J (c i j).val ξ)
    rw [← he] at hh
    simpa only [map_inv₀,map_natCast] using hh
  have hh : ConvexCone.hull ℝ (Set.range (fun a : Algebra M => modularQuadratic J a ξ)) ≤
      C.comap (K.starProjection.restrictScalars ℝ).toLinearMap := by
    apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    exact hgen a
  exact closure_minimal (fun _ hx => hh hx)
    ((modularPositiveCone_isClosed (M := E.relativeVonNeumann) J ξ).preimage
      K.starProjection.continuous) hη

theorem modularPositiveCone_mono_algebra (N : VonNeumannAlgebra H) (hNM : N ≤ M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    modularPositiveCone (M := N) J ξ ≤ modularPositiveCone (M := M) J ξ := by
  have hh : ConvexCone.hull ℝ (Set.range (fun a : Algebra N => modularQuadratic J a ξ)) ≤
      modularPositiveCone (M := M) J ξ := by
    apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    exact modularQuadratic_mem_positiveCone J ξ ⟨a.val,hNM a.property⟩
  exact closure_minimal hh (modularPositiveCone_isClosed J ξ)

include hJ hright in
omit [Nonempty ι] in
theorem relative_positiveCone_mem_central {ξ η : H}
    (hξ : ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (hη : η ∈ modularPositiveCone (M := E.relativeVonNeumann) J ξ) :
    η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J := by
  let K := centralVectorSpace (matrixUnitConcreteAlgebra E) J
  let C : ConvexCone ℝ H :=
    { carrier := K
      smul_mem' r _ x hx := K.smul_mem r hx
      add_mem' x hx y hy := K.add_mem hx hy }
  have hh : ConvexCone.hull ℝ
      (Set.range (fun a : Algebra E.relativeVonNeumann => modularQuadratic J a ξ)) ≤ C := by
    apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    exact relative_algebra_orbit_mem_central E J hright _
      (relative_conjugate_preserves_central E J hJ hright hξ a) a
  exact closure_minimal hh (centralVectorSpace_isClosed _ J) hη

include hJ hright in
theorem mem_relative_positiveCone_iff {ξ η : H}
    (hξ : ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J) :
    η ∈ modularPositiveCone (M := E.relativeVonNeumann) J ξ ↔
      η ∈ modularPositiveCone (M := M) J ξ ∧
      η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J := by
  constructor
  · intro hη
    exact ⟨modularPositiveCone_mono_algebra E.relativeVonNeumann E.relativeVonNeumann_le J ξ hη,
      relative_positiveCone_mem_central E J hJ hright hξ hη⟩
  · rintro ⟨hη,hcentral⟩
    have h := centralProjection_mem_relative_positiveCone E J hJ hright hξ hη
    rwa [Submodule.starProjection_eq_self_iff.mpr hcentral] at h

end

end KadisonKastler

end OAI
