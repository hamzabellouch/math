import OAI.Geometry.SingularHomology.SimplicialSphereHomology
import OAI.Geometry.SingularHomology.FiniteSimplicialHomology

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SimplicialSphere

lemma face_surjective : Function.Surjective
    (fun i : Fin 4 => (⟨face i, face_nondegenerate i⟩ : sphere.nonDegenerate 2)) := by
  intro x
  have hx := (SSet.Subcomplex.mem_nonDegenerate_iff (SSet.boundary 3) x.val).1 x.property
  have hmono : Mono (SSet.stdSimplex.objEquiv x.val.val) := by
    rw [← SSet.stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono]
    convert hx using 1
    exact SSet.stdSimplex.objEquiv.symm_apply_apply x.val.val
  let := hmono
  obtain ⟨i, hi⟩ := SimplexCategory.eq_δ_of_mono (SSet.stdSimplex.objEquiv x.val.val)
  refine ⟨i, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply SSet.stdSimplex.objEquiv.injective
  simpa [face] using hi.symm

noncomputable def faceEquiv : Fin 4 ≃ sphere.nonDegenerate 2 :=
  Equiv.ofBijective (fun i => ⟨face i, face_nondegenerate i⟩)
    ⟨fun _ _ h => face_injective (congrArg Subtype.val h), face_surjective⟩

lemma card_nondegenerate_two : Nat.card (sphere.nonDegenerate 2) = 4 := by
  rw [← Nat.card_congr faceEquiv]
  simp

lemma face_coordinate_decomposition :
    (∑ i : Fin 4, coefficient ⟨face i, face_nondegenerate i⟩ ≫
      sphere.ιNormalizedChainComplex (face i)) = 𝟙 (chains.X 2) := by
  apply sphere.normalizedChainComplex_hom_ext
  intro x hx
  obtain ⟨i, hi⟩ := face_surjective ⟨x, hx⟩
  have hix : face i = x := congrArg Subtype.val hi
  rw [← hix]
  simp only [Preadditive.comp_sum, ← Category.assoc, face_coefficient, Category.comp_id]
  simp only [ite_comp, zero_comp, Category.id_comp, Fintype.sum_ite_eq]

lemma eq_zero_of_face_coordinates_eq_zero (v : chains.X 2)
    (h : ∀ i : Fin 4, coefficient ⟨face i, face_nondegenerate i⟩ v = 0) : v = 0 := by
  have heq := ConcreteCategory.congr_hom face_coordinate_decomposition v
  simpa [h] using heq.symm

lemma face_edge_nondegenerate (i : Fin 4) (j : Fin 3) :
    sphere.δ j (face i) ∈ sphere.nonDegenerate 1 := by
  apply (SSet.Subcomplex.mem_nonDegenerate_iff (SSet.boundary 3) _).2
  change SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ j ≫ SimplexCategory.δ i) ∈
    (Δ[3] : SSet).nonDegenerate 1
  rw [SSet.stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono]
  infer_instance

def edgeCoefficient (k : Fin 3) : chains.X 1 ⟶ coefficients := by
  classical
  exact (sphere.isColimitCofanNormalizedChainComplex coefficients 1).desc
    (Cofan.mk coefficients (fun y =>
      if y = ⟨sphere.δ k (face 0), face_edge_nondegenerate 0 k⟩
      then 𝟙 coefficients else 0))

lemma face_edge_coefficient (i : Fin 4) (j k : Fin 3) :
    sphere.ιNormalizedChainComplex (sphere.δ j (face i)) ≫ edgeCoefficient k =
      if (sphere.δ j (face i) : sphere.{0} _⦋1⦌) = sphere.δ k (face 0) then 𝟙 coefficients else 0 := by
  classical
  have h := (sphere.isColimitCofanNormalizedChainComplex coefficients 1).fac
    (Cofan.mk coefficients (fun y : sphere.nonDegenerate 1 =>
      if y = ⟨sphere.δ k (face 0), face_edge_nondegenerate 0 k⟩
      then 𝟙 coefficients else 0))
    (Discrete.mk ⟨sphere.δ j (face i), face_edge_nondegenerate i j⟩)
  simpa [edgeCoefficient, Subtype.mk.injEq] using! h

lemma face_edge_eq_iff (i : Fin 4) (j k : Fin 3) :
    (sphere.δ j (face i) : sphere.{0} _⦋1⦌) = sphere.δ k (face 0) ↔
      (SimplexCategory.δ j ≫ SimplexCategory.δ i) =
        (SimplexCategory.δ k ≫ SimplexCategory.δ (0 : Fin 4)) := by
  constructor
  · intro h
    exact congrArg (fun x : sphere.{0} _⦋1⦌ => SSet.stdSimplex.objEquiv x.val) h
  · intro h
    apply Subtype.ext
    exact congrArg SSet.stdSimplex.objEquiv.symm h

lemma simplex_face_edge_eq_iff (i : Fin 4) (j k : Fin 3) :
    (SimplexCategory.δ j ≫ SimplexCategory.δ i) =
      (SimplexCategory.δ k ≫ SimplexCategory.δ (0 : Fin 4)) ↔
    (i = 0 ∧ j = k) ∨ (i.val = k.val + 1 ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

lemma boundary_edge_zero : chains.d 2 1 ≫ edgeCoefficient 0 =
    coefficient ⟨face 0, face_nondegenerate 0⟩ +
    coefficient ⟨face 1, face_nondegenerate 1⟩ := by
  apply sphere.normalizedChainComplex_hom_ext
  intro x hx
  obtain ⟨i, hi⟩ := face_surjective ⟨x, hx⟩
  have hix : face i = x := congrArg Subtype.val hi
  rw [← hix, ← Category.assoc, SSet.ιNormalizedChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
    Preadditive.comp_add, face_coefficient, face_edge_coefficient]
  fin_cases i <;> norm_num [Fin.sum_univ_succ, Preadditive.neg_comp,
    face_edge_coefficient, face_edge_eq_iff, simplex_face_edge_eq_iff]

lemma boundary_edge_one : chains.d 2 1 ≫ edgeCoefficient 1 =
    -coefficient ⟨face 0, face_nondegenerate 0⟩ +
    coefficient ⟨face 2, face_nondegenerate 2⟩ := by
  apply sphere.normalizedChainComplex_hom_ext
  intro x hx
  obtain ⟨i, hi⟩ := face_surjective ⟨x, hx⟩
  have hix : face i = x := congrArg Subtype.val hi
  rw [← hix, ← Category.assoc, SSet.ιNormalizedChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
    Preadditive.comp_add, Preadditive.comp_neg, face_coefficient, face_edge_coefficient]
  fin_cases i <;> norm_num [Fin.sum_univ_succ, Preadditive.neg_comp,
    face_edge_coefficient, face_edge_eq_iff, simplex_face_edge_eq_iff]

lemma boundary_edge_two : chains.d 2 1 ≫ edgeCoefficient 2 =
    coefficient ⟨face 0, face_nondegenerate 0⟩ +
    coefficient ⟨face 3, face_nondegenerate 3⟩ := by
  apply sphere.normalizedChainComplex_hom_ext
  intro x hx
  obtain ⟨i, hi⟩ := face_surjective ⟨x, hx⟩
  have hix : face i = x := congrArg Subtype.val hi
  rw [← hix, ← Category.assoc, SSet.ιNormalizedChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
    Preadditive.comp_add, face_coefficient, face_edge_coefficient]
  fin_cases i <;> norm_num [Fin.sum_univ_succ, Preadditive.neg_comp,
    face_edge_coefficient, face_edge_eq_iff, simplex_face_edge_eq_iff]

lemma cycle_eq_zero_of_first_coordinate (v : chains.X 2)
    (hv : chains.d 2 1 v = 0)
    (hc : coefficient ⟨face 0, face_nondegenerate 0⟩ v = 0) : v = 0 := by
  have h1 := ConcreteCategory.congr_hom boundary_edge_zero v
  have h2 := ConcreteCategory.congr_hom boundary_edge_one v
  have h3 := ConcreteCategory.congr_hom boundary_edge_two v
  have hc1 : coefficient ⟨face 1, face_nondegenerate 1⟩ v = 0 := by
    simpa [hv, hc] using h1.symm
  have hc2 : coefficient ⟨face 2, face_nondegenerate 2⟩ v = 0 := by
    simpa [hv, hc] using h2.symm
  have hc3 : coefficient ⟨face 3, face_nondegenerate 3⟩ v = 0 := by
    simpa [hv, hc] using h3.symm
  apply eq_zero_of_face_coordinates_eq_zero v
  intro i
  fin_cases i <;> assumption

def firstCycleCoordinate : LinearMap.ker (chains.d 2 1).hom →ₗ[ℝ] ℝ :=
  (coefficient ⟨face 0, face_nondegenerate 0⟩).hom.comp
    (LinearMap.ker (chains.d 2 1).hom).subtype

lemma firstCycleCoordinate_injective : Function.Injective firstCycleCoordinate := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply Subtype.ext
  exact cycle_eq_zero_of_first_coordinate v.val v.property hv

lemma finrank_cycles_two_le_one : Module.finrank ℝ (LinearMap.ker (chains.d 2 1).hom) ≤ 1 := by
  simpa using LinearMap.finrank_le_finrank_of_injective firstCycleCoordinate_injective

lemma finrank_normalized_homology_two_le_one : Module.finrank ℝ (chains.homology 2) ≤ 1 := by
  have : FiniteDimensional ℝ (LinearMap.ker (chains.d 2 1).hom) :=
    Module.Finite.of_injective firstCycleCoordinate firstCycleCoordinate_injective
  rw [(chains.homologyIsoSc' 3 2 1 (by simp) (by simp)).toLinearEquiv.finrank_eq,
    (chains.sc' 3 2 1).moduleCatHomologyIso.toLinearEquiv.finrank_eq]
  change Module.finrank ℝ (LinearMap.ker (chains.d 2 1).hom ⧸
    LinearMap.range (chains.sc' 3 2 1).moduleCatToCycles) ≤ 1
  have : FiniteDimensional ℝ (LinearMap.ker (chains.sc' 3 2 1).g.hom) := by
    change FiniteDimensional ℝ (LinearMap.ker (chains.d 2 1).hom)
    infer_instance
  exact (Submodule.finrank_quotient_le (LinearMap.range
    (chains.sc' 3 2 1).moduleCatToCycles)).trans finrank_cycles_two_le_one

theorem finrank_homology_two :
    Module.finrank ℝ (sphere.homology coefficients 2 : ModuleCat ℝ) = 1 := by
  have : FiniteDimensional ℝ (sphere.homology coefficients 2 : ModuleCat ℝ) :=
    finiteDimensional_real_simplicial_homology sphere 2
  have : Nontrivial (sphere.homology coefficients 2 : ModuleCat ℝ) :=
    homology_two_nontrivial
  apply Nat.le_antisymm
  · let e := asIso (HomologicalComplex.homologyMap
      (sphere.toNormalizedChainComplex coefficients) 2)
    rw [e.toLinearEquiv.finrank_eq]
    exact finrank_normalized_homology_two_le_one
  · exact Module.finrank_pos

end Problem340.SimplicialSphere

end

end OAI
