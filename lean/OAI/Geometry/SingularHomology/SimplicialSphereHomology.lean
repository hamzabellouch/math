import Mathlib

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SimplicialSphere

abbrev sphere : SSet := (SSet.boundary 3 : SSet)
abbrev coefficients : ModuleCat ℝ := ModuleCat.of ℝ ℝ
abbrev chains := sphere.normalizedChainComplex coefficients

def face (i : Fin 4) : sphere _⦋2⦌ :=
  ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i), by
    rw [SSet.boundary_obj_eq_univ 2 3]
    trivial⟩

lemma face_nondegenerate (i : Fin 4) : face i ∈ sphere.nonDegenerate 2 := by
  apply (SSet.Subcomplex.mem_nonDegenerate_iff (SSet.boundary 3) (face i)).2
  change SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) ∈
    (Δ[3] : SSet).nonDegenerate 2
  rw [SSet.stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono]
  infer_instance

def fundamentalCycle : coefficients ⟶ chains.X 2 :=
  sphere.ιNormalizedChainComplex (face 0) -
  sphere.ιNormalizedChainComplex (face 1) +
  sphere.ιNormalizedChainComplex (face 2) -
  sphere.ιNormalizedChainComplex (face 3)

lemma face_injective : Function.Injective face := by
  intro i j h
  have h' := congrArg (fun x : sphere _⦋2⦌ => x.val) h
  have h'' := congrArg SSet.stdSimplex.objEquiv h'
  apply SimplexCategory.δ_injective
  simpa [face] using h''

lemma fundamentalCycle_boundary : fundamentalCycle ≫ chains.d 2 1 = 0 := by
  have e01 : sphere.δ 0 (face 0) = sphere.δ 0 (face 1) := by
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.symm.injective.eq_iff.mpr
    rfl
  have e02 : sphere.δ 1 (face 0) = sphere.δ 0 (face 2) := by
    apply Subtype.ext
    apply SSet.stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  have e03 : sphere.δ 2 (face 0) = sphere.δ 0 (face 3) := by
    apply Subtype.ext
    apply SSet.stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  have e12 : sphere.δ 1 (face 1) = sphere.δ 1 (face 2) := by
    apply Subtype.ext
    apply SSet.stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  have e13 : sphere.δ 2 (face 1) = sphere.δ 1 (face 3) := by
    apply Subtype.ext
    apply SSet.stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  have e23 : sphere.δ 2 (face 2) = sphere.δ 2 (face 3) := by
    apply Subtype.ext
    apply SSet.stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  simp only [fundamentalCycle, Preadditive.sub_comp, Preadditive.add_comp,
    SSet.ιNormalizedChainComplex_d]
  simp only [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  norm_num
  rw [e01, e02, e03, e12, e13, e23]
  abel

def coefficient (x : sphere.nonDegenerate 2) : chains.X 2 ⟶ coefficients := by
  classical
  exact (sphere.isColimitCofanNormalizedChainComplex coefficients 2).desc
    (Cofan.mk coefficients (fun y => if y = x then 𝟙 coefficients else 0))

lemma face_coefficient (i j : Fin 4) :
    sphere.ιNormalizedChainComplex (face i) ≫
      coefficient ⟨face j, face_nondegenerate j⟩ =
        if i = j then 𝟙 coefficients else 0 := by
  classical
  have h := (sphere.isColimitCofanNormalizedChainComplex coefficients 2).fac
    (Cofan.mk coefficients (fun y : sphere.nonDegenerate 2 =>
      if y = ⟨face j, face_nondegenerate j⟩ then 𝟙 coefficients else 0))
    (Discrete.mk ⟨face i, face_nondegenerate i⟩)
  simpa [coefficient, Subtype.mk.injEq, face_injective.eq_iff] using! h

lemma fundamentalCycle_coefficient :
    fundamentalCycle ≫ coefficient ⟨face 0, face_nondegenerate 0⟩ =
      𝟙 coefficients := by
  simp only [fundamentalCycle, Preadditive.sub_comp, Preadditive.add_comp,
    face_coefficient]
  norm_num [Fin.ext_iff]

lemma fundamentalCycle_ne_zero : fundamentalCycle ≠ 0 := by
  intro h
  have hc := fundamentalCycle_coefficient
  rw [h, zero_comp] at hc
  have h01 := ConcreteCategory.congr_hom hc (1 : ℝ)
  norm_num at h01

lemma incoming_differential_zero : chains.d 3 2 = 0 :=
  (sphere.isZero_normalizedChainComplex_X_of_hasDimensionLT coefficients 3 3).eq_zero_of_src _

theorem normalized_homology_two_not_isZero : ¬ IsZero (chains.homology 2) := by
  intro h
  have he : chains.ExactAt 2 :=
    (HomologicalComplex.exactAt_iff_isZero_homology chains 2).2 h
  have he' : (chains.sc' 3 2 1).Exact := by
    exact (HomologicalComplex.exactAt_iff' chains 3 2 1 (by simp) (by simp)).1 he
  have hm : Mono (chains.d 2 1) := he'.mono_g incoming_differential_zero
  apply fundamentalCycle_ne_zero
  apply (cancel_mono (chains.d 2 1)).1
  simp only [fundamentalCycle_boundary, zero_comp]

theorem homology_two_not_isZero : ¬ IsZero (sphere.homology coefficients 2) := by
  intro h
  apply normalized_homology_two_not_isZero
  apply HomologicalComplex.ExactAt.isZero_homology
  apply (exactAt_iff_of_quasiIsoAt
    (sphere.toNormalizedChainComplex coefficients) 2).1
  exact (HomologicalComplex.exactAt_iff_isZero_homology
    (sphere.chainComplex coefficients) 2).2 h

theorem homology_two_nontrivial :
    Nontrivial (sphere.homology coefficients 2 : ModuleCat ℝ) := by
  rw [← not_subsingleton_iff_nontrivial]
  exact fun h => homology_two_not_isZero (ModuleCat.isZero_iff_subsingleton.mpr h)

end Problem340.SimplicialSphere

end

end OAI
