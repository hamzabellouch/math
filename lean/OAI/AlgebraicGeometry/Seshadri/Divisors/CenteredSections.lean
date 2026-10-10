import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionChart
import OAI.AlgebraicGeometry.Seshadri.Projective.ProjectiveTranslate
import OAI.AlgebraicGeometry.Seshadri.Projective.ProjectiveMapEvaluation

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] [Fintype σ] {X : Scheme}
local instance : DecidableEq σ := Classical.decEq σ

@[simp] lemma scalarEnd_zero : scalarEnd (0 : Γ(X, ⊤)) = 0 := by
  apply endValue_injective
  rw [endValue_scalarEnd]
  rfl

@[simp] lemma scalarEnd_one : scalarEnd (1 : Γ(X, ⊤)) = 𝟙 (O X) := by
  apply endValue_injective
  simp

def shiftCoefficients (c : σ → K) : Option σ → (Option σ → K)
  | none => Pi.single none 1
  | some i => Pi.single (some i) 1 + Pi.single none (c i)

lemma linearEquation_single (i : Option σ) (a : K) :
    linearEquation (Pi.single i a) = C a * MvPolynomial.X i := by
  classical
  rw [linearEquation, Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_eq_of_ne hji]
  · simp

lemma linearEquation_add (a b : Option σ → K) :
    linearEquation (a + b) = linearEquation a + linearEquation b := by
  classical
  simp [linearEquation, map_add, add_mul, Finset.sum_add_distrib]

lemma linearEquation_shiftCoefficients (c : σ → K) (i : Option σ) :
    linearEquation (shiftCoefficients c i) = shiftedVariable c i := by
  cases i <;> simp [shiftCoefficients, shiftedVariable, linearEquation_single,
    linearEquation_add]

def shiftedSections {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (c : σ → K) (i : Option σ) : O X ⟶ M :=
  sectionCombination k s (shiftCoefficients c i)

lemma coefficient_shiftedSections {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (c : σ → K) (U : X.Opens)
    (e : M.restrict U.ι ≅ O U.toScheme) (i : Option σ) :
    coefficient e (restrictSection U.ι (shiftedSections k s c i)) =
      eval₂Hom (U.ι.appTop.hom.comp k)
        (fun j => coefficient e (restrictSection U.ι (s j))) (shiftedVariable c i) := by
  rw [← linearEquation_shiftCoefficients]
  simp only [shiftedSections, sectionCombination, restrictSection_sum,
    coefficient_sum, linearEquation, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X']
  apply Finset.sum_congr rfl
  intro j hj
  exact coefficient_restrict_scalar_comp U.ι e _ _

lemma shiftedSections_none {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (c : σ → K) :
    shiftedSections k s c none = s none := by
  classical
  simp [shiftedSections, sectionCombination, shiftCoefficients, Pi.single_apply]

lemma shiftedSections_preimage {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (c : σ → K) (i : Option σ) :
    (sectionsMorphism k s hs ≫ (projectiveShift c).hom) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade K (Option σ)) (MvPolynomial.X i) =
        SectionOpens.isoOpen (shiftedSections k s c i) := by
  rw [Scheme.Hom.comp_preimage]
  change sectionsMorphism k s hs ⁻¹ᵁ
    (Proj.map (projectiveShiftHom c) (shift_irrelevant c) ⁻¹ᵁ _) = _
  rw [Proj.map_preimage_basicOpen, projectiveShiftHom_X,
    ← linearEquation_shiftCoefficients, sectionsMorphism_hyperplane]
  rfl

lemma shiftedSections_cover {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (c : σ → K) : (⨆ i, SectionOpens.isoOpen (shiftedSections k s c i)) = ⊤ := by
  simp_rw [← shiftedSections_preimage k s hs c]
  rw [← Scheme.Hom.preimage_iSup, projective_coordinate_cover, Scheme.Hom.preimage_top]

omit [Fintype σ] in
lemma eval₂_comp_shift (k : K →+* Γ(X, ⊤)) (a : Option σ → Γ(X, ⊤)) (c : σ → K) :
    (eval₂Hom k a).comp (projectiveShiftHom c).toRingHom =
      eval₂Hom k (fun i => eval₂Hom k a (shiftedVariable c i)) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp
  · intro i
    simp

omit [Fintype σ] in
lemma coordinatesMap_comp_shift (k : K →+* Γ(X, ⊤)) (a : Option σ → Γ(X, ⊤))
    (h : a none = 1) (c : σ → K) :
    coordinatesMap X k a none h ≫ (projectiveShift c).hom =
      coordinatesMap X k (fun i => eval₂Hom k a (shiftedVariable c i)) none
        (by simpa [shiftedVariable] using h) := by
  unfold coordinatesMap
  rw [Category.assoc]
  congr 1
  exact fromUnitCoordinate_comp_Proj_map_eq (projectiveShiftHom c) (shift_irrelevant c)
    (eval₂Hom k a) (by decide : 0 < (1 : ℕ)) (coordinates_X_mem (K := K) none)
    (MvPolynomial.X none) (projectiveShiftHom_X c none) (coordinates_X_mem none)
    _ _ (eval₂_comp_shift k a c) _

theorem sectionsMorphism_shift [IsIntegral X] {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (h₀ : (SectionOpens.isoOpen (s none) : Set X).Nonempty) (c : σ → K) :
    sectionsMorphism k (shiftedSections k s c) (shiftedSections_cover k s hs c) =
      sectionsMorphism k s hs ≫ (projectiveShift c).hom := by
  let U := SectionOpens.isoOpen (s none)
  let : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense h₀)
  let b : Proj (PolyGrade K (Option σ)) ⟶ Spec (CommRingCat.of ℤ) :=
    projectiveBase ≫ specZIsTerminal.from (Spec (CommRingCat.of K))
  let : IsSeparated (specZIsTerminal.from (Spec (CommRingCat.of K))) := inferInstance
  let : IsSeparated b := inferInstance
  apply ext_of_isDominant_of_isSeparated b (specZIsTerminal.hom_ext _ _) U.ι
  have hU : U ≤ SectionOpens.isoOpen (shiftedSections k s c none) := by
    rw [shiftedSections_none]
  rw [sectionsMorphism_on k (shiftedSections k s c) (shiftedSections_cover k s hs c)
    none U hU, ← Category.assoc, sectionsMorphism_on k s hs none U le_rfl,
    coordinatesMap_comp_shift]
  congr 1
  funext i
  simpa only [shiftedSections_none] using
    coefficient_shiftedSections k s c U (sectionFrameOn (s none) U le_rfl) i

theorem shiftedSections_closed [IsIntegral X] {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)]
    (h₀ : (SectionOpens.isoOpen (s none) : Set X).Nonempty) (c : σ → K) :
    IsClosedImmersion (sectionsMorphism k (shiftedSections k s c)
      (shiftedSections_cover k s hs c)) := by
  rw [sectionsMorphism_shift k s hs h₀ c]
  infer_instance

end
end MaximalSeshadri.Projective

end


end
end

end OAI
