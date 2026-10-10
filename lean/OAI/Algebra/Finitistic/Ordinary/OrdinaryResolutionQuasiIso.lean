import OAI.Algebra.Finitistic.Ordinary.OrdinaryResolutionExact
import Mathlib.Algebra.Homology.QuasiIso

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.OrdinarySimulation.ChainAlgebra
universe u
variable (k : Type u) [Field k] (l : ℕ)

theorem resolutionInitial_injective (h : 0 < l) :
    Function.Injective (resolutionDifferential k l 0).hom := by
  intro x y hxy
  apply (supportedIdealEquiv k l 0 (by omega)).injective
  apply resolution_first_injective (k := k) h
  rw [← supportedIdealEquiv_d k l 0 h, ← supportedIdealEquiv_d k l 0 h, hxy]

/-- Exactness in every degree except the terminal homology degree. -/
theorem terminalProjectiveComplex_exactAt (n : ℕ) (hn : n ≠ l) :
    (terminalProjectiveComplex k l).ExactAt n := by
  by_cases h : l < n
  · exact HomologicalComplex.ExactAt.of_isZero (resolutionTerm_vanishes k l n h)
  have hnl : n < l := by omega
  cases n with
  | zero =>
    rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' : (resolutionDifferential k l 0).hom x = 0 := by
      change ((terminalProjectiveComplex k l).d 0 ((ComplexShape.up ℕ).next 0)).hom x = 0 at hx
      rw [show (ComplexShape.up ℕ).next 0 = 1 by simp] at hx
      change (CochainComplex.of.d (resolutionTerm k l) (resolutionDifferential k l) 0 (0+1)).hom x = 0 at hx
      rw [CochainComplex.of_d] at hx
      exact hx
    have hx0 : x = 0 := resolutionInitial_injective k l hnl (hx'.trans (map_zero _).symm)
    refine ⟨0, ?_⟩
    simp only [hx0, map_zero]
  | succ n =>
    apply (HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)).2
    change (ShortComplex.mk (CochainComplex.of.d _ _ n (n+1)) (CochainComplex.of.d _ _ (n+1) ((n+1)+1)) _).Exact
    simpa only [CochainComplex.of_d] using supported_complex_exact k l n hnl

theorem resolutionAugmentation_surjective : Function.Surjective (resolutionAugmentation k l).hom :=
  (augmentation_surjective k l).comp (supportedIdealEquiv k l l le_rfl).surjective

instance resolutionAugmentation_epi : Epi (resolutionAugmentation k l) :=
  (ModuleCat.epi_iff_surjective _).mpr (resolutionAugmentation_surjective k l)

theorem resolutionAugmentation_comp (n : ℕ) :
    resolutionDifferential k (n+1) n ≫ resolutionAugmentation k (n+1) = 0 := by
  ext x
  change (extendedArrow k (n+1) n * x.val).1 (Fin.last (n+1)) = (0:k)
  rw [extendedArrow, dite_eq_left (by omega), mul_diagonal, arrow_diagonal, zero_mul]

theorem resolutionAugmentation_exact (n : ℕ) :
    (ShortComplex.mk (resolutionDifferential k (n+1) n) (resolutionAugmentation k (n+1))
      (resolutionAugmentation_comp k n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : augmentation k (n+1) (supportedIdealEquiv k (n+1) (n+1) le_rfl x) = 0 := hx
  obtain ⟨y,hy⟩ := (augmentation_exact k n _).mp hx'
  refine ⟨(supportedIdealEquiv k (n+1) n (by omega)).symm y, ?_⟩
  apply (supportedIdealEquiv k (n+1) (n+1) le_rfl).injective
  rw [supportedIdealEquiv_d k (n+1) n (by omega), LinearEquiv.apply_symm_apply]
  exact hy

theorem resolutionAugmentation_zero_injective :
    Function.Injective (resolutionAugmentation k 0).hom :=
  (augmentation_zero_injective k).comp (supportedIdealEquiv k 0 0 le_rfl).injective

theorem resolutionDifferential_last_zero : resolutionDifferential k l l = 0 := by
  ext x
  change extendedArrow k l l * x.val = 0
  rw [extendedArrow, dite_eq_right (lt_irrefl l), zero_mul]

/-- Postcomposing a short complex's second map by an isomorphism preserves exactness. -/
theorem exact_post_iso {R : Type u} [Ring R] {X Y Z Z' : ModuleCat.{u} R}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0) (e : Z ≅ Z')
    (h : (ShortComplex.mk f g hfg).Exact) :
    (ShortComplex.mk f (g ≫ e.hom) (by rw [← Category.assoc, hfg, zero_comp])).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at h ⊢
  intro x hx
  apply h x
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  exact hx.trans (map_zero _).symm

/-- The augmentation is a quasi-isomorphism at the terminal degree. -/
theorem terminalAugmentationMap_quasiIsoAt_last :
    QuasiIsoAt (terminalAugmentationMap k l) l := by
  rw [quasiIsoAt_iff]
  refine (ShortComplex.quasiIso_iff_of_zeros' _ ?_ ?_ ?_).2 ?_
  · change (terminalProjectiveComplex k l).d l ((ComplexShape.up ℕ).next l) = 0
    rw [show (ComplexShape.up ℕ).next l = l+1 by simp]
    change CochainComplex.of.d (resolutionTerm k l) (resolutionDifferential k l) l (l+1) = 0
    rw [CochainComplex.of_d]
    exact resolutionDifferential_last_zero k l
  · exact HomologicalComplex.single_obj_d (.up ℕ) l (ModuleCat.of (ChainAlgebra k l)ᵐᵒᵖ (TerminalSimple k)) ((ComplexShape.up ℕ).prev l) l
  · exact HomologicalComplex.single_obj_d (.up ℕ) l (ModuleCat.of (ChainAlgebra k l)ᵐᵒᵖ (TerminalSimple k)) l ((ComplexShape.up ℕ).next l)
  · change (ShortComplex.mk ((terminalProjectiveComplex k l).d ((ComplexShape.up ℕ).prev l) l)
        ((terminalAugmentationMap k l).f l) _).Exact ∧ Epi ((terminalAugmentationMap k l).f l)
    have hf : (terminalAugmentationMap k l).f l = resolutionAugmentation k l ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (ChainAlgebra k l)ᵐᵒᵖ (TerminalSimple k))).inv := by
      unfold terminalAugmentationMap
      apply HomologicalComplex.mkHomToSingle_f
    simp only [hf]
    constructor
    · refine exact_post_iso _ _ ?_
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (ChainAlgebra k l)ᵐᵒᵖ (TerminalSimple k))).symm ?_
      · cases l with
        | zero =>
          have hz := (terminalProjectiveComplex k 0).shape ((ComplexShape.up ℕ).prev 0) 0 (by simp)
          erw [hz, zero_comp]
        | succ n =>
          rw [show (ComplexShape.up ℕ).prev (n+1) = n by simp]
          simp only [terminalProjectiveComplex, CochainComplex.of_d]
          convert resolutionAugmentation_comp k n using 1
          rfl
      cases l with
      | zero =>
        rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        have hx' : (resolutionAugmentation k 0).hom x = 0 := hx
        have hx0 : x = 0 := resolutionAugmentation_zero_injective k (hx'.trans (map_zero _).symm)
        refine ⟨0, ?_⟩
        simp only [hx0, map_zero]
      | succ n =>
        rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
          (resolutionAugmentation_exact k n) x hx
        change ∃ z : resolutionTerm k (n+1) ((ComplexShape.up ℕ).prev (n+1)),
          (CochainComplex.of.d (resolutionTerm k (n+1)) (resolutionDifferential k (n+1))
            ((ComplexShape.up ℕ).prev (n+1)) (n+1)).hom z = x
        rw [show (ComplexShape.up ℕ).prev (n+1) = n by simp]
        exact ⟨y, by simpa only [CochainComplex.of_d] using hy⟩
    · erw [ModuleCat.epi_iff_surjective]
      exact ((ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (ChainAlgebra k l)ᵐᵒᵖ (TerminalSimple k))).inv)).comp
        (resolutionAugmentation_surjective k l)

/-- The source's finite projective resolution now has its actual augmentation quasi-isomorphism. -/
theorem terminalAugmentationMap_quasiIso : QuasiIso (terminalAugmentationMap k l) := by
  constructor
  intro n
  by_cases hn : n = l
  · subst n; exact terminalAugmentationMap_quasiIsoAt_last k l
  · apply (quasiIsoAt_iff_exactAt' _ n ?_).2 (terminalProjectiveComplex_exactAt k l n hn)
    exact HomologicalComplex.ExactAt.of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
end LittleFinitistic.OrdinarySimulation.ChainAlgebra

end

end OAI
