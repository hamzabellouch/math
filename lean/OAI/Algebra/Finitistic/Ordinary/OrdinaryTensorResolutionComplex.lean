import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorAugmentation

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

abbrev termObject (n : ℕ) : ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ := ModuleCat.of _ (term k B l n)

def complex : CochainComplex (ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) ℕ :=
  CochainComplex.of (termObject k B l) (fun n => ModuleCat.ofHom (differential k B l n))
    (fun n => by apply ModuleCat.hom_ext; exact differential_square k B l n)

instance projectiveTerm (n : ℕ) : Projective (termObject k B l n) := inferInstance

theorem term_vanishes (n : ℕ) (h : l < n) : IsZero (termObject k B l n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hz (x : term k B l n) : x = 0 := by
    apply Subtype.ext
    have hp := x.property
    change ((1:B) ⊗ₜ[k] ChainAlgebra.extendedVertex k l n) * x.val = x.val at hp
    rw [ChainAlgebra.extendedVertex,dite_eq_right (Nat.not_le.mpr h),TensorProduct.tmul_zero,zero_mul] at hp
    exact hp.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Every differential preserves the regular left B-action. -/
theorem differential_left (n : ℕ) (b : B) (x : term k B l n) :
    differential k B l n (b • x) = b • differential k B l n x := by
  apply Subtype.ext
  change ((1:B) ⊗ₜ[k] ChainAlgebra.extendedArrow k l n) * (TensorIdeal.coefficient b * x.val) =
    TensorIdeal.coefficient b * (((1:B) ⊗ₜ[k] ChainAlgebra.extendedArrow k l n) * x.val)
  rw [← mul_assoc,← mul_assoc]
  congr 1
  simp only [TensorIdeal.coefficient,Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one]

theorem complex_exactAt (n : ℕ) (hn : n ≠ l) : (complex k B l).ExactAt n := by
  by_cases h : l < n
  · exact HomologicalComplex.ExactAt.of_isZero (term_vanishes k B l n h)
  have hnl : n < l := by omega
  cases n with
  | zero =>
    rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' : differential k B l 0 x = 0 := by
      change ((complex k B l).d 0 ((ComplexShape.up ℕ).next 0)).hom x = 0 at hx
      rw [show (ComplexShape.up ℕ).next 0 = 1 by simp] at hx
      change (CochainComplex.of.d (termObject k B l) (fun n => ModuleCat.ofHom (differential k B l n)) 0 (0+1)).hom x = 0 at hx
      rw [CochainComplex.of_d] at hx
      exact hx
    have hx0 : x = 0 := initial_injective k B l hnl (hx'.trans (map_zero _).symm)
    exact ⟨0, by simp only [hx0,map_zero]⟩
  | succ n =>
    apply (HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)).2
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' : differential k B l (n+1) x = 0 := by
      change (CochainComplex.of.d (termObject k B l) (fun n => ModuleCat.ofHom (differential k B l n)) (n+1) ((n+1)+1)).hom x = 0 at hx
      rw [CochainComplex.of_d] at hx
      exact hx
    obtain ⟨y,hy⟩ := (differential_exact k B l n hnl x).mp hx'
    refine ⟨y, ?_⟩
    change (CochainComplex.of.d (termObject k B l)
      (fun j => ModuleCat.ofHom (differential k B l j)) n (n+1)).hom y = x
    rw [CochainComplex.of_d]
    exact hy

abbrev augmentationHom : termObject k B l l ⟶ ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B) :=
  ModuleCat.ofHom (augmentation k B l)

instance augmentation_epi : Epi (augmentationHom k B l) :=
  (ModuleCat.epi_iff_surjective _).mpr (augmentation_surjective k B l)

/-- The actual B-extended resolution augmentation as a chain map. -/
def augmentationMap : complex k B l ⟶
    (HomologicalComplex.single _ (.up ℕ) l).obj (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) :=
  HomologicalComplex.mkHomToSingle (augmentationHom k B l) (by
    intro i hi
    change i+1=l at hi
    subst l
    change CochainComplex.of.d _ _ i (i+1) ≫ augmentationHom k B (i+1) = 0
    rw [CochainComplex.of_d]
    ext x
    exact congrArg (fun f => f x) (augmentation_comp k B i))

theorem differential_last_zero : differential k B l l = 0 := by
  ext x
  change ((1:B) ⊗ₜ[k] ChainAlgebra.extendedArrow k l l) * x.val = 0
  rw [ChainAlgebra.extendedArrow,dite_eq_right (lt_irrefl l),TensorProduct.tmul_zero,zero_mul]

theorem augmentationMap_quasiIsoAt_last : QuasiIsoAt (augmentationMap k B l) l := by
  rw [quasiIsoAt_iff]
  refine (ShortComplex.quasiIso_iff_of_zeros' _ ?_ ?_ ?_).2 ?_
  · change (complex k B l).d l ((ComplexShape.up ℕ).next l) = 0
    rw [show (ComplexShape.up ℕ).next l = l+1 by simp]
    change CochainComplex.of.d (termObject k B l) (fun n => ModuleCat.ofHom (differential k B l n)) l (l+1) = 0
    rw [CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact differential_last_zero k B l
  · exact HomologicalComplex.single_obj_d (.up ℕ) l (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) ((ComplexShape.up ℕ).prev l) l
  · exact HomologicalComplex.single_obj_d (.up ℕ) l (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) l ((ComplexShape.up ℕ).next l)
  · change (ShortComplex.mk ((complex k B l).d ((ComplexShape.up ℕ).prev l) l)
      ((augmentationMap k B l).f l) _).Exact ∧ Epi ((augmentationMap k B l).f l)
    have hf : (augmentationMap k B l).f l = augmentationHom k B l ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B))).inv := by
      unfold augmentationMap
      apply HomologicalComplex.mkHomToSingle_f
    simp only [hf]
    constructor
    · refine ChainAlgebra.exact_post_iso _ _ ?_
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B))).symm ?_
      · cases l with
        | zero =>
          have hz := (complex k B 0).shape ((ComplexShape.up ℕ).prev 0) 0 (by simp)
          erw [hz,zero_comp]
        | succ n =>
          rw [show (ComplexShape.up ℕ).prev (n+1) = n by simp]
          change CochainComplex.of.d _ _ n (n+1) ≫ augmentationHom k B (n+1) = 0
          rw [CochainComplex.of_d]
          ext x
          exact congrArg (fun f => f x) (augmentation_comp k B n)
      cases l with
      | zero =>
        rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        have hx0 : x = 0 := augmentation_zero_injective k B (hx.trans (map_zero _).symm)
        exact ⟨0, by simp only [hx0,map_zero]⟩
      | succ n =>
        rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        obtain ⟨y,hy⟩ := (augmentation_exact k B n x).mp hx
        change ∃ z : termObject k B (n+1) ((ComplexShape.up ℕ).prev (n+1)),
          (CochainComplex.of.d (termObject k B (n+1))
            (fun j => ModuleCat.ofHom (differential k B (n+1) j))
            ((ComplexShape.up ℕ).prev (n+1)) (n+1)).hom z = x
        rw [show (ComplexShape.up ℕ).prev (n+1) = n by simp]
        exact ⟨y, by rw [CochainComplex.of_d]; exact hy⟩
    · erw [ModuleCat.epi_iff_surjective]
      exact ((ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B))).inv)).comp
        (augmentation_surjective k B l)

/-- Actual augmentation quasi-isomorphism for the finite right-BC-projective resolution. -/
theorem augmentationMap_quasiIso : QuasiIso (augmentationMap k B l) := by
  constructor
  intro n
  by_cases hn : n = l
  · subst n; exact augmentationMap_quasiIsoAt_last k B l
  · apply (quasiIsoAt_iff_exactAt' _ n ?_).2 (complex_exactAt k B l n hn)
    exact HomologicalComplex.ExactAt.of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
