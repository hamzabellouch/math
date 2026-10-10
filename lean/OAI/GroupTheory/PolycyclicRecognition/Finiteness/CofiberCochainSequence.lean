import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CochainSuccessor
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepCofiber
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RepCochainMaps
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

namespace OAI

/-! # The short exact sequence of cochains of a mapping cone -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {k G : Type} [CommRing k] [Group G]
  {P Q : ChainComplex (Rep k G) ℕ} (φ : P ⟶ Q) (A : Rep k G)

def cofiberCochainInclusionComponent (i : ℕ) :
    (cochainSuccessor (P.linearYonedaObj k A)).X i ⟶
      (ChainComplex.linearYonedaObj (repCofiber φ) k A).X i :=
  match i with
  | 0 => 0
  | n + 1 => (cochainSuccessorXIso (P.linearYonedaObj k A) n).hom ≫
      ModuleCat.ofHom (Linear.leftComp k A (repCofiberFst φ n))

def cofiberCochainInclusion :
    cochainSuccessor (P.linearYonedaObj k A) ⟶ ChainComplex.linearYonedaObj (repCofiber φ) k A where
  f := cofiberCochainInclusionComponent φ A
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    cases i with
    | zero => exact (cochainSuccessor_zero (P.linearYonedaObj k A)).eq_of_src _ _
    | succ i =>
      change ((cochainSuccessorXIso (P.linearYonedaObj k A) i).hom ≫ _) ≫ _ =
        (cochainSuccessor (P.linearYonedaObj k A)).d (i + 1) (i + 2) ≫
          ((cochainSuccessorXIso (P.linearYonedaObj k A) (i + 1)).hom ≫ _)
      rw [cochainSuccessor_d]
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_assoc]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let f : P.X i ⟶ A := (cochainSuccessorXIso (P.linearYonedaObj k A) i).hom.hom x
      change (repCofiber φ).d (i + 2) (i + 1) ≫ (repCofiberFst φ i ≫ f) =
        repCofiberFst φ (i + 1) ≫ (-(P.d (i + 1) i ≫ f))
      have hd : (repCofiber φ).d (i + 2) (i + 1) ≫ repCofiberFst φ i =
          -repCofiberFst φ (i + 1) ≫ P.d (i + 1) i :=
        homotopyCofiber.d_fstX φ (i + 2) (i + 1) i rfl rfl
      rw [← Category.assoc, hd]
      simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]

def cofiberCochainProjection :
    ChainComplex.linearYonedaObj (repCofiber φ) k A ⟶ Q.linearYonedaObj k A :=
  repCochainPrecomp k (homotopyCofiber.inr φ) A

theorem cofiberCochainInclusion_projection :
    cofiberCochainInclusion φ A ≫ cofiberCochainProjection φ A = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | zero => exact zero_comp
  | succ i =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let f : P.X i ⟶ A := (cochainSuccessorXIso (P.linearYonedaObj k A) i).hom.hom x
    change repCofiberInr φ (i + 1) ≫
        (repCofiberFst φ i ≫ f) = 0
    rw [← Category.assoc, homotopyCofiber.inrX_fstX φ (i + 1) i rfl, zero_comp]

def cofiberCochainSequence : ShortComplex (CochainComplex (ModuleCat k) ℕ) :=
  ShortComplex.mk (cofiberCochainInclusion φ A) (cofiberCochainProjection φ A)
    (cofiberCochainInclusion_projection φ A)

theorem cofiberCochainProjection_surjective (i : ℕ) :
    Function.Surjective ((cofiberCochainProjection φ A).f i).hom := by
  intro f
  change Q.X i ⟶ A at f
  refine ⟨repCofiberSnd φ i ≫ f, ?_⟩
  change repCofiberInr φ i ≫ (repCofiberSnd φ i ≫ f) = f
  rw [← Category.assoc, homotopyCofiber.inrX_sndX, Category.id_comp]

theorem cofiberCochainInclusion_injective (i : ℕ) :
    Function.Injective ((cofiberCochainInclusion φ A).f i).hom := by
  cases i with
  | zero =>
    let := ModuleCat.subsingleton_of_isZero (cochainSuccessor_zero (P.linearYonedaObj k A))
    exact fun _ _ _ => Subsingleton.elim _ _
  | succ i =>
    intro x y hxy
    let E : (cochainSuccessor (P.linearYonedaObj k A)).X (i + 1) ≃ₗ[k] (P.X i ⟶ A) :=
      (cochainSuccessorXIso (P.linearYonedaObj k A) i).toLinearEquiv
    apply E.injective
    change repCofiberFst φ i ≫ E x = repCofiberFst φ i ≫ E y at hxy
    have h := congrArg (fun f => repCofiberInl φ i ≫ f) hxy
    have hid : repCofiberInl φ i ≫ repCofiberFst φ i = 𝟙 _ :=
      homotopyCofiber.inlX_fstX φ i (i + 1) rfl
    simpa only [← Category.assoc, hid, Category.id_comp] using h

theorem cofiberCochainSequence_exact_degree (i : ℕ) :
    ((cofiberCochainSequence φ A).map (eval _ _ i)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change ((repCofiber φ).X i ⟶ A) at f
  change repCofiberInr φ i ≫ f = 0 at hf
  cases i with
  | zero =>
    refine ⟨0, ?_⟩
    change 0 = f
    calc
      0 = repCofiberSnd φ 0 ≫ (repCofiberInr φ 0 ≫ f) := by rw [hf, comp_zero]
      _ = f := by
        rw [← Category.assoc, homotopyCofiber.sndX_inrX φ 0 (by simp)]
        exact Category.id_comp f
  | succ i =>
    let E : (cochainSuccessor (P.linearYonedaObj k A)).X (i + 1) ≃ₗ[k] (P.X i ⟶ A) :=
      (cochainSuccessorXIso (P.linearYonedaObj k A) i).toLinearEquiv
    refine ⟨E.symm (repCofiberInl φ i ≫ f), ?_⟩
    change repCofiberFst φ i ≫ E (E.symm (repCofiberInl φ i ≫ f)) = f
    rw [E.apply_symm_apply]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change f.hom ((repCofiberInl φ i).hom ((repCofiberFst φ i).hom x)) = f.hom x
    have h := congrArg f.hom (repCofiber_decompose φ i x)
    have hz : f.hom ((repCofiberInr φ (i + 1)).hom ((repCofiberSnd φ (i + 1)).hom x)) = 0 :=
      congrArg (fun u => u.hom ((repCofiberSnd φ (i + 1)).hom x)) hf
    simpa only [map_add, hz, add_zero] using h

theorem cofiberCochainSequence_shortExact : (cofiberCochainSequence φ A).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  exact
    { exact := cofiberCochainSequence_exact_degree φ A i
      mono_f := (ModuleCat.mono_iff_injective _).mpr (cofiberCochainInclusion_injective φ A i)
      epi_g := (ModuleCat.epi_iff_surjective _).mpr (cofiberCochainProjection_surjective φ A i) }

def cofiberCochainSectionComponent (i : ℕ) :
    (Q.linearYonedaObj k A).X i ⟶ (ChainComplex.linearYonedaObj (repCofiber φ) k A).X i :=
  ModuleCat.ofHom (Linear.leftComp k A (repCofiberSnd φ i))

theorem cofiberCochainSection_projection (i : ℕ) :
    cofiberCochainSectionComponent φ A i ≫ (cofiberCochainProjection φ A).f i = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (Q.X i ⟶ A) at f
  change repCofiberInr φ i ≫ (repCofiberSnd φ i ≫ f) = f
  rw [← Category.assoc, homotopyCofiber.inrX_sndX, Category.id_comp]

theorem cofiberCochainSection_d (i : ℕ) :
    cofiberCochainSectionComponent φ A i ≫
        (ChainComplex.linearYonedaObj (repCofiber φ) k A).d i (i + 1) =
      (repCochainPrecomp k φ A).f i ≫
        (cochainSuccessorXIso (P.linearYonedaObj k A) i).inv ≫
          (cofiberCochainInclusion φ A).f (i + 1) +
        (Q.linearYonedaObj k A).d i (i + 1) ≫ cofiberCochainSectionComponent φ A (i + 1) := by
  change _ = (repCochainPrecomp k φ A).f i ≫
      (cochainSuccessorXIso (P.linearYonedaObj k A) i).inv ≫
        ((cochainSuccessorXIso (P.linearYonedaObj k A) i).hom ≫
          ModuleCat.ofHom (Linear.leftComp k A (repCofiberFst φ i))) + _
  erw [Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (Q.X i ⟶ A) at f
  change (repCofiber φ).d (i + 1) i ≫ (repCofiberSnd φ i ≫ f) =
    repCofiberFst φ i ≫ (φ.f i ≫ f) + repCofiberSnd φ (i + 1) ≫ (Q.d (i + 1) i ≫ f)
  have hd : (repCofiber φ).d (i + 1) i ≫ repCofiberSnd φ i =
      repCofiberFst φ i ≫ φ.f i + repCofiberSnd φ (i + 1) ≫ Q.d (i + 1) i :=
    homotopyCofiber.d_sndX φ (i + 1) i rfl
  rw [← Category.assoc, hd, Preadditive.add_comp]
  simp only [Category.assoc]

end PolycyclicRecognition

end

end OAI
