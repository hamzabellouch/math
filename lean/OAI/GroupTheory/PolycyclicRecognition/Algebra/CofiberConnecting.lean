import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CofiberCochainSequence

namespace OAI

/-! # The connecting homomorphism of the mapping-cone cochain sequence -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {k : Type} [CommRing k]

theorem cochainSuccessor_liftCycles_homology
    (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) {M : ModuleCat k}
    (x : M ⟶ C.X i) (hx : x ≫ C.d i (i + 1) = 0)
    (hs : (x ≫ (cochainSuccessorXIso C i).inv) ≫
      (cochainSuccessor C).d (i + 1) (i + 2) = 0) :
    (cochainSuccessor C).liftCycles (x ≫ (cochainSuccessorXIso C i).inv) (i + 2) (by simp) hs ≫
        (cochainSuccessor C).homologyπ (i + 1) ≫ (cochainSuccessorHomologyIso C i).hom =
      C.liftCycles x (i + 1) (by simp) hx ≫ C.homologyπ i := by
  rw [cochainSuccessorHomologyIso_π, ← Category.assoc]
  congr 1
  apply (cancel_mono (C.iCycles i)).mp
  rw [Category.assoc, cochainSuccessorCyclesIso_iCycles, ← Category.assoc,
    liftCycles_i, Category.assoc, Iso.inv_hom_id, Category.comp_id, liftCycles_i]

variable {G : Type} [Group G] {P Q : ChainComplex (Rep k G) ℕ}
  (φ : P ⟶ Q) (A : Rep k G)

theorem cofiberCochain_connecting (i : ℕ) :
    (cofiberCochainSequence_shortExact φ A).δ i (i + 1) (by simp) ≫
        (cochainSuccessorHomologyIso (P.linearYonedaObj k A) i).hom =
      HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i := by
  let C := P.linearYonedaObj k A
  let D := Q.linearYonedaObj k A
  let E := cochainSuccessor C
  let u := repCochainPrecomp k φ A
  let x₃ := D.iCycles i
  let x₂ := x₃ ≫ cofiberCochainSectionComponent φ A i
  let x := x₃ ≫ u.f i
  let x₁ := x ≫ (cochainSuccessorXIso C i).inv
  have hx₃ : x₃ ≫ D.d i (i + 1) = 0 := D.iCycles_d i (i + 1)
  have hx : x ≫ C.d i (i + 1) = 0 := by
    dsimp only [x]
    rw [Category.assoc, u.comm i (i + 1), ← Category.assoc, hx₃, zero_comp]
  have hx₂ : x₂ ≫ (cofiberCochainProjection φ A).f i = x₃ := by
    dsimp only [x₂]
    rw [Category.assoc, cofiberCochainSection_projection, Category.comp_id]
  have hx₁ : x₁ ≫ (cofiberCochainInclusion φ A).f (i + 1) =
      x₂ ≫ (ChainComplex.linearYonedaObj (repCofiber φ) k A).d i (i + 1) := by
    dsimp only [x₁, x, x₂]
    simp only [Category.assoc]
    rw [cofiberCochainSection_d, Preadditive.comp_add]
    rw [← Category.assoc x₃ (D.d i (i + 1)), hx₃, zero_comp, add_zero]
  have hs : x₁ ≫ E.d (i + 1) (i + 2) = 0 := by
    dsimp only [x₁]
    rw [Category.assoc, cochainSuccessor_d]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, Preadditive.comp_neg, hx, neg_zero, zero_comp]
  have hd := (cofiberCochainSequence_shortExact φ A).δ_eq i (i + 1) (by simp)
    x₃ hx₃ x₂ hx₂ x₁ hx₁ (i + 2) (by simp)
  change D.liftCycles x₃ (i + 1) (by simp) hx₃ ≫ D.homologyπ i ≫
      (cofiberCochainSequence_shortExact φ A).δ i (i + 1) (by simp) =
    E.liftCycles x₁ (i + 2) (by simp) hs ≫ E.homologyπ (i + 1) at hd
  have hid : D.liftCycles x₃ (i + 1) (by simp) hx₃ = 𝟙 (D.cycles i) := by
    apply (cancel_mono (D.iCycles i)).mp
    rw [liftCycles_i, Category.id_comp]
  rw [hid, Category.id_comp] at hd
  apply (cancel_epi (D.homologyπ i)).mp
  erw [← Category.assoc, hd]
  calc
    _ = D.liftCycles x₃ (i + 1) (by simp) hx₃ ≫
        HomologicalComplex.cyclesMap u i ≫ C.homologyπ i := by
      calc
        _ = E.liftCycles x₁ (i + 2) (by simp) hs ≫
            (E.homologyπ (i + 1) ≫ (cochainSuccessorHomologyIso C i).hom) :=
          Category.assoc _ _ _
        _ = C.liftCycles x (i + 1) (by simp) hx ≫ C.homologyπ i :=
          cochainSuccessor_liftCycles_homology C i x hx hs
        _ = _ := by rw [← Category.assoc, liftCycles_comp_cyclesMap]
    _ = D.homologyπ i ≫ HomologicalComplex.homologyMap u i := by
      rw [hid, Category.id_comp, homologyπ_naturality]

end PolycyclicRecognition

end

end OAI
