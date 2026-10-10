import OAI.GroupTheory.PolycyclicRecognition.Analysis.CofiberChainSequence

namespace OAI

/-! # The connecting map of the chain mapping-cone sequence -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex

theorem chainSuccessor_liftCycles_homology
    (C : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) {M : ModuleCat ℤ}
    (x : M ⟶ C.X i) (hx : x ≫ C.d i (i - 1) = 0)
    (hs : (x ≫ (chainSuccessorXIso C i).inv) ≫
      (chainSuccessor C).d (i + 1) i = 0) :
    (chainSuccessor C).liftCycles (x ≫ (chainSuccessorXIso C i).inv) i (by simp) hs ≫
        (chainSuccessor C).homologyπ (i + 1) ≫ (chainSuccessorHomologyIso C i).hom =
      C.liftCycles x (i - 1) (by cases i <;> simp) hx ≫ C.homologyπ i := by
  rw [chainSuccessorHomologyIso_π, ← Category.assoc]
  congr 1
  apply (cancel_mono (C.iCycles i)).mp
  rw [Category.assoc, chainSuccessorCyclesIso_iCycles, ← Category.assoc,
    liftCycles_i, Category.assoc, Iso.inv_hom_id, Category.comp_id, liftCycles_i]

variable {P Q : ChainComplex (ModuleCat ℤ) ℕ} (φ : P ⟶ Q)

theorem cofiberChain_connecting (i : ℕ) :
    (chainSuccessorHomologyIso P i).inv ≫
        (cofiberChainSequence_shortExact φ).δ (i + 1) i (by simp) =
      HomologicalComplex.homologyMap φ i := by
  have hid : P.liftCycles (P.iCycles i) (i - 1) (by cases i <;> simp)
      (P.iCycles_d i (i - 1)) = 𝟙 _ := by
    have he : P.liftCycles (P.iCycles i) (i - 1) (by cases i <;> simp)
        (P.iCycles_d i (i - 1)) ≫ P.iCycles i = (𝟙 (P.cycles i)) ≫ P.iCycles i := by
      rw [liftCycles_i, Category.id_comp]
    exact (cancel_mono (P.iCycles i)).mp he
  let x₃ := P.iCycles i ≫ (chainSuccessorXIso P i).inv
  let x₂ := P.iCycles i ≫ homotopyCofiber.inlX φ i (i + 1) (by simp)
  let x₁ := P.iCycles i ≫ φ.f i
  have hx₃ : x₃ ≫ (chainSuccessor P).d (i + 1) i = 0 := by
    cases i with
    | zero => exact (chainSuccessor_zero P).eq_of_tgt _ _
    | succ i =>
      dsimp only [x₃]
      rw [chainSuccessor_d]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, Preadditive.comp_neg, P.iCycles_d, neg_zero, zero_comp]
  have hx₂ : x₂ ≫ (cofiberChainProjection φ).f (i + 1) = x₃ := by
    dsimp only [x₂, x₃, cofiberChainProjection, cofiberChainProjectionComponent]
    simp only [Category.assoc, homotopyCofiber.inlX_fstX_assoc]
  have hx₁ : x₁ ≫ (homotopyCofiber.inr φ).f i =
      x₂ ≫ (homotopyCofiber φ).d (i + 1) i := by
    dsimp only [x₁, x₂]
    change (P.iCycles i ≫ φ.f i) ≫ homotopyCofiber.inrX φ i =
      (P.iCycles i ≫ homotopyCofiber.inlX φ i (i + 1) (by simp)) ≫
        homotopyCofiber.d φ (i + 1) i
    cases i with
    | zero =>
      have hd := homotopyCofiber.inlX_d' φ 1 0 (by simp) (by simp)
      exact (congrArg (fun f => P.iCycles 0 ≫ f) hd).symm
    | succ i =>
      have hd := homotopyCofiber.inlX_d φ (i + 1 + 1) (i + 1) i (by simp) (by simp)
      have he := congrArg (fun f => P.iCycles (i + 1) ≫ f) hd
      simpa only [Preadditive.comp_add, Preadditive.comp_neg, ← Category.assoc,
        P.iCycles_d, neg_zero, zero_comp, zero_add, Nat.add_assoc] using he.symm
  have hx : x₁ ≫ Q.d i (i - 1) = 0 := by
    dsimp only [x₁]
    rw [Category.assoc, φ.comm i (i - 1), ← Category.assoc, P.iCycles_d, zero_comp]
  have hd := (cofiberChainSequence_shortExact φ).δ_eq (i + 1) i (by simp)
    x₃ hx₃ x₂ hx₂ x₁ hx₁ (i - 1) (by cases i <;> simp)
  have hs := chainSuccessor_liftCycles_homology P i (P.iCycles i)
    (P.iCycles_d i (i - 1)) hx₃
  rw [hid, Category.id_comp] at hs
  apply (cancel_epi (P.homologyπ i)).mp
  rw [← Category.assoc, ← hs]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hd]
  have hs' := congrArg (fun f => f ≫ HomologicalComplex.homologyMap φ i) hs
  simp only [Category.assoc] at hs'
  rw [hs', HomologicalComplex.homologyπ_naturality φ i]
  congr 1

end PolycyclicRecognition

end

end OAI
