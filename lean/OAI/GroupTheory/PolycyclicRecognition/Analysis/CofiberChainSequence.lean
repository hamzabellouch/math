import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChainSuccessor
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

namespace OAI

/-! # The split-in-each-degree sequence of a chain mapping cone -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {P Q : ChainComplex (ModuleCat ℤ) ℕ} (φ : P ⟶ Q)

private theorem chainDownSuccessorRel (i : ℕ) : (ComplexShape.down ℕ).Rel (i + 1) i := rfl

def cofiberChainProjectionComponent : ∀ i,
    (homotopyCofiber φ).X i ⟶ (chainSuccessor P).X i
  | 0 => 0
  | n + 1 => homotopyCofiber.fstX φ (n + 1) n (chainDownSuccessorRel n) ≫ (chainSuccessorXIso P n).inv

def cofiberChainProjection : homotopyCofiber φ ⟶ chainSuccessor P where
  f := cofiberChainProjectionComponent φ
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    cases j with
    | zero => exact (chainSuccessor_zero P).eq_of_tgt _ _
    | succ j =>
      change (homotopyCofiber.fstX φ (j + 2) (j + 1) (chainDownSuccessorRel (j + 1)) ≫
        (chainSuccessorXIso P (j + 1)).inv) ≫ _ =
          (homotopyCofiber φ).d (j + 2) (j + 1) ≫
            (homotopyCofiber.fstX φ (j + 1) j (chainDownSuccessorRel j) ≫ (chainSuccessorXIso P j).inv)
      rw [chainSuccessor_d]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have hd := homotopyCofiber.d_fstX φ (j + 2) (j + 1) j (chainDownSuccessorRel (j + 1)) (chainDownSuccessorRel j)
      change (homotopyCofiber φ).d (j + 2) (j + 1) ≫
        homotopyCofiber.fstX φ (j + 1) j (chainDownSuccessorRel j) = _ at hd
      rw [← Category.assoc ((homotopyCofiber φ).d _ _), hd]
      simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]

theorem cofiberChain_inclusion_projection :
    homotopyCofiber.inr φ ≫ cofiberChainProjection φ = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | zero => exact comp_zero
  | succ i =>
    change homotopyCofiber.inrX φ (i + 1) ≫
      (homotopyCofiber.fstX φ (i + 1) i (chainDownSuccessorRel i) ≫ (chainSuccessorXIso P i).inv) = 0
    simp

abbrev cofiberChainSequence : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (homotopyCofiber.inr φ) (cofiberChainProjection φ)
    (cofiberChain_inclusion_projection φ)

def cofiberChainDegreeSplitting (i : ℕ) :
    ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) i).mapShortComplex.obj
      (cofiberChainSequence φ)).Splitting where
  r := homotopyCofiber.sndX φ i
  s := match i with
    | 0 => 0
    | n + 1 => (chainSuccessorXIso P n).hom ≫ homotopyCofiber.inlX φ n (n + 1) (chainDownSuccessorRel n)
  f_r := homotopyCofiber.inrX_sndX φ i
  s_g := by
    cases i with
    | zero => exact (chainSuccessor_zero P).eq_of_src _ _
    | succ i =>
      change ((chainSuccessorXIso P i).hom ≫ homotopyCofiber.inlX φ i (i + 1) (chainDownSuccessorRel i)) ≫
        (homotopyCofiber.fstX φ (i + 1) i (chainDownSuccessorRel i) ≫ (chainSuccessorXIso P i).inv) = 𝟙 _
      simp
  id := by
    cases i with
    | zero =>
      change homotopyCofiber.sndX φ 0 ≫ homotopyCofiber.inrX φ 0 +
        (0 : homotopyCofiber.X φ 0 ⟶ homotopyCofiber.X φ 0) = 𝟙 _
      rw [homotopyCofiber.sndX_inrX φ 0 (by simp)]
      simp
    | succ i =>
      change homotopyCofiber.sndX φ (i + 1) ≫ homotopyCofiber.inrX φ (i + 1) +
        (homotopyCofiber.fstX φ (i + 1) i (chainDownSuccessorRel i) ≫ (chainSuccessorXIso P i).inv) ≫
          ((chainSuccessorXIso P i).hom ≫ homotopyCofiber.inlX φ i (i + 1) (chainDownSuccessorRel i)) = 𝟙 _
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      apply homotopyCofiber.ext_from_X φ i (i + 1) (chainDownSuccessorRel i)
      · simp
      · simp

theorem cofiberChainSequence_shortExact : (cofiberChainSequence φ).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  exact (cofiberChainDegreeSplitting φ i).shortExact

end PolycyclicRecognition

end

end OAI
