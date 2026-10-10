import OAI.NumberTheory.Ostmann.Characters.SourceTemplateListIndices
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateRoleIndices

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template

abbrev sourceHalfSize {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :=
  (m+1)+configCellCount cfg

theorem roleListPositionEquiv_get {k : ℕ} (cfg : SourceConfiguration k)
    (j : Fin (k+1)) (a : Fin (cfg.2 j).length) :
    (List.ofFn cfg.2).flatten.get (roleListPositionEquiv cfg ⟨j,a⟩) = (cfg.2 j).get a := by
  unfold roleListPositionEquiv
  rw [Equiv.trans_apply, listFlattenPositionEquiv_get]
  simp only [Equiv.sigmaCongr, Equiv.trans_apply, Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft,
    Equiv.coe_fn_mk, List.get_eq_getElem, List.getElem_ofFn, finCongr_apply, Fin.val_cast]

def cellCoordinateEquiv {k : ℕ} (cfg : SourceConfiguration k) :
    (Fin (2*k) ⊕ (Σ j : Fin (k+1), Fin (cfg.2 j).length)) ≃ Fin (configCellCount cfg) :=
  (Equiv.sumCongr (Equiv.refl _) (roleListPositionEquiv cfg)).trans
    (finSumFinEquiv.trans (finCongr (by
      simp only [configCellCount, configurationIndices, List.length_append, List.length_ofFn])))

theorem cellCoordinateEquiv_anchor {k : ℕ} (cfg : SourceConfiguration k) (a : Fin (2*k)) :
    configCellIndices cfg (cellCoordinateEquiv cfg (.inl a)) = cfg.1 a := by
  have ha : a.val < (List.ofFn cfg.1).length := by simpa only [List.length_ofFn] using a.isLt
  change (List.ofFn cfg.1 ++ (List.ofFn cfg.2).flatten)[a.val] = cfg.1 a
  rw [List.getElem_append_left ha]
  simp only [List.getElem_ofFn]

theorem cellCoordinateEquiv_list {k : ℕ} (cfg : SourceConfiguration k)
    (j : Fin (k+1)) (a : Fin (cfg.2 j).length) :
    configCellIndices cfg (cellCoordinateEquiv cfg (.inr ⟨j,a⟩)) = (cfg.2 j).get a := by
  have hv : 2*k+(roleListPositionEquiv cfg ⟨j,a⟩).val <
      (List.ofFn cfg.1 ++ (List.ofFn cfg.2).flatten).length := by
    simpa only [List.length_append, List.length_ofFn] using
      Nat.add_lt_add_left (roleListPositionEquiv cfg ⟨j,a⟩).isLt (2*k)
  change (List.ofFn cfg.1 ++ (List.ofFn cfg.2).flatten)[2*k+(roleListPositionEquiv cfg ⟨j,a⟩).val] = _
  rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega)]
  simpa only [List.length_ofFn, Nat.add_sub_cancel_left, List.get_eq_getElem] using
    roleListPositionEquiv_get cfg j a

def halfSourceCoordinateEquiv {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    HalfSourceCoordinates cfg m ≃ Fin (sourceHalfSize cfg m) :=
  (Equiv.sumCongr (Equiv.refl _) (cellCoordinateEquiv cfg)).trans finSumFinEquiv

def halfRoleIndexEquiv {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    HalfRoleConstituent cfg m ≃ Fin (sourceHalfSize cfg m) :=
  (halfRoleCoordinateEquiv cfg m).trans (halfSourceCoordinateEquiv cfg m)

def sourceDoubleIndexEquiv (b : ℕ) : (Fin b × Bool) ≃ Fin (b+b) :=
  (Equiv.prodCongr (Equiv.refl _) Equiv.boolNot).trans
    ((pairBoolSumEquiv (Fin b)).trans finSumFinEquiv)

def sourceIndexEquiv {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    SourceConstituent cfg m ≃ Fin (sourceHalfSize cfg m + sourceHalfSize cfg m) :=
  (constituentHalfEquiv cfg m).trans
    ((Equiv.prodCongr (halfRoleIndexEquiv cfg m) (Equiv.refl Bool)).trans
      (sourceDoubleIndexEquiv (sourceHalfSize cfg m)))

@[simp] theorem sourceIndexEquiv_word_true {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (a : Fin (m+1)) :
    sourceIndexEquiv cfg m ⟨(.word,true),a⟩ =
      Fin.castAdd (sourceHalfSize cfg m) (Fin.castAdd (configCellCount cfg) a) := by
  apply Fin.ext
  rfl

@[simp] theorem sourceIndexEquiv_word_false {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (a : Fin (m+1)) :
    sourceIndexEquiv cfg m ⟨(.word,false),a⟩ =
      Fin.natAdd (sourceHalfSize cfg m) (Fin.castAdd (configCellCount cfg) a) := by
  apply Fin.ext
  rfl

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
