import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCentralLayerUnipotence
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RationalQuasiUnipotentFiltration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.VirtualNilpotentByAbelian
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Nilpotent

namespace OAI

/-! # Finite-index nilpotence from the central layers

For a polycyclic solvable group of finite integral dimension, polynomial
growth forces unipotent action on every central layer of its maximal
nilpotent normal subgroup. A finite intersection of the resulting normal
subgroups acts nilpotently on all layers and is itself nilpotent.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem centralLayer_finite_free (F : Subgroup G) [F.Normal]
    [Group.IsNilpotent F] [Group.FG F] (hF : HasNoNontrivialTorsion F) (i : ℕ) :
    Module.Finite ℤ (Additive (CentralLayer F i)) ∧
      Module.Free ℤ (Additive (CentralLayer F i)) := by
  have hp := isPolycyclic_of_finitelyGenerated_nilpotent
    (F ⧸ Subgroup.upperCentralSeries F i)
  let : Group.FG (CentralLayer F i) :=
    (hp.of_injective (Subgroup.center _).subtype Subtype.val_injective).finitelyGenerated
  let : Module.Finite ℤ (Additive (CentralLayer F i)) :=
    Module.Finite.iff_addGroup_fg.mpr inferInstance
  have htf : HasNoNontrivialTorsion (CentralLayer F i) :=
    (nilpotent_upperCentralQuotient_torsionFree hF i).of_injective
      (Subgroup.center _).subtype Subtype.val_injective
  let : IsMulTorsionFree (CentralLayer F i) :=
    isMulTorsionFree_iff_not_isOfFinOrder.mpr (by
      intro a ha hf
      exact ha (htf a (orderOf a) (ne_of_gt hf.orderOf_pos) (pow_orderOf_eq_one a)))
  let : Module.IsTorsionFree ℤ (Additive (CentralLayer F i)) := inferInstance
  exact ⟨inferInstance, inferInstance⟩

theorem polynomial_growth_nilpotent_finiteIndex_of_finiteDimension
    [DecidableEq G] [Group.IsSolvable G]
    (hpoly : IsPolycyclic G) (hcd : HasFiniteIntegralCohomologicalDimension G)
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d) :
    Group.IsVirtuallyNilpotent G := by
  classical
  let : Group.FG G := hpoly.finitelyGenerated
  obtain ⟨F, hFn, hFnil, hmax⟩ := exists_maximal_nilpotent_normal_subgroup hcd
  let := hFn
  let := hFnil
  let : Group.FG F := (hpoly.of_injective F.subtype Subtype.val_injective).finitelyGenerated
  let c := Group.nilpotencyClass F
  have hall (i : Fin c) : ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧ ∃ n : ℕ,
      linearActionFiltration (fun a : H => (rationalUpperCentralAction F i a).toLinearMap - 1)
        n = ⊥ := by
    obtain ⟨hfin, hfree⟩ := centralLayer_finite_free F (hcd.subgroup F).torsionFree i
    let := hfin
    let := hfree
    let : Module.Finite ℚ (RationalAbelianSpace (CentralLayer F i)) := inferInstance
    exact rationalAction_finiteIndex_unipotent_filtration (rationalUpperCentralAction F i)
      (polynomial_growth_centralLayer_unipotent_power F S hS hgen hvol i)
  choose H hHn hHi n hn using hall
  let K : Subgroup G := ⨅ i, H i
  let : K.Normal := Subgroup.normal_iInf_normal hHn
  have hKi : K.FiniteIndex := Subgroup.finiteIndex_iInf hHi
  refine ⟨K, ?_, hKi⟩
  apply nilpotent_of_unipotent_central_layers F (hcd.subgroup F).torsionFree K
    (centralizer_le_maximal_nilpotent_normal F hmax)
  intro i hi
  let j : Fin c := ⟨i, hi⟩
  let inc : K →* H j := Subgroup.inclusion (iInf_le H j)
  refine ⟨n j, linearActionFiltration_eq_bot_of_word_zero _ _ ?_⟩
  intro w hw
  have he : actionOperatorWord
      (fun a : K => (rationalUpperCentralAction F i a).toLinearMap - 1) w =
      actionOperatorWord
        (fun a : H j => (rationalUpperCentralAction F i a).toLinearMap - 1) (w.map inc) := by
    clear hw
    induction w with
    | nil => rfl
    | cons a w ih =>
      change _ * actionOperatorWord _ w = _ * actionOperatorWord _ (w.map inc)
      rw [ih]
      rfl
  rw [he]
  exact actionOperatorWord_zero_of_filtration_eq_bot _ (hn j) _
    (by simpa only [List.length_map] using hw)

end PolycyclicRecognition

end

end OAI
