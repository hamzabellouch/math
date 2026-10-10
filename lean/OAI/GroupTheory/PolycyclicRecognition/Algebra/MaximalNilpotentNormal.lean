import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommutingSubgroupProduct
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace OAI

/-! # The centralizer of a maximal nilpotent normal subgroup

In a solvable group, a maximal nilpotent normal subgroup contains its own
centralizer. Descend the derived series of that centralizer: if the next term
lies in the maximal subgroup, the current term has class at most two and
centralizes it, so their product contradicts maximality unless it was already
contained. Finite integral cohomological dimension supplies the maximal
subgroup by the uniform nilpotence bound.
-/

namespace PolycyclicRecognition

open scoped commutatorElement

variable {G : Type} [Group G] [Group.IsSolvable G]

theorem centralizer_le_maximal_nilpotent_normal
    (F : Subgroup G) [F.Normal] [Group.IsNilpotent F]
    (hmax : ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → F ≤ N → N = F) :
    Subgroup.centralizer (F : Set G) ≤ F := by
  let C := Subgroup.centralizer (F : Set G)
  let D (i : ℕ) := (derivedSeries C i).map C.subtype
  have hDC (i : ℕ) : D i ≤ C := by
    rintro g ⟨a, _, rfl⟩
    exact a.property
  have hnormal (i : ℕ) : (D i).Normal := by
    dsimp [D]
    infer_instance
  have hstep (i : ℕ) (hnext : D (i + 1) ≤ F) : D i ≤ F := by
    have hDD : ⁅D i, D i⁆ ≤ F := by
      simpa only [D, derivedSeries_succ, Subgroup.map_commutator] using hnext
    have hcomm : ⁅F, D i⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mpr (hDC i))
    have hnilD : Group.IsNilpotent (D i) := by
      apply (Subgroup.isNilpotent_iff_lowerCentralSeries (D i)).mpr
      refine ⟨2, eq_bot_iff.mpr ?_⟩
      change ⁅⁅D i, D i⁆, D i⁆ ≤ ⊥
      exact (Subgroup.commutator_mono hDD le_rfl).trans (le_of_eq hcomm)
    let := hnilD
    let := hnormal i
    have hnil : Group.IsNilpotent (F ⊔ D i : Subgroup G) :=
      nilpotent_sup_of_commute F (D i) (fun f d => hDC i d.property f f.property)
    have heq : F ⊔ D i = F := hmax (F ⊔ D i) inferInstance hnil le_sup_left
    exact heq ▸ (show D i ≤ F ⊔ D i from le_sup_right)
  have hback : ∀ k i, D (i + k) ≤ F → D i ≤ F := by
    intro k
    induction k with
    | zero => intro i hi; exact hi
    | succ k ih =>
      intro i hi
      apply hstep
      apply ih (i + 1)
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hi
  obtain ⟨m, hm⟩ := Group.IsSolvable.solvable (G := C)
  have hterminal : D (0 + m) ≤ F := by simp only [D, Nat.zero_add, hm, Subgroup.map_bot, bot_le]
  have hzero := hback m 0 hterminal
  simpa only [D, derivedSeries_zero, Subgroup.map_top, Subgroup.range_subtype] using hzero

theorem exists_selfCentralizing_nilpotent_normal
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ F : Subgroup G, F.Normal ∧ Group.IsNilpotent F ∧
      Subgroup.centralizer (F : Set G) ≤ F := by
  obtain ⟨F, hFn, hF, hmax⟩ := exists_maximal_nilpotent_normal_subgroup hG
  let := hFn
  let := hF
  exact ⟨F, hFn, hF, centralizer_le_maximal_nilpotent_normal F hmax⟩

end PolycyclicRecognition

end OAI
