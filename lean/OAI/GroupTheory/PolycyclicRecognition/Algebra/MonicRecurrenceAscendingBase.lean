import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteOrbitAscendingBase
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianByFiniteContractor

namespace OAI

/-! # Integral action recurrences and the nilpotent finiteness endgame

A monic recurrence bounds the positive orbit of a finite generating set.
Two-sided orbit generation then gives an actual finitely generated ascending
base. The final theorem applies this criterion to the nilpotent abelianization;
it does not assume that FP-infinity supplies the recurrence.
-/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type} [CommGroup A]

theorem ascendingBase_of_monic_recurrence (α : MulAut A) (s : Finset A)
    {d : ℕ} (hd : 0 < d) (c : Fin d → ℤ)
    (hrec : ∀ x ∈ s, (α ^ d) x = ∏ i : Fin d, ((α ^ i.val) x) ^ c i)
    (hgen : (⨆ k : ℤ, (Subgroup.closure (s : Set A)).map (α ^ k).toMonoidHom) = ⊤) :
    HasFinitelyGeneratedAscendingBase α := by
  let C := Subgroup.closure (s : Set A)
  have hC : C.FG := ⟨s, rfl⟩
  apply ascendingBase_of_finite_orbit_relation α C hC hd ?_ hgen
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  change (α ^ d) x ∈ finiteOrbitSubgroup α C d
  rw [hrec x hx]
  apply Subgroup.prod_mem
  intro i _
  apply Subgroup.zpow_mem
  apply (le_iSup (fun j : Fin d => C.map (α ^ j.val).toMonoidHom) i)
  exact ⟨x, Subgroup.subset_closure hx, rfl⟩

variable {G : Type} [Group G] [Group.FG G]
open scoped IsMulCommutative

/-- A finite monic certificate in the actual abelianization suffices for the
already proved nilpotent-by-abelian-by-finite structural endgame. -/
theorem virtualSolvableFiniteDimension_of_abelianization_recurrence
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (H : Subgroup (G ⧸ N)) [H.Normal] [H.FiniteIndex] [IsMulCommutative H]
    (t : G) (s : Finset (Abelianization N)) {d : ℕ} (hd : 0 < d) (c : Fin d → ℤ)
    (hrec : ∀ x ∈ s,
      ((characteristicQuotientAut (commutator N) (MulAut.conjNormal (H := N) t)) ^ d) x =
        ∏ i : Fin d,
          (((characteristicQuotientAut (commutator N) (MulAut.conjNormal (H := N) t)) ^ i.val) x) ^ c i)
    (hgen : (⨆ k : ℤ, (Subgroup.closure (s : Set (Abelianization N))).map
      ((characteristicQuotientAut (commutator N) (MulAut.conjNormal (H := N) t)) ^ k).toMonoidHom) = ⊤) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  apply virtualSolvableFiniteDimension_of_abelianByFinite_contractor N H t
  exact ascendingBase_of_monic_recurrence _ s hd c hrec hgen

end PolycyclicRecognition

end

end OAI
