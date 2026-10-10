import OAI.NumberTheory.Ostmann.Construction.ConstituentScheduleEquiv
import OAI.NumberTheory.Ostmann.Construction.ScheduledPivotPartition

namespace OAI

/-! # The concrete pivot enumeration and its exact harmonic-prior dimension -/

namespace Ostmann

/-- A single pivot atom contributes exactly its original number of prime
constituents, even after the earlier copy steps. -/
noncomputable def pivotConstituentEquiv {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (p : I)
    (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p) :
    Fin (size p) ≃ CurrentPivotConstituent (fun i : Σ a, Fin (size a) => role i.1) n :=
  Equiv.ofBijective (fun k => ⟨⟨p, k⟩, hp⟩) (by
    constructor
    · intro i j he
      have he' : (⟨p, i⟩ : Σ a, Fin (size a)) = ⟨p, j⟩ := congrArg Subtype.val he
      exact eq_of_heq (Sigma.mk.inj_iff.mp he').2
    · rintro ⟨⟨i, k⟩, hi⟩
      have he : i = p := hu i hi
      subst i
      exact ⟨k, rfl⟩)

/-- Choose the first prime constituent solely to name the pivot column.
All constituents remain present in the grouped phase and prior. -/
def constituentPivot {I : Type*} (size : I → ℕ) (pivot : ℕ → I)
    (hsize : ∀ n, 0 < size (pivot n)) (n : ℕ) : Σ i, Fin (size i) :=
  ⟨pivot n, ⟨0, hsize n⟩⟩

theorem constituentPivot_role {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (pivot : ℕ → I) (hsize : ∀ n, 0 < size (pivot n))
    (hpivot : ∀ n, role (pivot n) = .pivot n) (n : ℕ) :
    (role ∘ Sigma.fst) (constituentPivot size pivot hsize n) = .pivot n := hpivot n

theorem currentPivotConstituent_card {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (p : I)
    (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p) :
    Nat.card (CurrentPivotConstituent (fun i : Σ a, Fin (size a) => role i.1) n) = size p := by
  rw [← Nat.card_congr (pivotConstituentEquiv role size n p hp hu)]
  exact Nat.card_fin _

end Ostmann

end OAI
