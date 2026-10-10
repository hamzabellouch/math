import OAI.NumberTheory.Ostmann.Characters.TemplateParityActionsBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template.ParityActions
attribute [local instance] Classical.propDecidable

abbrev BulkSlot (k n m : ℕ) := Word k (n+1) × Fin m

def wordPermutation (k n : ℕ) (σ : (ε : ℤˣ) → Equiv.Perm (ParityFiber k n ε)) :
    Equiv.Perm (Word k (n+1)) :=
  (Equiv.sigmaFiberEquiv (fun w : Word k (n+1) => rowSign k (n+1) w.val)).symm.trans
    ((Equiv.sigmaCongrRight σ).trans
      (Equiv.sigmaFiberEquiv (fun w : Word k (n+1) => rowSign k (n+1) w.val)))

@[simp] theorem wordPermutation_apply (k n : ℕ)
    (σ : (ε : ℤˣ) → Equiv.Perm (ParityFiber k n ε)) (w : Word k (n+1)) :
    wordPermutation k n σ w = (σ (rowSign k (n+1) w.val) ⟨w,rfl⟩).val := rfl

@[simp] theorem wordPermutation_onFiber (k n : ℕ)
    (σ : (ε : ℤˣ) → Equiv.Perm (ParityFiber k n ε)) (ε : ℤˣ)
    (w : ParityFiber k n ε) : wordPermutation k n σ w.val = (σ ε w).val := by
  rcases w with ⟨w,hw⟩
  subst ε
  rfl

@[simp] theorem wordPermutation_sign (k n : ℕ)
    (σ : (ε : ℤˣ) → Equiv.Perm (ParityFiber k n ε)) (w : Word k (n+1)) :
    rowSign k (n+1) (wordPermutation k n σ w).val = rowSign k (n+1) w.val :=
  (σ _ ⟨w,rfl⟩).property

theorem wordPermutation_mul (k n : ℕ)
    (σ ρ : (ε : ℤˣ) → Equiv.Perm (ParityFiber k n ε)) :
    wordPermutation k n (σ*ρ) = wordPermutation k n σ*wordPermutation k n ρ := by
  apply Equiv.ext
  intro w
  let z : ParityFiber k n (rowSign k (n+1) w.val) := ⟨w,rfl⟩
  change wordPermutation k n (σ*ρ) z.val =
    wordPermutation k n σ (wordPermutation k n ρ z.val)
  rw [wordPermutation_onFiber k n (σ*ρ) _ z,
    wordPermutation_onFiber k n ρ _ z,
    wordPermutation_onFiber k n σ _ (ρ _ z)]
  rfl

def bulkPermutation (k n m : ℕ) (σ : Reassignments k n m) : Equiv.Perm (BulkSlot k n m) :=
  Equiv.prodCongrLeft (fun i => wordPermutation k n (σ i))

@[simp] theorem bulkPermutation_apply (k n m : ℕ) (σ : Reassignments k n m)
    (w : Word k (n+1)) (i : Fin m) :
    bulkPermutation k n m σ (w,i) = (wordPermutation k n (σ i) w,i) := rfl

@[simp] theorem bulkPermutation_position (k n m : ℕ) (σ : Reassignments k n m)
    (z : BulkSlot k n m) : (bulkPermutation k n m σ z).2 = z.2 := rfl

@[simp] theorem bulkPermutation_symm_position (k n m : ℕ) (σ : Reassignments k n m)
    (z : BulkSlot k n m) : ((bulkPermutation k n m σ).symm z).2 = z.2 := rfl

@[simp] theorem bulkPermutation_sign (k n m : ℕ) (σ : Reassignments k n m)
    (z : BulkSlot k n m) :
    rowSign k (n+1) (bulkPermutation k n m σ z).1.val = rowSign k (n+1) z.1.val :=
  wordPermutation_sign k n (σ z.2) z.1

theorem bulkPermutation_injective (k n m : ℕ) : Function.Injective (bulkPermutation k n m) := by
  intro σ ρ h
  funext i ε
  apply Equiv.ext
  intro w
  apply Subtype.ext
  have hh := congrArg Prod.fst (Equiv.congr_fun h (w.val,i))
  change wordPermutation k n (σ i) w.val = wordPermutation k n (ρ i) w.val at hh
  exact (wordPermutation_onFiber k n (σ i) ε w).symm.trans
    (hh.trans (wordPermutation_onFiber k n (ρ i) ε w))

def bulkPermutationHom (k n m : ℕ) : Reassignments k n m →* Equiv.Perm (BulkSlot k n m) where
  toFun := bulkPermutation k n m
  map_one' := by
    apply Equiv.ext
    intro z
    rcases z with ⟨w,i⟩
    change (wordPermutation k n (fun _ => 1) w,i) = (w,i)
    rfl
  map_mul' σ ρ := by
    apply Equiv.ext
    intro z
    rcases z with ⟨w,i⟩
    change (wordPermutation k n (σ i*ρ i) w,i) =
      (wordPermutation k n (σ i) (wordPermutation k n (ρ i) w),i)
    rw [wordPermutation_mul,Equiv.Perm.mul_apply]

theorem exists_distinct_destinations (k n m : ℕ) {σ ρ : Reassignments k n m}
    (h : σ ≠ ρ) : ∃ z : BulkSlot k n m,
      (bulkPermutation k n m σ z).1 ≠ (bulkPermutation k n m ρ z).1 ∧
      (bulkPermutation k n m σ z).2 = (bulkPermutation k n m ρ z).2 ∧
      rowSign k (n+1) (bulkPermutation k n m σ z).1.val =
        rowSign k (n+1) (bulkPermutation k n m ρ z).1.val := by
  have hn : bulkPermutation k n m σ ≠ bulkPermutation k n m ρ :=
    fun he => h (bulkPermutation_injective k n m he)
  have hex : ∃ z, bulkPermutation k n m σ z ≠ bulkPermutation k n m ρ z := by
    by_contra hall
    push Not at hall
    exact hn (Equiv.ext hall)
  obtain ⟨z,hz⟩ := hex
  refine ⟨z,?_,rfl,?_⟩
  · intro he
    exact hz (Prod.ext he rfl)
  · rw [bulkPermutation_sign,bulkPermutation_sign]

end Ostmann.Characters.Template.ParityActions

end

end OAI
