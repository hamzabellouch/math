import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import OAI.Algebra.Finitistic.Selection.TestModules

namespace OAI
namespace LittleFinitistic
open CategoryTheory

/-- The image of the central idempotent, expressed by its fixed vectors. -/
noncomputable def selectedSubmodule (M : ModuleCat SelectionRing) : Submodule SelectionRing M where
  carrier := {x | selectionIdempotent 0 • x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change selectionIdempotent 0 • x = x at hx
    change selectionIdempotent 0 • y = y at hy
    change selectionIdempotent 0 • (x+y) = x+y
    rw [smul_add,hx,hy]
  smul_mem' := by
    intro r x hx
    change selectionIdempotent 0 • (r • x) = r • x
    rw [← mul_smul,(selectionIdempotent_central 0 r).eq,mul_smul,hx]

theorem selectedSubmodule_eq_image (M : ModuleCat SelectionRing) (x : M) :
    x ∈ selectedSubmodule M ↔ ∃ y : M, selectionIdempotent 0 • y = x := by
  constructor
  · intro hx; exact ⟨x,hx⟩
  · rintro ⟨y,rfl⟩
    change selectionIdempotent 0 • (selectionIdempotent 0 • y) = _
    rw [← mul_smul,selectionIdempotent_square]

/-- Exactly H(Y) = restriction along alpha of eY from the manuscript. -/
noncomputable def selectionStep (M : ModuleCat SelectionRing) : ModuleCat SelectionRing :=
  (ModuleCat.restrictScalars (selectionAutomorphism 1).toRingHom).obj
    (ModuleCat.of SelectionRing (selectedSubmodule M))

noncomputable def selectionIterate (M : ModuleCat SelectionRing) : ℕ → ModuleCat SelectionRing
  | 0 => M
  | n+1 => selectionStep (selectionIterate M n)

def IdentityAt (M : ModuleCat SelectionRing) (q : ℕ) : Prop :=
  ∀ x : M, selectionIdempotent q • x = x

def ZeroAt (M : ModuleCat SelectionRing) (q : ℕ) : Prop :=
  ∀ x : M, selectionIdempotent q • x = 0

theorem identityAt_step (M : ModuleCat SelectionRing) (q : ℕ)
    (h : IdentityAt M (q+1)) : IdentityAt (selectionStep M) q := by
  intro x
  apply Subtype.ext
  change selectionAutomorphism 1 (selectionIdempotent q) • x.val = x.val
  rw [selectionAutomorphism_idempotent]
  exact_mod_cast h x.val

theorem zeroAt_step (M : ModuleCat SelectionRing) (q : ℕ)
    (h : ZeroAt M (q+1)) : ZeroAt (selectionStep M) q := by
  intro x
  apply Subtype.ext
  change selectionAutomorphism 1 (selectionIdempotent q) • x.val = 0
  rw [selectionAutomorphism_idempotent]
  exact_mod_cast h x.val

theorem selectionStep_nontrivial (M : ModuleCat SelectionRing) [Nontrivial M]
    (h : IdentityAt M 0) : Nontrivial (selectionStep M) := by
  obtain ⟨x,y,hxy⟩ := exists_pair_ne M
  exact ⟨⟨⟨x,h x⟩,⟨y,h y⟩,fun he => hxy (congrArg Subtype.val he)⟩⟩

theorem selectionStep_subsingleton (M : ModuleCat SelectionRing)
    (h : ZeroAt M 0) : Subsingleton (selectionStep M) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx : x.val = 0 := (x.property).symm.trans (h x.val)
  have hy : y.val = 0 := (y.property).symm.trans (h y.val)
  exact hx.trans hy.symm

theorem identityAt_iterate (M : ModuleCat SelectionRing) (n q : ℕ)
    (h : IdentityAt M (q+n)) : IdentityAt (selectionIterate M n) q := by
  induction n generalizing q with
  | zero => simpa [selectionIterate] using h
  | succ n ih =>
    apply identityAt_step
    apply ih
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem zeroAt_iterate (M : ModuleCat SelectionRing) (n q : ℕ)
    (h : ZeroAt M (q+n)) : ZeroAt (selectionIterate M n) q := by
  induction n generalizing q with
  | zero => simpa [selectionIterate] using h
  | succ n ih =>
    apply zeroAt_step
    apply ih
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

noncomputable def testObject (m : ℕ) [NeZero m] : ModuleCat SelectionRing :=
  ModuleCat.of SelectionRing (TestModule m)

theorem testObject_identityAt (m : ℕ) [NeZero m] (q : ℕ) (hq : q < m-1) :
    IdentityAt (testObject m) q := by
  intro x
  let i : Fin m := ⟨q,by omega⟩
  have hi : i ≠ lastIndex m := by
    intro h
    have hv := congrArg Fin.val h
    change q = m-1 at hv
    omega
  exact (testModule_idempotent_action m i x).trans (ite_eq_right hi)

theorem testObject_zeroAt (m : ℕ) [NeZero m] : ZeroAt (testObject m) (m-1) := by
  intro x
  exact (testModule_idempotent_action m (lastIndex m) x).trans (ite_eq_left rfl)

theorem selectionIterate_test_nontrivial (m : ℕ) [NeZero m] (n : ℕ) (hn : n < m) :
    Nontrivial (selectionIterate (testObject m) n) := by
  induction n with
  | zero => exact testModule_nontrivial m
  | succ n ih =>
    have := ih (by omega)
    apply selectionStep_nontrivial
    apply identityAt_iterate
    simpa only [Nat.zero_add] using testObject_identityAt m n (by omega)

theorem selectionIterate_test_subsingleton (m : ℕ) [NeZero m] :
    Subsingleton (selectionIterate (testObject m) m) := by
  have hm : m = (m-1)+1 := by have := NeZero.ne m; omega
  have hzero : ZeroAt (selectionIterate (testObject m) (m-1)) 0 :=
    zeroAt_iterate (testObject m) (m-1) 0 (by simpa using testObject_zeroAt m)
  have h := selectionStep_subsingleton _ hzero
  change Subsingleton (selectionIterate (testObject m) ((m-1)+1)) at h
  rwa [← hm] at h

/-- Exact extinction under the manuscript's actual selection operation H:
every earlier iterate is nonzero and the m-th iterate is zero. -/
theorem selection_extinction (m : ℕ) [NeZero m] :
    (∀ n < m, Nontrivial (selectionIterate (testObject m) n)) ∧
    Subsingleton (selectionIterate (testObject m) m) :=
  ⟨selectionIterate_test_nontrivial m,selectionIterate_test_subsingleton m⟩

noncomputable def complexObject (M : ModuleCat SelectionRing) : ModuleCat ℂ :=
  (ModuleCat.restrictScalars (algebraMap ℂ SelectionRing)).obj M

noncomputable def selectionStep_inclusion (M : ModuleCat SelectionRing) :
    complexObject (selectionStep M) →ₗ[ℂ] complexObject M where
  toFun x := x.val
  map_add' _ _ := rfl
  map_smul' c x := by
    change selectionAutomorphism 1 (algebraMap ℂ SelectionRing c) • x.val =
      algebraMap ℂ SelectionRing c • x.val
    rw [AlgEquiv.commutes]

theorem selectionStep_finiteDimensional (M : ModuleCat SelectionRing)
    [FiniteDimensional ℂ (complexObject M)] :
    FiniteDimensional ℂ (complexObject (selectionStep M)) :=
  FiniteDimensional.of_injective (selectionStep_inclusion M) Subtype.val_injective

theorem testObject_finiteDimensional (m : ℕ) [NeZero m] :
    FiniteDimensional ℂ (complexObject (testObject m)) := by
  let f : complexObject (testObject m) →ₗ[ℂ] TestModule m :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        have h : ∀ y : TestModule m, algebraMap ℂ SelectionRing c • y = c • y :=
          fun y => algebraMap_smul SelectionRing c y
        exact h x }
  exact FiniteDimensional.of_injective f (fun _ _ h => h)

theorem selectionIterate_test_finiteDimensional (m : ℕ) [NeZero m] (n : ℕ) :
    FiniteDimensional ℂ (complexObject (selectionIterate (testObject m) n)) := by
  induction n with
  | zero => exact testObject_finiteDimensional m
  | succ n ih =>
    have := ih
    exact selectionStep_finiteDimensional _
end LittleFinitistic

end OAI
