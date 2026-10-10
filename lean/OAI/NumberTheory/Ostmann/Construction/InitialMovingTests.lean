import OAI.NumberTheory.Ostmann.Construction.InitialSpectatorFourier
import OAI.NumberTheory.Ostmann.Construction.HalfPrimeInitialAmplitude
import OAI.NumberTheory.Ostmann.Characters.NormalizedResidueFamily

namespace OAI

/-! # The original giant and regular tests under the moving-slot reindexing -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialGiantFlag (b d r : ℕ) :
    Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → Bool :=
  let a : Fin (b + (d + r) + 1) → Bool := Fin.cons true (fun _ => false)
  Fin.append a a

theorem initialGiantFlag_reindex (b d r : ℕ)
    (i : Fin (d + d) ⊕ (Bool ⊕ MovingRegularSlot 0 (r + r) (b + b))) :
    initialGiantFlag b d r (initialCompleteIndexEquiv b d r i) =
      Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (fun _ => false)) i := by
  let a : InitialRetainedSlot b r → Bool := Sum.elim (fun _ => true) (fun _ => false)
  have hhalf : initialHalfAssemble b d r (fun _ => false) a =
      Fin.cons true (fun _ => false) := by
    funext j
    obtain ⟨i, rfl⟩ := (initialSpectatorSlotEquiv b d r).surjective j
    rcases i with i | (u | (i | i)) <;>
      simp [initialHalfAssemble, initialSpectatorSlotEquiv, a]
  have h := initialCompleteIndexEquiv_assemble b d r (fun _ => false) (fun _ => false) a a
  rw [hhalf] at h
  have hret : Sum.elim a a ∘ (initialRetainedIndexEquiv b r).symm =
      Sum.elim (fun _ : Bool => true) (fun _ => false) := by
    funext j
    obtain ⟨i, rfl⟩ := (initialRetainedIndexEquiv b r).surjective j
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rcases i with ((u | (i | i)) | (u | (i | i))) <;> rfl
  rw [hret] at h
  have ha : Fin.append (fun _ : Fin d => false) (fun _ : Fin d => false) =
      (fun _ : Fin (d + d) => false) := by
    funext j
    exact Fin.addCases (fun _ => Fin.append_left _ _ _) (fun _ => Fin.append_right _ _ _) j
  rw [ha] at h
  exact congrFun h i

theorem initial_full_physical_test (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (S : (p : P) → Finset (ZMod (p : ℕ))) (fav : P → Bool)
    (i : Fin ((b + (d + r) + 1) + (b + (d + r) + 1))) (p : P) :
    Fin.append (primeHalfTests (n := b + (d + r)) P S fav)
      (primeHalfTests (n := b + (d + r)) P S fav) i p =
    primePhysicalTest (S p) (initialGiantFlag b d r i) (fav p) := by
  let flag : Fin (b + (d + r) + 1) → Bool := Fin.cons true (fun _ => false)
  have hh (j : Fin (b + (d + r) + 1)) :
      primeHalfTests P S fav j p =
        primePhysicalTest (S p) (flag j) (fav p) := by
    refine Fin.cases ?_ (fun k => ?_) j <;>
      simp only [flag, primeHalfTests, Fin.cons_zero, Fin.cons_succ, primePhysicalTest,
        Bool.false_eq_true, ↓reduceIte]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [initialGiantFlag, Fin.append_left] using hh j
  · simpa only [initialGiantFlag, Fin.append_right] using hh j

/-- The complete transform uses exactly the manuscript's phase at the two
original giant positions and its normalized residue transform elsewhere. -/
theorem initial_full_transform (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool)
    (x : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) (s : ℤ) :
    movingRegularTransform (fun i => (x i : ℕ))
      (fun i => densityFourier (Fin.append
        (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p))
        (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p)) i (x i))) 1 s =
    movingTaggedTransform (fun i => (x i : ℕ)) (initialGiantFlag b d r)
      (normalizedResidueFamily S) (normalizedResidueFamily S) fav 1 s := by
  unfold movingRegularTransform movingTaggedTransform
  apply Finset.prod_congr rfl
  intro i _
  dsimp only
  rw [initial_full_physical_test, primePhysicalTest_fourier, normalizedResidueFamily_eq]
  split_ifs <;> rfl

/-- Exact factorization of the original transform after fixing spectators. -/
theorem initial_moving_transform (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool)
    (sl sr : Fin d → P) (XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ) :
    let x := initialMovingTuple b d r sl sr XL XR y
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append sl sr i : P) : ℕ)
    let p := Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ))
    movingRegularTransform (fun i => (x i : ℕ))
      (fun i => densityFourier (Fin.append
        (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p))
        (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p)) i (x i))) 1 s =
      (∏ i, normalizedResidueFamily S (q i)
        ((s : ZMod (q i)) * (((∏ j, p j) * tupleCofactor q i : ℕ) : ZMod (q i))⁻¹)) *
      movingTaggedTransform p (Sum.elim (fun _ => true) (fun _ => false))
        (normalizedResidueFamily S) (normalizedResidueFamily S) fav (∏ i, q i) s := by
  intro x q p
  rw [initial_full_transform]
  have hx : (fun i => (x i : ℕ)) ∘ initialCompleteIndexEquiv b d r = Sum.elim q p := by
    funext i
    change ((initialMovingTuple b d r sl sr XL XR y ∘ initialCompleteIndexEquiv b d r) i : ℕ) = _
    rw [initialMovingTuple_reindex]
    rcases i with i | (a | i)
    · rfl
    · cases a <;> rfl
    · rfl
  have ht : initialGiantFlag b d r ∘ initialCompleteIndexEquiv b d r =
      Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (fun _ => false)) := by
    funext i
    exact initialGiantFlag_reindex b d r i
  have he := movingTaggedTransform_equiv (initialCompleteIndexEquiv b d r)
    (fun i => (x i : ℕ)) (fun i => NeZero.ne (x i : ℕ)) (initialGiantFlag b d r)
    (normalizedResidueFamily S) (normalizedResidueFamily S) fav 1 s
  rw [hx, ht] at he
  rw [← he, movingTaggedTransform_spectator_split]
  · simp only [one_mul]
  · intro i
    exact NeZero.ne ((Fin.append sl sr i : P) : ℕ)
  · rintro (a | i)
    · cases a
      · exact NeZero.ne (XR : ℕ)
      · exact NeZero.ne (XL : ℕ)
    · exact NeZero.ne (y i : ℕ)

theorem initial_moving_tagged_zero (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b r : ℕ) (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool)
    (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) (D : ℕ) :
    movingTaggedTransform
      (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ)))
      (Sum.elim (fun _ => true) (fun _ => false))
      (normalizedResidueFamily S) (normalizedResidueFamily S) fav D 0 = 0 := by
  unfold movingTaggedTransform
  apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl true))
  let c : ZMod (XL : ℕ) := ((D * tupleCofactor
    (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ)))
    (Sum.inl true) : ℕ) : ZMod (XL : ℕ))⁻¹
  change (if fav (XL : ℕ) then complexUnitPhase (normalizedResidueFamily S (XL : ℕ)
    (((0 : ℤ) : ZMod (XL : ℕ)) * c)) else 0) = 0
  have hz : ((0 : ℤ) : ZMod (XL : ℕ)) * c = 0 := by simp
  rw [hz, normalizedResidueFamily_zero, complexUnitPhase_zero]
  split_ifs <;> rfl

end Ostmann

end OAI
