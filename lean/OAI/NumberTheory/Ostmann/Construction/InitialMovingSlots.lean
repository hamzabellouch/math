import OAI.NumberTheory.Ostmann.Construction.InitialFrozenAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTransferTransform

namespace OAI

/-! # The original two half-lists in the moving-slot order -/
namespace Ostmann
open scoped Classical BigOperators

abbrev InitialRetainedSlot (b r : ℕ) := Unit ⊕ (Fin b ⊕ Fin r)

/-- The left giant is `true`; fixed cells precede bulk in the moving template. -/
def initialRetainedIndexEquiv (b r : ℕ) :
    InitialRetainedSlot b r ⊕ InitialRetainedSlot b r ≃
      Bool ⊕ MovingRegularSlot 0 (r + r) (b + b) where
  toFun
    | .inl (.inl _) => .inl true
    | .inr (.inl _) => .inl false
    | .inl (.inr (.inl i)) => .inr ((), .inr (i.castAdd b))
    | .inr (.inr (.inl i)) => .inr ((), .inr (Fin.natAdd b i))
    | .inl (.inr (.inr i)) => .inr ((), .inl (i.castAdd r))
    | .inr (.inr (.inr i)) => .inr ((), .inl (Fin.natAdd r i))
  invFun
    | .inl true => .inl (.inl ())
    | .inl false => .inr (.inl ())
    | .inr (_, .inl i) => Fin.addCases (fun j => .inl (.inr (.inr j)))
        (fun j => .inr (.inr (.inr j))) i
    | .inr (_, .inr i) => Fin.addCases (fun j => .inl (.inr (.inl j)))
        (fun j => .inr (.inr (.inl j))) i
  left_inv := by
    rintro ((u | (i | i)) | (u | (i | i))) <;>
      simp only [Fin.addCases_left, Fin.addCases_right]
  right_inv := by
    rintro (a | ⟨u, i | i⟩)
    · cases a <;> rfl
    · cases u
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.addCases_left, Fin.addCases_right]
    · cases u
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.addCases_left, Fin.addCases_right]

/-- Separate all fixed spectators, then the two giants and the moving slots. -/
def initialCompleteIndexEquiv (b d r : ℕ) :
    Fin (d + d) ⊕ (Bool ⊕ MovingRegularSlot 0 (r + r) (b + b)) ≃
      Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) :=
  (Equiv.sumCongr finSumFinEquiv.symm (initialRetainedIndexEquiv b r).symm).trans
    ((Equiv.sumSumSumComm (Fin d) (Fin d) (InitialRetainedSlot b r)
      (InitialRetainedSlot b r)).trans
      ((Equiv.sumCongr (initialSpectatorSlotEquiv b d r)
        (initialSpectatorSlotEquiv b d r)).trans finSumFinEquiv))

noncomputable def initialMovingTuple {P : Type*} (b d r : ℕ)
    (sl sr : Fin d → P) (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P :=
  Sum.elim (Fin.append sl sr) (Sum.elim (fun a : Bool => if a then XL else XR) y) ∘
    (initialCompleteIndexEquiv b d r).symm

theorem initialCompleteIndexEquiv_assemble {P : Type*} (b d r : ℕ)
    (sl sr : Fin d → P) (yl yr : InitialRetainedSlot b r → P) :
    Fin.append (initialHalfAssemble b d r sl yl) (initialHalfAssemble b d r sr yr) ∘
      initialCompleteIndexEquiv b d r =
    Sum.elim (Fin.append sl sr)
      (Sum.elim yl yr ∘ (initialRetainedIndexEquiv b r).symm) := by
  funext i
  rcases i with i | i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [initialCompleteIndexEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
        Equiv.sumSumSumComm_apply, Equiv.sumAssoc, Equiv.sumComm, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, id_eq,
        finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, initialHalfAssemble, Function.comp_apply,
        Fin.append_left, Fin.append_right, Equiv.symm_apply_apply,
        Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Sum.swap_inl]
  · obtain ⟨j, rfl⟩ := (initialRetainedIndexEquiv b r).surjective i
    rcases j with j | j <;>
      simp only [initialCompleteIndexEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
        Equiv.sumSumSumComm_apply, Equiv.sumAssoc, Equiv.sumComm, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, id_eq,
        finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, initialHalfAssemble, Function.comp_apply,
        Fin.append_left, Fin.append_right, Equiv.symm_apply_apply,
        Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Sum.swap_inr]

theorem initial_reassembled_moving_tuple {P : Type*} (b d r : ℕ)
    (sl sr : Fin d → P) (z : Bool ⊕ MovingRegularSlot 0 (r + r) (b + b) → P) :
    Fin.append
      (initialHalfAssemble b d r sl (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inl))
      (initialHalfAssemble b d r sr (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inr)) =
    Sum.elim (Fin.append sl sr) z ∘ (initialCompleteIndexEquiv b d r).symm := by
  have h := initialCompleteIndexEquiv_assemble b d r sl sr
    (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inl)
    (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inr)
  have he : Sum.elim (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inl)
      (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inr) = z ∘ initialRetainedIndexEquiv b r := by
    funext i
    cases i <;> rfl
  rw [he] at h
  have hz : (z ∘ initialRetainedIndexEquiv b r) ∘ (initialRetainedIndexEquiv b r).symm = z := by
    funext i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [hz] at h
  funext i
  have hh := congrFun h ((initialCompleteIndexEquiv b d r).symm i)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hh

theorem initialMovingTuple_reindex {P : Type*} (b d r : ℕ)
    (sl sr : Fin d → P) (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    initialMovingTuple b d r sl sr XL XR y ∘ initialCompleteIndexEquiv b d r =
      Sum.elim (Fin.append sl sr) (Sum.elim (fun a : Bool => if a then XL else XR) y) := by
  funext i
  simp only [initialMovingTuple, Function.comp_apply, Equiv.symm_apply_apply]

theorem initialMovingTuple_product {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (sl sr : Fin d → P) (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    (∏ i, value (initialMovingTuple b d r sl sr XL XR y i)) =
      (∏ i, value (Fin.append sl sr i)) * (value XL * value XR * ∏ i, value (y i)) := by
  rw [← (initialCompleteIndexEquiv b d r).prod_comp]
  change (∏ i, value ((initialMovingTuple b d r sl sr XL XR y ∘
    initialCompleteIndexEquiv b d r) i)) = _
  rw [initialMovingTuple_reindex, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.prod_bool, Bool.false_eq_true,
    ite_false, ite_true]

end Ostmann

end OAI
