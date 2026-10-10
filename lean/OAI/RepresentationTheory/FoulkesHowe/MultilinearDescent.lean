import Mathlib

namespace OAI

noncomputable section

namespace Problem346

open Function

universe uR uI uM uN uW

variable {R : Type uR} [Semiring R] {I : Type uI}
    {M : I → Type uM} {N : I → Type uN} {W : Type uW}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    [AddCommMonoid W] [Module R W]

/-- A multilinear map constant on the fibers of coordinatewise surjections descends. -/
def multilinearDescend
    (q : ∀ i, M i →ₗ[R] N i) (hq : ∀ i, Surjective (q i))
    (f : MultilinearMap R M W)
    (hf : ∀ x y, (∀ i, q i (x i) = q i (y i)) → f x = f y) :
    MultilinearMap R N W where
  toFun y := f (fun i => surjInv (hq i) (y i))
  map_update_add' y i x z := by
    let s : ∀ i, N i → M i := fun i => surjInv (hq i)
    have hs : ∀ i x, q i (s i x) = x := fun i x => surjInv_eq (hq i) x
    have h (t : N i) :
        f (fun j => s j (update y i t j)) = f (update (fun j => s j (y j)) i (s i t)) := by
      apply hf
      intro j
      by_cases hji : j = i
      · subst j; simp [hs]
      · simp [hji, hs]
    change f (fun j => s j (update y i (x + z) j)) =
      f (fun j => s j (update y i x j)) + f (fun j => s j (update y i z j))
    rw [h, h, h]
    have hadd :
        f (update (fun j => s j (y j)) i (s i (x + z))) =
        f (update (fun j => s j (y j)) i (s i x + s i z)) := by
      apply hf
      intro j
      by_cases hji : j = i
      · subst j; simp [hs]
      · simp [hji]
    rw [hadd, f.map_update_add]
  map_update_smul' y i c x := by
    let s : ∀ i, N i → M i := fun i => surjInv (hq i)
    have hs : ∀ i x, q i (s i x) = x := fun i x => surjInv_eq (hq i) x
    have h (t : N i) :
        f (fun j => s j (update y i t j)) = f (update (fun j => s j (y j)) i (s i t)) := by
      apply hf
      intro j
      by_cases hji : j = i
      · subst j; simp [hs]
      · simp [hji, hs]
    change f (fun j => s j (update y i (c • x) j)) =
      c • f (fun j => s j (update y i x j))
    rw [h, h]
    have hsmul :
        f (update (fun j => s j (y j)) i (s i (c • x))) =
        f (update (fun j => s j (y j)) i (c • s i x)) := by
      apply hf
      intro j
      by_cases hji : j = i
      · subst j; simp [hs]
      · simp [hji]
    rw [hsmul, f.map_update_smul]

@[simp]
theorem multilinearDescend_apply_image
    (q : ∀ i, M i →ₗ[R] N i) (hq : ∀ i, Surjective (q i))
    (f : MultilinearMap R M W)
    (hf : ∀ x y, (∀ i, q i (x i) = q i (y i)) → f x = f y)
    (x : ∀ i, M i) :
    multilinearDescend q hq f hf (fun i => q i (x i)) = f x := by
  apply hf
  intro i
  exact surjInv_eq (hq i) _

@[simp]
theorem multilinearDescend_compLinearMap
    (q : ∀ i, M i →ₗ[R] N i) (hq : ∀ i, Surjective (q i))
    (f : MultilinearMap R M W)
    (hf : ∀ x y, (∀ i, q i (x i) = q i (y i)) → f x = f y) :
    (multilinearDescend q hq f hf).compLinearMap q = f := by
  ext x
  exact multilinearDescend_apply_image q hq f hf x

end Problem346

end

end OAI
