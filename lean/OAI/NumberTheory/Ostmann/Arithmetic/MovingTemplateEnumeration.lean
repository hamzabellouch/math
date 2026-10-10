import Mathlib.Data.List.NodupEquivFin
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRestoredMultiplier

namespace OAI

/-! # The canonical full list contains every template coordinate once -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateSlotList_nodup (n r m : ℕ) :
    (movingTemplateSlotList n r m).Nodup := by
  unfold movingTemplateSlotList movingTemplateSmall
  apply List.nodup_append.mpr
  refine ⟨bulkSlotLeaves_nodup n r _ ?_,
    bulkSlotLeaves_nodup n m _ (movingTemplateBulk n r m).injective, ?_⟩
  · intro i j h
    exact Prod.ext (congrArg (fun z : MovingRegularSlot n r m => z.1) h)
      (Sum.inl.inj (congrArg (fun z : MovingRegularSlot n r m => z.2) h))
  · intro a ha b hb hab
    obtain ⟨i, rfl⟩ := (mem_flatten_bulkSlotLeaves n r _ a).mp ha
    obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n m _ b).mp hb
    have hh : (Sum.inl i.2 : Fin r ⊕ Fin m) = Sum.inr j.2 :=
      congrArg (fun z : MovingRegularSlot n r m => z.2) hab
    cases hh

noncomputable def movingTemplateListEquiv (n r m : ℕ) :
    Fin (movingTemplateSlotList n r m).length ≃ MovingRegularSlot n r m :=
  List.Nodup.getEquivOfForallMemList (movingTemplateSlotList n r m)
    (movingTemplateSlotList_nodup n r m) (mem_movingTemplateSlotList n r m)

@[simp] theorem movingTemplateListEquiv_apply (n r m : ℕ)
    (i : Fin (movingTemplateSlotList n r m).length) :
    movingTemplateListEquiv n r m i = (movingTemplateSlotList n r m).get i := rfl

/-- Enumerating the full template does not change its masked cofactor product. -/
theorem movingTemplate_multiplier_list {A : Type*} (value : A → ℕ)
    (hprime : ∀ a, (value a).Prime) (n r m : ℕ)
    (x : MovingRegularSlot n r m → A) (active : MovingRegularSlot n r m → Bool)
    (g : ∀ q : ℕ, ZMod q → ℂ) (D XL XR : ℕ) (s : ℤ) :
    let L := movingTemplateSlotList n r m
    let p := fun i : Fin L.length => value (x (L.get i))
    let _ : ∀ i, Fact (p i).Prime := fun _ => ⟨hprime _⟩
    let _ : ∀ i, Fact ((value ∘ x) i).Prime := fun _ => ⟨hprime _⟩
    naturalRegularMultiplier p (fun i => active (L.get i)) s
      (fun i => ((D * tupleCofactor p i : ℕ) : ZMod (p i)))
      (fun i => g (p i)) XL XR =
    naturalRegularMultiplier (value ∘ x) active s
      (fun i => ((D * tupleCofactor (value ∘ x) i : ℕ) : ZMod ((value ∘ x) i)))
      (fun i => g (value (x i))) XL XR := by
  dsimp only
  let _ : ∀ i, Fact ((value ∘ x) i).Prime := fun _ => ⟨hprime _⟩
  let _ : ∀ i : Fin (movingTemplateSlotList n r m).length,
      Fact (value (x ((movingTemplateSlotList n r m).get i))).Prime := fun _ => ⟨hprime _⟩
  rw [naturalRegularMultiplier_eq_transform_norm, naturalRegularMultiplier_eq_transform_norm]
  have he := movingRegularTransform_equiv (movingTemplateListEquiv n r m) (value ∘ x)
    (fun i z => if active i then g (value (x i)) z else 1) (D * XL * XR) s
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2) he

end Ostmann

end OAI
