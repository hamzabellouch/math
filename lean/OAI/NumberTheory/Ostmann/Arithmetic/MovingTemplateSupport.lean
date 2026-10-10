import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCoefficientSupport
import OAI.NumberTheory.Ostmann.Construction.GiantTransformProduct

namespace OAI

/-! # The literal regular template and its full Fourier factor -/

namespace Ostmann
open scoped Classical BigOperators

local instance templateSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

noncomputable def movingTemplateSlotList (n r m : ℕ) : List (MovingRegularSlot n r m) :=
  flattenMovingSlots n (movingTemplateSmall n r m) ++
    flattenMovingSlots n (bulkSlotLeaves n m (movingTemplateBulk n r m))

theorem mem_movingTemplateSlotList (n r m : ℕ) (i : MovingRegularSlot n r m) :
    i ∈ movingTemplateSlotList n r m := by
  rcases i with ⟨j, i | i⟩
  · apply List.mem_append_left
    exact (mem_flatten_bulkSlotLeaves n r _ _).mpr ⟨(j, i), rfl⟩
  · apply List.mem_append_right
    exact (mem_flatten_bulkSlotLeaves n m _ _).mpr ⟨(j, i), rfl⟩

private theorem prime_pairwise_list_nodup (L : List ℕ) (hp : ∀ p ∈ L, p.Prime)
    (h : L.Pairwise Nat.Coprime) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons p L ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp h
    refine List.nodup_cons.mpr ⟨?_, ih (fun q hq => hp q (List.mem_cons_of_mem p hq)) ht⟩
    intro hmem
    have h1 : p = 1 := by simpa only [Nat.coprime_self] using hh p hmem
    exact (hp p List.mem_cons_self).ne_one h1

/-- The support of the actual coefficient forces every prime in the full
regular template to be distinct. -/
theorem movingTemplateCoefficient_nonzero_injective {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (XL XR : ℕ)
    (hprime : ∀ i, (value (y i)).Prime)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n r m s y XL XR ≠ 0) :
    Function.Injective (value ∘ y) := by
  have hs := (movingFrequencyCoefficient_nonzero_support value outside μ childBound pivotBound V
    F φ G n s _ _ XL XR h).1
  have hr : ((movingTemplateSlotList n r m).map (value ∘ y) ++ outside).Pairwise Nat.Coprime := by
    simpa only [flattenMovingSlots_map, List.map_append, List.map_map, Function.comp_def,
      movingTemplateSlotList, List.tail_cons] using hs.tail.tail
  have hnd : ((movingTemplateSlotList n r m).map (value ∘ y)).Nodup := by
    apply prime_pairwise_list_nodup _ _ (List.pairwise_append.mp hr).1
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact hprime i
  intro i j hij
  exact List.inj_on_of_nodup_map hnd (mem_movingTemplateSlotList n r m i)
    (mem_movingTemplateSlotList n r m j) hij

/-- The two phase factors and the regular product transform combine into
exactly the full indexed Fourier transform wherever the coefficient contributes. -/
theorem movingTemplateCoefficient_full_transform {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (q : Bool → ℕ) [∀ b, Fact (q b).Prime]
    (hprime : ∀ i, (value (y i)).Prime)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    let _ : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime i⟩
    movingRegularTransform (Sum.elim q (value ∘ y))
      (fun i => match i with
        | .inl b => fun t => if favorable (q b) then complexUnitPhase (ggiant (q b) t) else 0
        | .inr j => greg (value (y j))) outside.prod s *
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n r m s y (q true) (q false) =
    (giantPairPhase ggiant favorable outside.prod (∏ i, value (y i)) (q true) (q false) s *
      primeProductTransform greg (outside.prod * q true * q false) (∏ i, value (y i)) s) *
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n r m s y (q true) (q false) := by
  let : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime i⟩
  dsimp only
  by_cases h : movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n r m s y (q true) (q false) = 0
  · simp only [h, mul_zero]
  · have he := movingRegularTransform_two_giant_phases q (value ∘ y)
      (movingTemplateCoefficient_nonzero_injective value outside μ childBound pivotBound V F
        φ G n r m s y (q true) (q false) hprime h) greg ggiant favorable outside.prod s
    have hh := congrArg (fun z : ℂ => z * movingTemplateCoefficient value outside μ childBound pivotBound V
      F φ G n r m s y (q true) (q false)) he
    convert hh using 1 <;> try rfl
    apply congrArg (fun z : ℂ => z * movingTemplateCoefficient value outside μ childBound pivotBound V
      F φ G n r m s y (q true) (q false))
    unfold movingRegularTransform
    apply Finset.prod_congr rfl
    intro i _
    cases i <;> rfl

end Ostmann

end OAI
