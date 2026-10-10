import OAI.NumberTheory.Ostmann.Arithmetic.MovingPairedTransform
import OAI.NumberTheory.Ostmann.Arithmetic.MovingChildListSupport

namespace OAI

/-! # Transfer support derived from nonzero original template coefficients -/

namespace Ostmann
open scoped Classical BigOperators

private theorem indexed_coprime_of_list {I : Type*} (p : I → ℕ) (L : List I)
    (hcover : ∀ i, i ∈ L) (h : (L.map p).Pairwise Nat.Coprime) :
    Pairwise (fun i j => (p i).Coprime (p j)) := by
  have h' : L.Pairwise (fun i j => i ≠ j → (p i).Coprime (p j)) :=
    (List.pairwise_map.mp h).imp (fun {i j} hij (_ : i ≠ j) => hij)
  have hflip : L.Pairwise (flip (fun i j => i ≠ j → (p i).Coprime (p j))) :=
    h'.imp (fun {i j} hij (hji : j ≠ i) => (hij hji.symm).symm)
  intro i j hij
  exact h'.forall_of_forall_of_flip (fun a _ haa => (haa rfl).elim) hflip
    (hcover i) (hcover j) hij

/-- The complete current Fourier slots inherit pairwise and outside
coprimality directly from the support of their coefficient. -/
theorem movingTemplateCoefficient_transfer_support {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (q : Bool → ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n r m s y (q true) (q false) ≠ 0) :
    Pairwise (fun i j => (Sum.elim q (value ∘ y) i).Coprime (Sum.elim q (value ∘ y) j)) ∧
      ∀ i, outside.prod.Coprime (Sum.elim q (value ∘ y) i) := by
  let L : List (Bool ⊕ MovingRegularSlot n r m) :=
    [.inl true, .inl false] ++ (movingTemplateSlotList n r m).map Sum.inr
  let p := Sum.elim q (value ∘ y)
  have hcover : ∀ i, i ∈ L := by
    intro i
    cases i with
    | inl b => cases b <;> simp [L]
    | inr i => exact List.mem_append_right _ (List.mem_map.mpr
        ⟨i, mem_movingTemplateSlotList n r m i, rfl⟩)
  have hs := (movingFrequencyCoefficient_nonzero_support value outside μ childBound
    pivotBound V F φ G n s _ _ (q true) (q false) h).1
  have hs' : (L.map p ++ outside).Pairwise Nat.Coprime := by
    simpa only [L, p, List.map_append, List.map_cons, List.map_nil, List.map_map,
      List.cons_append, List.nil_append, Sum.elim_inl, Sum.elim_inr,
      movingTemplateSlotList, flattenMovingSlots_map, Function.comp_def] using hs
  obtain ⟨hp, _, ho⟩ := List.pairwise_append.mp hs'
  refine ⟨indexed_coprime_of_list p L hcover hp, ?_⟩
  intro i
  apply Nat.coprime_list_prod_left_iff.mpr
  intro d hd
  exact (ho (p i) (List.mem_map.mpr ⟨i, hcover i, rfl⟩) d hd).symm

/-- Restrict the full support to the two pieces of a restored child.
This supplies the exact support fields of the giant transfer. -/
theorem movingTemplateCoefficient_restored_support {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → σ) (y : MovingRegularSlot n r m → σ)
    (p X : ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n (4 + r) m s (movingRestoreSample n r m u y) p X ≠ 0) :
    let Q := Sum.elim (fun _ : Unit => p) (value ∘ u)
    let L := Sum.elim (fun _ : Unit => X) (value ∘ y)
    Pairwise (fun i j => (Q i).Coprime (Q j)) ∧
      (∀ i, outside.prod.Coprime (Q i)) ∧
      Pairwise (fun i j => (L i).Coprime (L j)) ∧
      (∏ i, L i).Coprime (∏ i, Q i) ∧
      (∀ i, outside.prod.Coprime (L i)) := by
  let q : Bool → ℕ := fun b => if b then p else X
  have hs := movingTemplateCoefficient_transfer_support value outside μ childBound pivotBound V
    F φ G n (4 + r) m s (movingRestoreSample n r m u y) q h
  have he := movingTransferSlotEquiv_values value n r m u y p X
  let f := Sum.elim (Sum.elim (fun _ : Unit => p) (value ∘ u))
    (Sum.elim (fun _ : Unit => X) (value ∘ y))
  have hp : Pairwise (fun i j => (f i).Coprime (f j)) := by
    intro i j hij
    have hx := hs.1 ((movingTransferSlotEquiv n r m).injective.ne hij)
    change (Sum.elim q (value ∘ movingRestoreSample n r m u y)
      (movingTransferSlotEquiv n r m i)).Coprime
      (Sum.elim q (value ∘ movingRestoreSample n r m u y)
      (movingTransferSlotEquiv n r m j)) at hx
    rw [congrFun he i, congrFun he j] at hx
    exact hx
  have hd : ∀ i, outside.prod.Coprime (f i) := by
    intro i
    have hx := hs.2 (movingTransferSlotEquiv n r m i)
    rw [congrFun he i] at hx
    exact hx
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hp (fun he => hij (Sum.inl.inj he))
  · intro i
    exact hd (.inl i)
  · intro i j hij
    exact hp (fun he => hij (Sum.inr.inj he))
  · apply Nat.coprime_prod_left_iff.mpr
    intro i _
    apply Nat.coprime_prod_right_iff.mpr
    intro j _
    exact hp (Sum.inr_ne_inl)
  · intro i
    exact hd (.inr i)

end Ostmann

end OAI
