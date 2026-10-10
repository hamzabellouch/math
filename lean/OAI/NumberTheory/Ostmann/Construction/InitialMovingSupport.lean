import OAI.NumberTheory.Ostmann.Construction.InitialMovingCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateEnumeration
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTransferSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingInitialCoefficient

namespace OAI

/-! # The original distinct-prime test as the moving leaf's pairwise guard -/
namespace Ostmann
open scoped Classical

private theorem prime_list_pairwise_iff {I : Type*} (L : List I)
    (hnd : L.Nodup) (hcover : ∀ i, i ∈ L) (value : I → ℕ)
    (hp : ∀ i, (value i).Prime) :
    (L.map value).Pairwise Nat.Coprime ↔ Function.Injective value := by
  constructor
  · intro h i j hij
    by_contra hne
    have hs := List.pairwise_map.mp h
    have : Std.Symm (fun i j => (value i).Coprime (value j)) := ⟨fun _ _ h => h.symm⟩
    have hc := hs.forall (hcover i) (hcover j) hne
    rw [hij, Nat.coprime_self] at hc
    exact (hp j).ne_one hc
  · intro hinj
    apply List.pairwise_map.mpr
    apply hnd.imp
    intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))

noncomputable def initialMovingSlotList (r m d : ℕ) :
    List (Fin d ⊕ (Bool ⊕ MovingRegularSlot 0 r m)) :=
  ([Sum.inr (.inl true), Sum.inr (.inl false)] ++
    (movingTemplateSlotList 0 r m).map (fun j => Sum.inr (.inr j))) ++
    (List.finRange d).map Sum.inl

theorem initialMovingSlotList_nodup (r m d : ℕ) :
    (initialMovingSlotList r m d).Nodup := by
  unfold initialMovingSlotList
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨by simp, ?_, ?_⟩
    · exact (movingTemplateSlotList_nodup 0 r m).map (by intro a b h; cases h; rfl)
    · intro a ha b hb hab
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
      rcases ha with rfl | rfl <;> cases hab
  · exact (List.nodup_finRange d).map Sum.inl_injective
  · intro a ha b hb hab
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
    rcases List.mem_append.mp ha with ha | ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> cases hab
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
      cases hab

theorem mem_initialMovingSlotList (r m d : ℕ)
    (i : Fin d ⊕ (Bool ⊕ MovingRegularSlot 0 r m)) : i ∈ initialMovingSlotList r m d := by
  rcases i with i | (a | j)
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  · apply List.mem_append_left
    apply List.mem_append_left
    cases a <;> simp
  · apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨j, mem_movingTemplateSlotList 0 r m j, rfl⟩

theorem initialMovingTuple_pairwise_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (sl sr : Fin d → P) (XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    (((XL : ℕ) :: (XR : ℕ) ::
      (movingTemplateSlotList 0 (r + r) (b + b)).map (fun i => (y i : ℕ))) ++
      List.ofFn (fun i : Fin (d + d) => ((Fin.append sl sr i : P) : ℕ))).Pairwise Nat.Coprime ↔
      Function.Injective (initialMovingTuple b d r sl sr XL XR y) := by
  let v : Fin (d + d) ⊕ (Bool ⊕ MovingRegularSlot 0 (r + r) (b + b)) → P :=
    Sum.elim (Fin.append sl sr) (Sum.elim (fun a : Bool => if a then XL else XR) y)
  have h := prime_list_pairwise_iff (initialMovingSlotList (r + r) (b + b) (d + d))
    (initialMovingSlotList_nodup _ _ _) (mem_initialMovingSlotList _ _ _)
    (fun i => (v i : ℕ)) (fun i => hP (v i) (v i).property)
  have hmap : (initialMovingSlotList (r + r) (b + b) (d + d)).map (fun i => (v i : ℕ)) =
      ((XL : ℕ) :: (XR : ℕ) ::
        (movingTemplateSlotList 0 (r + r) (b + b)).map (fun i => (y i : ℕ))) ++
      List.ofFn (fun i : Fin (d + d) => ((Fin.append sl sr i : P) : ℕ)) := by
    simp only [initialMovingSlotList, List.map_append, List.map_cons,
      List.map_map, Function.comp_def, v, Sum.elim_inl, Sum.elim_inr,
      Bool.false_eq_true, ite_false, ite_true, List.cons_append, List.nil_append,
      List.ofFn_eq_map]
  rw [hmap] at h
  rw [h]
  have hc : Function.Injective (fun i => (v i : ℕ)) ↔ Function.Injective v := by
    constructor
    · intro hv i j hij
      exact hv (congrArg Subtype.val hij)
    · intro hv i j hij
      exact hv (Subtype.ext hij)
  rw [hc]
  have he : v = initialMovingTuple b d r sl sr XL XR y ∘ initialCompleteIndexEquiv b d r :=
    (initialMovingTuple_reindex b d r sl sr XL XR y).symm
  rw [he]
  exact (initialCompleteIndexEquiv b d r).injective_comp _

noncomputable def initialMovingState (P : Finset ℕ) (b r : ℕ)
    (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ) :
    MovingSlotState P :=
  ⟨0, .leaf s ((movingTemplateSlotList 0 (r + r) (b + b)).map y), XL, XR⟩

theorem initialMovingState_support_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (sl sr : Fin d → P) (XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ)
    (hs : s ≠ 0) (hXL : s.natAbs < (XL : ℕ)) (hXR : s.natAbs < (XR : ℕ)) :
    movingLocalSupport (fun p : P => (p : ℕ))
      (List.ofFn (fun i : Fin (d + d) => ((Fin.append sl sr i : P) : ℕ)))
      (initialMovingState P b r XL XR y s) ↔
      Function.Injective (initialMovingTuple b d r sl sr XL XR y) := by
  have hp := initialMovingTuple_pairwise_iff P hP b d r sl sr XL XR y
  constructor
  · intro h
    apply hp.mp
    simpa only [initialMovingState, movingLocalSupport, MovingSlotData.currentSlots,
      MovingSlotData.regularSlots, List.map_map, Function.comp_def] using h.1
  · intro h
    apply moving_local_support_prime_giants (V := s.natAbs) _ _ _ _ _
      (hP XL XL.property) (hP XR XR.property) hXL hXR
    · simpa only [initialMovingState, MovingSlotData.currentSlots,
        MovingSlotData.regularSlots, List.map_map, Function.comp_def] using hp.mpr h
    · exact ⟨hs, le_rfl⟩

theorem movingTemplateCoefficient_initial (P : Finset ℕ) (b r : ℕ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ) :
    movingTemplateCoefficient (fun p : P => (p : ℕ)) outside μ childBound pivotBound V
      F φ G 0 (r + r) (b + b) s y XL XR =
    movingGuardedLeaf (fun p : P => (p : ℕ)) outside F (initialMovingState P b r XL XR y s) s := by
  rw [movingTemplateCoefficient, movingFrequencyCoefficient_levelZero]
  unfold initialMovingState movingTemplateSlotList
  rw [List.map_append]
  rfl

theorem movingTemplateCoefficient_initial_supported (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b d r : ℕ) (sl sr : Fin d → P)
    (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ)
    (hs : s ≠ 0) (hXL : s.natAbs < (XL : ℕ)) (hXR : s.natAbs < (XR : ℕ)) :
    movingTemplateCoefficient (fun p : P => (p : ℕ))
      (List.ofFn (fun i : Fin (d + d) => ((Fin.append sl sr i : P) : ℕ)))
      μ childBound pivotBound V F φ G 0 (r + r) (b + b) s y XL XR =
    if Function.Injective (initialMovingTuple b d r sl sr XL XR y) then
      F (initialMovingState P b r XL XR y s) s else 0 := by
  rw [movingTemplateCoefficient_initial, movingGuardedLeaf]
  rw [initialMovingState_support_iff P hP b d r sl sr XL XR y s hs hXL hXR]
  split_ifs <;> rfl

end Ostmann

end OAI
