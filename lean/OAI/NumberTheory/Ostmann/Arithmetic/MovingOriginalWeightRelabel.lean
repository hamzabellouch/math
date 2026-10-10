import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotStateRelabel
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRecursiveSupport

namespace OAI

/-! # The original giant weight commutes with evaluating pattern labels -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

@[simp] theorem movingSlotModulus_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (x : MovingSlotState σ) :
    movingSlotModulus value (x.map f) = movingSlotModulus (value ∘ f) x := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [MovingSlotState.map, MovingSlotData.map, movingSlotModulus,
    ← List.map_append, MovingSlotReversal.naturalProduct_map]

theorem movingSlotCutoff_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (extra : MovingSlotState τ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound extra (x.map f) s v w =
      movingSlotCutoff (value ∘ f) childBound pivotBound
        (fun x => extra (x.map f)) x s v w := by
  simp only [movingSlotCutoff, MovingSlotState.compensation_map, movingHistoryPivot_map]

theorem movingPhiExtra_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (extra : MovingSlotState τ → ℤ → ℤ → ℤ → ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingPhiExtra value childBound pivotBound extra φ G (x.map f) s v w =
      movingPhiExtra (value ∘ f) childBound pivotBound
        (fun x => extra (x.map f)) φ G x s v w := by
  simp only [movingPhiExtra, MovingSlotState.map_depth, movingHistoryPivot_map,
    MovingSlotState.compensation_map]

theorem movingOriginalGiantWeight_map {σ τ I : Type*} (f : σ → τ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : τ → ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData τ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData τ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (XL XR : ℕ) :
    movingOriginalGiantWeight q value childBound pivotBound F E g Dq S ψ X lo hi φ G
      (T.map f) t XL XR =
    movingOriginalGiantWeight q (value ∘ f) childBound pivotBound
      (fun T => F (T.map f)) (fun T => E (T.map f)) g Dq S ψ X lo hi φ G T t XL XR := by
  unfold movingOriginalGiantWeight
  change recursiveTransferWeight _ _ _ n
    ((⟨n, T, XL, XR⟩ : MovingSlotState σ).map f) t = _
  rw [movingRecursiveWeight_map]
  congr 1
  · funext x s
    simp only [movingWindowLeaf, movingDataLeaf, movingFourierLeaf,
      spectatorHistoryLeaf, movingSlotModulus_map, MovingSlotState.map_data]
    rfl
  · funext x s v w
    rw [movingSlotCutoff_map]
    congr 1
    funext y a b c
    rw [movingPhiExtra_map]
    rfl

@[simp] theorem MovingSlotData.regularSlots_map {σ τ : Type*} (f : σ → τ)
    {n : ℕ} (T : MovingSlotData σ n) : (T.map f).regularSlots = T.regularSlots.map f := by
  cases T <;> simp only [MovingSlotData.map, MovingSlotData.regularSlots, List.map_append]

@[simp] theorem MovingSlotData.frequencyProduct_map {σ τ : Type*} (f : σ → τ)
    {n : ℕ} (T : MovingSlotData σ n) : (T.map f).frequencyProduct = T.frequencyProduct := by
  induction T with
  | leaf => rfl
  | node s CL CR u l r ihL ihR =>
    simp only [MovingSlotData.map, MovingSlotData.frequencyProduct, ihL, ihR]

@[simp] theorem MovingSlotData.currentSlots_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    (T.map f).currentSlots value XL XR = T.currentSlots (value ∘ f) XL XR := by
  simp only [MovingSlotData.currentSlots, MovingSlotData.regularSlots_map, List.map_map]

theorem movingLocalGiantUnits_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℤ) :
    movingLocalGiantUnits value outside (T.map f) XL XR ↔
      movingLocalGiantUnits (value ∘ f) outside T XL XR := by
  simp only [movingLocalGiantUnits, MovingSlotData.frequencyProduct_map,
    MovingSlotData.regularSlots_map, MovingSlotReversal.naturalProduct_map]

theorem MovingSlotReversal.naturalPivot_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (s : MovingSlotReversal σ) (XL XR : ℕ) :
    (s.map f).naturalPivot value XL XR = s.naturalPivot (value ∘ f) XL XR := by
  simp only [MovingSlotReversal.naturalPivot, MovingSlotReversal.map,
    MovingSlotReversal.naturalProduct_map]

theorem movingLocalSupport_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (outside : List ℕ) (x : MovingSlotState σ) :
    movingLocalSupport value outside (x.map f) ↔
      movingLocalSupport (value ∘ f) outside x := by
  change (((x.data.map f).currentSlots value x.leftGiant x.rightGiant ++ outside).Pairwise Nat.Coprime ∧
      movingLocalGiantUnits value outside (x.data.map f) x.leftGiant x.rightGiant) ↔ _
  rw [MovingSlotData.currentSlots_map, movingLocalGiantUnits_map]
  rfl

theorem movingFullSupport_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    movingFullSupport value outside (T.map f) XL XR ↔
      movingFullSupport (value ∘ f) outside T XL XR := by
  induction T generalizing XL XR with
  | leaf s regular =>
    change movingLocalSupport value outside
      ((⟨0, .leaf s regular, XL, XR⟩ : MovingSlotState σ).map f) ↔ _
    exact movingLocalSupport_map f value outside _
  | node s CL CR u l r ihL ihR =>
    have hlocal := movingLocalSupport_map f value outside
      (⟨_, .node s CL CR u l r, XL, XR⟩ : MovingSlotState σ)
    change movingLocalSupport value outside
      ⟨_, .node s (CL.map f) (CR.map f) (u.map f) (l.map f) (r.map f), XL, XR⟩ ↔ _ at hlocal
    simp only [MovingSlotData.map, movingFullSupport_node, MovingSlotData.step_map,
      MovingSlotReversal.naturalPivot_map, ihL, ihR, hlocal]

theorem movingSupportedWeight_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (XL XR : ℕ) (z : ℂ) :
    movingSupportedWeight value outside (T.map f) XL XR z =
      movingSupportedWeight (value ∘ f) outside T XL XR z := by
  simp only [movingSupportedWeight, movingFullSupport_map]

end Ostmann

end OAI
