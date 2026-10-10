import OAI.NumberTheory.Ostmann.Arithmetic.MovingScheduledLeafCongruence
import OAI.NumberTheory.Ostmann.Arithmetic.MovingWeightedMatchedCorrelation
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateCoefficient

namespace OAI

/-! # Compact leaf multipliers preserve the scheduled statistic -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The zero frequency is removed and all live bottom frequencies are retained. -/
noncomputable def movingCompactLeaf (V : ℕ) (s : ℤ) : ℂ :=
  if s.natAbs ≤ V then if s = 0 then 0 else 1 else 0

theorem movingCompactLeaf_zero (V : ℕ) : movingCompactLeaf V 0 = 0 := by
  simp [movingCompactLeaf]

theorem movingCompactLeaf_norm (V : ℕ) (s : ℤ) :
    ‖movingCompactLeaf V s‖ ≤ if s.natAbs ≤ V then 1 else 0 := by
  unfold movingCompactLeaf
  split_ifs <;> simp

theorem movingOriginalLeaf_congr {σ I : Type*}
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (f h : ℤ → ℂ) (s : ℤ) (hs : f s = h s)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (x : MovingSlotState σ) :
    movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi x s =
      movingOriginalLeaf value q (fun _ => h) g Dq S ψ X lo hi x s := by
  simp only [movingOriginalLeaf, movingWindowLeaf, movingDataLeaf, hs]

theorem movingFrequencyCoefficient_original_leaf_congr {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (f h : ℤ → ℂ) (hf : ∀ s, s.natAbs ≤ V 0 → f s = h s)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (s : ℤ) (hs : s.natAbs ≤ V n)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s small bulk XL XR =
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => h) g Dq S ψ X lo hi) φ G n s small bulk XL XR := by
  apply movingFrequencyCoefficient_leaf_congr value outside μ childBound pivotBound V
    _ _ _ φ G n s hs small bulk XL XR
  intro x z hz
  exact movingOriginalLeaf_congr value q f h z (hf z hz) g Dq S ψ X lo hi x

theorem movingWeightedMatchedCorrelation_leaf_congr {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (f h : ℤ → ℂ) (hf : ∀ s, s.natAbs ≤ V 0 → f s = h s)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (W : ℤ → (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ) :
    movingWeightedMatchedCorrelation q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n small bulk W u v r w center =
    movingWeightedMatchedCorrelation q value outside μ ν childBound pivotBound V h g Dq S
      ψ X lo hi φ G n small bulk W u v r w center := by
  unfold movingWeightedMatchedCorrelation
  apply Finset.sum_congr rfl
  intro s _
  have he := movingFrequencyCoefficient_original_leaf_congr value q outside μ
    childBound pivotBound V f h hf g Dq S ψ X lo hi φ G n s.val
    ((mem_transferFrequencyRange _ _).mp s.property)
  simp_rw [he]

theorem movingTemplateCoefficient_original_leaf_congr {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (f h : ℤ → ℂ) (hf : ∀ s, s.natAbs ≤ V 0 → f s = h s)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (s : ℤ) (hs : s.natAbs ≤ V n)
    (y : MovingRegularSlot n r m → σ) (XL XR : ℕ) :
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n r m s y XL XR =
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => h) g Dq S ψ X lo hi) φ G n r m s y XL XR :=
  movingFrequencyCoefficient_original_leaf_congr value q outside μ childBound pivotBound V
    f h hf g Dq S ψ X lo hi φ G n s hs _ _ XL XR

theorem movingWeightedMatchedCorrelation_compact {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (W : ℤ → (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ) :
    movingWeightedMatchedCorrelation q value outside μ ν childBound pivotBound V
      (fun s => if s = 0 then 0 else 1) g Dq S ψ X lo hi φ G n small bulk W u v r w center =
    movingWeightedMatchedCorrelation q value outside μ ν childBound pivotBound V
      (movingCompactLeaf (V 0)) g Dq S ψ X lo hi φ G n small bulk W u v r w center := by
  apply movingWeightedMatchedCorrelation_leaf_congr
  intro s hs
  simp only [movingCompactLeaf, hs, ite_true]

end Ostmann

end OAI
