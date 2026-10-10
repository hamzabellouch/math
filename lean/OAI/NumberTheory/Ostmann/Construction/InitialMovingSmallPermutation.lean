import Mathlib.Data.List.FinRange
import OAI.NumberTheory.Ostmann.Arithmetic.MovingLeafPermutation
import OAI.NumberTheory.Ostmann.Construction.InitialMovingNorm

namespace OAI

/-! # Permuting small slots preserves the literal initial coefficient -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

def movingSmallSlotEquiv (n m : ℕ) {r r' : ℕ} (e : Fin r ≃ Fin r') :
    MovingRegularSlot n r m ≃ MovingRegularSlot n r' m :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.sumCongr e (Equiv.refl _))

theorem movingTemplateCoefficient_original_initial_halves {P I : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (y : MovingRegularSlot n a (b + b) → P) (hlen : a + 4 * n = r + r) (XL XR : ℕ) :
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n a (b + b) s y XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n (y ∘ movingTemplateBulk n a (b + b)) : ℂ) *
      movingTemplateCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
        φ G n a (b + b) s y XL XR := by
  unfold movingTemplateCoefficient
  rw [bulkSlotLeaves_map]
  exact movingFrequencyCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s _ _
    (movingLeafLengthEq_map y n _ a (bulkSlotLeaves_length_eq n a _)) hlen XL XR

theorem movingTemplateCoefficient_zero_small_perm {P I : Type} [Fintype P]
    (value : P → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (f : ℤ → ℂ) (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ)
    (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (r m : ℕ) (s : ℤ)
    (e : Equiv.Perm (Fin r)) (y : MovingRegularSlot 0 r m → P) (XL XR : ℕ) :
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G 0 r m s
      (y ∘ movingSmallSlotEquiv 0 m e) XL XR =
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G 0 r m s y XL XR := by
  unfold movingTemplateCoefficient
  simp only [movingTemplateSmall, bulkSlotLeaves, treeLeafTupleEquiv, treeLeafMap,
    Equiv.coe_fn_symm_mk, movingTemplateBulk, movingSmallSlotEquiv, Function.comp_def,
    Equiv.prodCongr_apply, List.map_ofFn]
  apply movingFrequencyCoefficient_zero_small_perm
  change (List.ofFn ((fun i => y ((), Sum.inl i)) ∘ e)).Perm
    (List.ofFn (fun i => y ((), Sum.inl i)))
  exact e.ofFn_comp_perm _

theorem movingTemplateCoefficient_initial_zero_small_perm {P I : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ)
    (e : Equiv.Perm (Fin (r + r))) (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (XL XR : ℕ) :
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G 0 (r + r) (b + b) s
      (y ∘ movingSmallSlotEquiv 0 (b + b) e) XL XR =
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G 0 (r + r) (b + b) s y XL XR := by
  rw [movingTemplateCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G 0 (r + r) s _ (by omega),
    movingTemplateCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G 0 (r + r) s _ (by omega)]
  rw [movingTemplateCoefficient_zero_small_perm value q _ g Dq S ψ X lo hi outside μ
    childBound pivotBound V φ G (r + r) (b + b) s e y XL XR]
  rfl

end Ostmann

end OAI
