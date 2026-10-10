import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingNormalizedStatistic

namespace OAI

/-! # The full-template Fourier amplitude is the original prime statistic -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

local instance coreSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

/-- The template amplitude used in the transfer and the core bounded by the
arithmetic estimate are identical at the actual prime giants. Every cofactor,
spectator transform, and leaf weight is evaluated at the original value. -/
theorem movingTemplatePrimeCore_eq_full {σ I : Type} [Fintype σ]
    (pSpec : I → ℕ) [∀ i, Fact (pSpec i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (pSpec i) → ℂ) (Dq : ∀ i, (ZMod (pSpec i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (s : ℤ) (y : MovingRegularSlot n r m → σ)
    (q : Bool → ℕ) [∀ b, Fact (q b).Prime]
    (hprime : ∀ i, (value (y i)).Prime)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    let _ : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime i⟩
    movingPrimeCore pSpec value outside μ childBound pivotBound V f g Dq S ψ X lo hi φ G
      n m (movingTemplateSmall n r m) (movingTemplateBulk n r m) greg ggiant favorable
      s y (Real.log (q true)) (Real.log (q false)) =
    movingRegularTransform (Sum.elim q (value ∘ y))
      (fun i => match i with
        | .inl b => fun t => if favorable (q b) then complexUnitPhase (ggiant (q b) t) else 0
        | .inr j => greg (value (y j))) outside.prod s *
      movingTemplateCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value pSpec (fun _ => f) g Dq S ψ X lo hi) φ G n r m s y
        (q true) (q false) := by
  let : ∀ i, Fact ((value ∘ y) i).Prime := fun i => ⟨hprime i⟩
  dsimp only
  have hfull := movingTemplateCoefficient_full_transform value outside μ childBound pivotBound V
    (movingOriginalLeaf value pSpec (fun _ => f) g Dq S ψ X lo hi) φ G n r m s y q hprime
    greg ggiant favorable
  have hphase := movingGiantPhase_regularFactor_eq value outside
    (movingTemplateSmall n r m) (bulkSlotLeaves n m (movingTemplateBulk n r m)) y q
    (value ∘ y) (movingTemplate_product value n r m y) greg ggiant favorable s
  have hq (b : Bool) : 0 < (q b : ℝ) := Nat.cast_pos.mpr (Fact.out : (q b).Prime).pos
  unfold movingPrimeCore
  rw [hphase, Real.exp_log (hq true), Real.exp_log (hq false), Nat.floor_natCast, Nat.floor_natCast]
  exact hfull.symm

end Ostmann

end OAI
