import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantPhase

namespace OAI

/-! # Recombining the two giant phases with the common regular transform -/

namespace Ostmann
open scoped Classical BigOperators

local instance giantProductSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

private theorem bool_tupleCofactor (q : Bool → ℕ) [∀ b, Fact (q b).Prime] (b : Bool) :
    tupleCofactor q b = q (!b) := by
  have hp : 0 < q b := (Fact.out : (q b).Prime).pos
  have hh := tupleCofactor_mul q b
  rw [Fintype.prod_bool] at hh
  cases b <;> simp only [Bool.not_true, Bool.not_false] <;> nlinarith

/-- The cofactor formula in the two-prime statistic is exactly the full
Fourier transform of the original ordered regular-prime tuple. -/
theorem movingRegularTransform_two_giant_phases {I : Type*} [Fintype I]
    (q : Bool → ℕ) (p : I → ℕ) [∀ b, Fact (q b).Prime] [∀ i, Fact (p i).Prime]
    (hp : Function.Injective p) (greg ggiant : ∀ r : ℕ, ZMod r → ℂ)
    (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingRegularTransform (Sum.elim q p)
      (fun i => match i with
        | .inl b => fun t => if favorable (q b) then complexUnitPhase (ggiant (q b) t) else 0
        | .inr j => greg (p j)) D s =
    ((if favorable (q true) then complexUnitPhase
      (ggiant (q true) ((s : ZMod (q true)) *
        ((D * q false * (∏ i, p i) : ℕ) : ZMod (q true))⁻¹)) else 0) *
      (if favorable (q false) then complexUnitPhase
      (ggiant (q false) ((s : ZMod (q false)) *
        ((D * q true * (∏ i, p i) : ℕ) : ZMod (q false))⁻¹)) else 0)) *
      primeProductTransform greg (D * q true * q false) (∏ i, p i) s := by
  have hs := moving_regular_transform_split q p
    (fun b t => if favorable (q b) then complexUnitPhase (ggiant (q b) t) else 0)
    (fun i => greg (p i)) D s
  have hfinal :
      movingRegularTransform q
        (fun b t => if favorable (q b) then complexUnitPhase (ggiant (q b) t) else 0)
        (D * ∏ i, p i) s *
      movingRegularTransform p (fun i => greg (p i)) (D * ∏ b, q b) s =
    ((if favorable (q true) then complexUnitPhase
      (ggiant (q true) ((s : ZMod (q true)) *
        ((D * q false * (∏ i, p i) : ℕ) : ZMod (q true))⁻¹)) else 0) *
      (if favorable (q false) then complexUnitPhase
      (ggiant (q false) ((s : ZMod (q false)) *
        ((D * q true * (∏ i, p i) : ℕ) : ZMod (q false))⁻¹)) else 0)) *
      primeProductTransform greg (D * q true * q false) (∏ i, p i) s := by
    rw [movingRegularTransform_eq_primeProduct p hp]
    simp only [Fintype.prod_bool]
    rw [show D * (q true * q false) = D * q true * q false by ring]
    congr 1
    simp only [movingRegularTransform, Fintype.prod_bool, bool_tupleCofactor,
      Bool.not_true, Bool.not_false]
    simp only [show ∀ a b c : ℕ, (a * b) * c = (a * c) * b by intros; ring]
  convert hs.trans hfinal using 1
  congr 1
  funext i
  cases i with
  | inl b =>
    funext t
    dsimp only
  | inr j => rfl

/-- The common factor actually used by the statistic is this same cofactor
product, including the two giant denominators. -/
theorem movingGiantPhase_regularFactor_eq {σ B I : Type*} [Fintype I] {n : ℕ}
    (value : σ → ℕ) (outside : List ℕ) (small bulk : TreeLeafTuple (List B) n)
    (y : B → σ) (q : Bool → ℕ) (p : I → ℕ) [∀ b, Fact (q b).Prime]
    (hprod : MovingSlotReversal.naturalProduct (value ∘ y)
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk) = ∏ i, p i)
    (greg ggiant : ∀ r : ℕ, ZMod r → ℂ) (favorable : ℕ → Bool) (s : ℤ) :
    movingGiantPhase value outside small bulk ggiant favorable s y
        (Real.log (q true)) (Real.log (q false)) *
      movingExternalRegularFactor value outside small bulk greg s y
        (Real.log (q true)) (Real.log (q false)) =
    ((if favorable (q true) then complexUnitPhase
      (ggiant (q true) ((s : ZMod (q true)) *
        ((outside.prod * q false * (∏ i, p i) : ℕ) : ZMod (q true))⁻¹)) else 0) *
      (if favorable (q false) then complexUnitPhase
      (ggiant (q false) ((s : ZMod (q false)) *
        ((outside.prod * q true * (∏ i, p i) : ℕ) : ZMod (q false))⁻¹)) else 0)) *
      primeProductTransform greg (outside.prod * q true * q false) (∏ i, p i) s := by
  have hq (b : Bool) : 0 < (q b : ℝ) := by exact_mod_cast (Fact.out : (q b).Prime).pos
  have he (b : Bool) : ⌊Real.exp (Real.log (q b : ℝ))⌋₊ = q b := by
    rw [Real.exp_log (hq b), Nat.floor_natCast]
  unfold movingGiantPhase movingExternalRegularFactor
  rw [he true, he false, hprod]
  rfl

end Ostmann

end OAI
