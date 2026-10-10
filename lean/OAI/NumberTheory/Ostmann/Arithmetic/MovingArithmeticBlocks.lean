import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedProduct
import OAI.NumberTheory.Ostmann.Arithmetic.CRTLineAverage

namespace OAI

/-! # Concrete CRT blocks for the original moving-history coefficient -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MovingArithmeticBlocks {I : Type*} (P : Finset ℕ) (S : Finset I) :=
  Unit ⊕ (P ⊕ S)

/-- One frequency block, one square for each distinct internal prime, and
one field for each spectator. -/
def movingArithmeticModuli {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I) : MovingArithmeticBlocks P S → ℕ
  | .inl _ => r
  | .inr (.inl p) => p.val ^ 2
  | .inr (.inr i) => q i.val

theorem movingArithmeticModuli_product {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I) :
    (∏ b, movingArithmeticModuli r q P S b) =
      r * ((∏ p ∈ P, p) ^ 2 * ∏ i ∈ S, q i) := by
  simp only [Fintype.prod_sum_type, movingArithmeticModuli, Fintype.prod_unique,
    Finset.prod_coe_sort, Finset.prod_pow]
  have hp : (∏ x : P, (x : ℕ)) = ∏ p ∈ P, p := Finset.prod_coe_sort P (fun p : ℕ => p)
  rw [hp]

theorem movingFrequencyPairFactor_modEq {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (hf : ∀ side, (T side).Frequencies (· ≠ 0))
    (hR : ∀ side, (T side).frequencyProduct ∣ R) (x y a b M : ℤ)
    (hM : R ^ (n + 1) ∣ M) (hx : x ≡ a [ZMOD M]) (hy : y ≡ b [ZMOD M]) :
    movingFrequencyPairFactor value outside F E T nodes R x y =
      movingFrequencyPairFactor value outside F E T nodes R a b := by
  have he (side : Bool) := movingFrequencyGate_modEq value R (T side) (hf side) (hR side)
    x y a b (hx.of_dvd hM) (hy.of_dvd hM)
  have hs : movingFrequencyPairSupport value outside T nodes R x y ↔
      movingFrequencyPairSupport value outside T nodes R a b := by
    simp only [movingFrequencyPairSupport, he]
  by_cases h : movingFrequencyPairSupport value outside T nodes R a b
  · simp only [movingFrequencyPairFactor, ite_eq_left (hs.mpr h), ite_eq_left h]
  · simp only [movingFrequencyPairFactor, ite_eq_right (fun hxy => h (hs.mp hxy)),
      ite_eq_right h]

/-- CRT coordinates are the casts of the original two residue representatives. -/
theorem crtExternalPairEquiv_casts {B : Type*} [Fintype B] (a : B → ℕ)
    [NeZero (∏ i, a i)] (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (z : ZMod (∏ i, a i) × (ZMod (∏ i, a i))ˣ) (i : B) :
    ((z.1.val : ZMod (a i)), ((z.2 : ZMod (∏ i, a i)).val : ZMod (a i))) =
      ((crtExternalPairEquiv a hc z i).1, ((crtExternalPairEquiv a hc z i).2 : ZMod (a i))) := by
  rcases z with ⟨x, y⟩
  rw [crtExternalPairEquiv_apply, crtUnitEquiv_apply, ZMod.prodEquivPi_apply]
  apply Prod.ext
  · have h := congrArg (ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i))
        (ZMod (a i))) (ZMod.natCast_zmod_val x)
    simpa only [map_natCast] using h
  · have h := congrArg (ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i))
        (ZMod (a i))) (ZMod.natCast_zmod_val (y : ZMod (∏ i, a i)))
    change ((y : ZMod (∏ i, a i)).val : ZMod (a i)) =
      (ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i)))
        (y : ZMod (∏ i, a i))
    simpa only [map_natCast] using h

noncomputable def movingArithmeticLocalFactor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) (P : Finset ℕ) (S : Finset I) :
    (b : MovingArithmeticBlocks P S) →
      ZMod (movingArithmeticModuli r q P S b) × (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ
  | .inl _, z => movingFrequencyPairFactor value outside F E T nodes R
      z.1.val (show (ZMod r)ˣ from z.2).val.val
  | .inr (.inl p), z => movingInternalPairFactor value T p.val z.1 (show (ZMod (p.val ^ 2))ˣ from z.2).val
  | .inr (.inr i), z => movingSpectatorPairFactor value (q i.val) (g i.val)
      (fun side => D side i.val) T z.1 (show (ZMod (q i.val))ˣ from z.2).val

/-- Complex-valued finite CRT factorization for the actual arithmetic blocks. -/
theorem movingArithmeticBlocks_average {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I)
    [∀ b, NeZero (movingArithmeticModuli r q P S b)]
    [NeZero (∏ b, movingArithmeticModuli r q P S b)]
    (hc : Pairwise (fun b c => (movingArithmeticModuli r q P S b).Coprime
      (movingArithmeticModuli r q P S c)))
    (f : ∀ b, ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ) :
    (Fintype.card (ZMod (∏ b, movingArithmeticModuli r q P S b) ×
      (ZMod (∏ b, movingArithmeticModuli r q P S b))ˣ) : ℂ)⁻¹ *
      (∑ z, ∏ b, f b (crtExternalPairEquiv (movingArithmeticModuli r q P S) hc z b)) =
    ∏ b, (Fintype.card (ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ) : ℂ)⁻¹ * ∑ z, f b z := by
  let e := crtExternalPairEquiv (movingArithmeticModuli r q P S) hc
  rw [e.sum_comp (fun x => ∏ b, f b (x b)), Fintype.card_congr e, Fintype.card_pi]
  rw [← Fintype.prod_sum]
  simp only [Nat.cast_prod, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end Ostmann

end OAI
