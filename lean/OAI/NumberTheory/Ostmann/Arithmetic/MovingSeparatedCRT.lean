import OAI.NumberTheory.Ostmann.Arithmetic.MovingArithmeticModulus

namespace OAI

/-! # Exact CRT factorization of the original separated pair -/

namespace Ostmann
open scoped Classical BigOperators

section
variable {σ I : Type*} (q : I → ℕ) [∀ i, Fact (q i).Prime]
  (value : σ → ℕ) (outside : List ℕ)
  (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
  (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
  (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ)
  {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
  (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) (S : Finset I)
  [NeZero (∏ b, movingArithmeticModuli r q P S b)]
  (hf : ∀ side, (T side).Frequencies (· ≠ 0))
  (hR : ∀ side, (T side).frequencyProduct ∣ R)
  (hfrequency : R ^ (n + 1) ∣ (r : ℤ))
  (hcover : ∀ side, ∀ o ∈ (T side).occurrences,
    ∀ i ∈ o.current.compensationSlots, value i ∈ P)
  (hc : Pairwise (fun b c => (movingArithmeticModuli r q P S b).Coprime
    (movingArithmeticModuli r q P S c)))

include hf hR hfrequency hcover hc

/-- Pointwise CRT identification, using the actual frequency recursion and
all actual internal occurrences, before any norm or average is taken. -/
theorem movingSeparatedPairResidueCoefficient_crt
    (z : ZMod (∏ b, movingArithmeticModuli r q P S b) ×
      (ZMod (∏ b, movingArithmeticModuli r q P S b))ˣ) :
    movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R
      z.1.val (z.2 : ZMod (∏ b, movingArithmeticModuli r q P S b)).val =
    ∏ b, movingArithmeticLocalFactor q value outside F E g D T nodes R r P S b
      (crtExternalPairEquiv (movingArithmeticModuli r q P S) hc z b) := by
  let a := movingArithmeticModuli r q P S
  let e := crtExternalPairEquiv a hc
  let f := movingArithmeticLocalFactor q value outside F E g D T nodes R r P S
  let x := z.1.val
  let y := (z.2 : ZMod (∏ b, a b)).val
  have hcasts (b) := crtExternalPairEquiv_casts a hc z b
  have hfreq : f (.inl ()) (e z (.inl ())) =
      movingFrequencyPairFactor value outside F E T nodes R x y := by
    let v : ZMod r × (ZMod r)ˣ := e z (.inl ())
    have hl : (x : ZMod r) = v.1 := congrArg Prod.fst (hcasts (.inl ()))
    have hr : (y : ZMod r) = (v.2 : ZMod r) := congrArg Prod.snd (hcasts (.inl ()))
    have hx : (x : ℤ) ≡ (v.1.val : ℤ) [ZMOD (r : ℤ)] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ r).mp
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
        hl
    have hy : (y : ℤ) ≡ ((v.2 : ZMod r).val : ℤ) [ZMOD (r : ℤ)] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ r).mp
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
        hr
    exact (movingFrequencyPairFactor_modEq value outside F E T nodes R hf hR
      x y v.1.val (v.2 : ZMod r).val r hfrequency hx hy).symm
  have hint (p : P) : f (.inr (.inl p)) (e z (.inr (.inl p))) =
      movingInternalPairFactor value T p.val x y := by
    have hl : (x : ZMod (p.val ^ 2)) = (e z (.inr (.inl p))).1 :=
      congrArg Prod.fst (hcasts (.inr (.inl p)))
    have hr : (y : ZMod (p.val ^ 2)) =
        (show (ZMod (p.val ^ 2))ˣ from (e z (.inr (.inl p))).2).val :=
      congrArg Prod.snd (hcasts (.inr (.inl p)))
    exact congrArg₂ (movingInternalPairFactor value T p.val) hl.symm hr.symm
  have hspec (i : S) : f (.inr (.inr i)) (e z (.inr (.inr i))) =
      movingSpectatorPairFactor value (q i.val) (g i.val) (fun side => D side i.val) T x y := by
    have hl : (x : ZMod (q i.val)) = (e z (.inr (.inr i))).1 :=
      congrArg Prod.fst (hcasts (.inr (.inr i)))
    have hr : (y : ZMod (q i.val)) =
        (show (ZMod (q i.val))ˣ from (e z (.inr (.inr i))).2).val :=
      congrArg Prod.snd (hcasts (.inr (.inr i)))
    exact congrArg₂ (movingSpectatorPairFactor value (q i.val) (g i.val)
      (fun side => D side i.val) T) hl.symm hr.symm
  change movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R x y =
    ∏ b, f b (e z b)
  rw [movingSeparatedPairResidueCoefficient_product q value outside F E g D S T nodes R P hcover]
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, hfreq, hint, hspec]
  rw [Finset.prod_coe_sort P (fun p => movingInternalPairFactor value T p x y),
    Finset.prod_coe_sort S (fun i =>
      movingSpectatorPairFactor value (q i) (g i) (fun side => D side i) T x y)]
  ring

/-- The Haar average of the original coefficient equals the product of its
frequency, internal-square and spectator averages. -/
theorem movingSeparatedPairResidueCoefficient_average
    [∀ b, NeZero (movingArithmeticModuli r q P S b)] :
    (Fintype.card (ZMod (∏ b, movingArithmeticModuli r q P S b) ×
      (ZMod (∏ b, movingArithmeticModuli r q P S b))ˣ) : ℂ)⁻¹ *
      (∑ z : ZMod (∏ b, movingArithmeticModuli r q P S b) ×
        (ZMod (∏ b, movingArithmeticModuli r q P S b))ˣ, movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R
        z.1.val (z.2 : ZMod (∏ b, movingArithmeticModuli r q P S b)).val) =
    ∏ b, (Fintype.card (ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ) : ℂ)⁻¹ *
      ∑ z, movingArithmeticLocalFactor q value outside F E g D T nodes R r P S b z := by
  simp_rw [movingSeparatedPairResidueCoefficient_crt q value outside F E g D T nodes
    R r P S hf hR hfrequency hcover hc]
  exact movingArithmeticBlocks_average r q P S hc _

end
end Ostmann

end OAI
