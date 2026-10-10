import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotPolynomials

namespace OAI

/-! # Integer realization of the source-ordered slot rows -/

namespace Ostmann
open scoped BigOperators Classical

namespace MovingSlotReversal

/-- Each list is evaluated as its actual natural product, with multiplicities. -/
def naturalProduct {σ : Type*} (value : σ → ℕ) (slots : List σ) : ℕ :=
  (slots.map value).prod

theorem coefficient_nat_eval {σ K : Type*} [CommRing K]
    (value : σ → ℕ) (s : ℤ) (slots : List σ) :
    MvPolynomial.eval₂Hom (Int.castRingHom K) (fun i => (value i : K))
      (movingSlotCoefficient s slots) = (s : K) * (naturalProduct value slots : K) := by
  rw [movingSlotCoefficient_eval]
  congr 1
  induction slots with
  | nil => simp [naturalProduct]
  | cons i slots ih =>
    simpa only [List.map_cons, List.prod_cons, naturalProduct, Nat.cast_mul] using
      (congrArg ((value i : K) * ·) ih)

def naturalPivot {σ : Type*} (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : ℕ) : ℕ :=
  movingGiantPivot s.rootFrequency s.leftFrequency s.rightFrequency
    (naturalProduct value s.leftSlots) (naturalProduct value s.rightSlots)
    (naturalProduct value s.compensationSlots) XL XR 1 1

def naturalStep {σ : Type*} (s : MovingSlotReversal σ) (value : σ → ℕ)
    (pair : ℕ × ℕ) : ℕ × ℕ :=
  (s.naturalPivot value pair.1 pair.2, if s.left then pair.1 else pair.2)

/-- This is exactly the integer equation at a supported reversal. -/
def IntegralAt {σ : Type*} (s : MovingSlotReversal σ) (value : σ → ℕ)
    (pair : ℕ × ℕ) : Prop :=
  0 < s.naturalPivot value pair.1 pair.2 ∧
  s.leftFrequency * ((pair.2 * naturalProduct value s.rightSlots : ℕ) : ℤ) -
    s.rightFrequency * ((pair.1 * naturalProduct value s.leftSlots : ℕ) : ℤ) =
    s.rootFrequency * ((naturalProduct value s.compensationSlots *
      s.naturalPivot value pair.1 pair.2 : ℕ) : ℤ)

noncomputable def naturalReduction {σ : Type*} (q : ℕ) (value : σ → ℕ) :
    MvPolynomial σ ℤ →+* ZMod q :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod q)) (fun i => (value i : ZMod q))

theorem polynomial_step_integer {σ : Type*} {q : ℕ} [Fact q.Prime]
    (s : MovingSlotReversal σ) (value : σ → ℕ) (T : GiantRows (ZMod q))
    (x y : ZMod q) (pair : ℕ × ℕ)
    (hpair : T.eval x y = ((pair.1 : ZMod q), (pair.2 : ZMod q)))
    (hvalid : s.IntegralAt value pair)
    (hunit : naturalReduction q value s.polynomial.v ≠ 0 ∧
      naturalReduction q value s.polynomial.w ≠ 0 ∧ naturalReduction q value s.polynomial.u ≠ 0) :
    (T.movingReverse s.left (Units.mk0 (naturalReduction q value s.polynomial.v) hunit.1)
      (Units.mk0 (naturalReduction q value s.polynomial.w) hunit.2.1)
      (Units.mk0 (naturalReduction q value s.polynomial.u) hunit.2.2)).eval x y =
      (((s.naturalStep value pair).1 : ZMod q), ((s.naturalStep value pair).2 : ZMod q)) := by
  have hcast : ((if s.left then pair.1 else pair.2 : ℕ) : ZMod q) =
      if s.left then (pair.1 : ZMod q) else (pair.2 : ZMod q) := by
    split_ifs <;> rfl
  change _ = ((s.naturalPivot value pair.1 pair.2 : ZMod q),
    ((if s.left then pair.1 else pair.2 : ℕ) : ZMod q))
  rw [hcast]
  apply GiantRows.movingReverse_integer_node T s.left _ _ _ x y pair.1 pair.2
    (s.naturalPivot value pair.1 pair.2) (naturalProduct value s.leftSlots)
    (naturalProduct value s.rightSlots) 1 1 (naturalProduct value s.compensationSlots)
    s.rootFrequency s.leftFrequency s.rightFrequency hpair
  · simpa only [Units.val_mk0, polynomial, Nat.mul_one, naturalReduction] using
      coefficient_nat_eval (K := ZMod q) value s.leftFrequency s.rightSlots
  · simpa only [Units.val_mk0, polynomial, Nat.mul_one, naturalReduction] using
      coefficient_nat_eval (K := ZMod q) value s.rightFrequency s.leftSlots
  · simpa only [Units.val_mk0, polynomial, naturalReduction] using
      coefficient_nat_eval (K := ZMod q) value s.rootFrequency s.compensationSlots
  · simpa only [Nat.mul_one] using hvalid.2

end MovingSlotReversal

/-- A path is written with its newest reversal first, matching the cleared
row recursion. Each step is performed over the integers before reduction. -/
def movingSlotNaturalPath {σ : Type*} (value : σ → ℕ) :
    List (MovingSlotReversal σ) → (ℕ × ℕ) → ℕ × ℕ
  | [], pair => pair
  | s :: path, pair => s.naturalStep value (movingSlotNaturalPath value path pair)

def MovingSlotPathIntegral {σ : Type*} (value : σ → ℕ) :
    List (MovingSlotReversal σ) → (ℕ × ℕ) → Prop
  | [], _ => True
  | s :: path, pair => MovingSlotPathIntegral value path pair ∧
      s.IntegralAt value (movingSlotNaturalPath value path pair)

/-- The polynomial ancestor pair is the reduction of the actual integer
reversal path, rather than an unrelated invertible linear system. -/
theorem movingSlotNaturalPath_realized {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ)) (pair : ℕ × ℕ)
    (hvalid : MovingSlotPathIntegral value path pair)
    (hunit : ∀ s ∈ path,
      MovingSlotReversal.naturalReduction q value s.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value s.polynomial.w ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value s.polynomial.u ≠ 0) :
    let φ := MvPolynomial.eval₂Hom (Int.castRingHom (ZMod q))
        (fun i => (value i : ZMod q));
    ((movingPolynomialAncestors (path.map MovingSlotReversal.polynomial)).normalized φ).eval
        (pair.1 : ZMod q) (pair.2 : ZMod q) =
      (((movingSlotNaturalPath value path pair).1 : ZMod q),
       ((movingSlotNaturalPath value path pair).2 : ZMod q)) := by
  let φ := MvPolynomial.eval₂Hom (Int.castRingHom (ZMod q)) (fun i => (value i : ZMod q));
  induction path with
  | nil =>
    simp [movingPolynomialAncestors, PolynomialGiantRows.normalized,
      PolynomialGiantRows.identity, GiantRows.identity, GiantRows.eval, movingSlotNaturalPath]
  | cons s path ih =>
    have hs := hunit s (by simp)
    have ht := fun t ht => hunit t (List.mem_cons_of_mem _ ht)
    have hden : φ (movingPolynomialAncestors (path.map MovingSlotReversal.polynomial)).denominator ≠ 0 := by
      apply movingPolynomialAncestors_denominator
      intro t ht'
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht'
      exact (ht u hu).2.2
    change (((movingPolynomialAncestors (path.map MovingSlotReversal.polynomial)).movingReverse
      s.left s.polynomial.v s.polynomial.w s.polynomial.u).normalized φ).eval _ _ = _
    rw [PolynomialGiantRows.normalized_movingReverse _ φ _ _ _ _ hden hs.1 hs.2.1 hs.2.2]
    exact s.polynomial_step_integer value _ _ _ _ (ih hvalid.1 ht) hvalid.2 hs

end Ostmann

end OAI
