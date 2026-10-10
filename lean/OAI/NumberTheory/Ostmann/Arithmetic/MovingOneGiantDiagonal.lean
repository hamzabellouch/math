import OAI.NumberTheory.Ostmann.Arithmetic.MovingOneGiant
import OAI.NumberTheory.Ostmann.Arithmetic.MovingDiagonalEnergy

namespace OAI

/-! # Identifying the single giant on a product/frequency diagonal -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

local instance oneGiantDiagonalSum_neZero {J I : Type*} (Q : J → ℕ) (L : I → ℕ)
    [∀ j, NeZero (Q j)] [∀ i, NeZero (L i)] (i : J ⊕ I) :
    NeZero (Sum.elim Q L i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

/-- A prime in the giant range cannot be exchanged with any of the
regular primes when two complete products agree. -/
theorem oneGiant_product_eq {J : Type*} [Fintype J]
    (X Y : ℕ) (hX : X.Prime) (hY : Y.Prime)
    (p q : J → ℕ) (hq : ∀ i, (q i).Prime)
    (hsep : ∀ i, X ≠ q i)
    (he : X * ∏ i, p i = Y * ∏ i, q i) :
    X = Y ∧ (∏ i, p i) = ∏ i, q i := by
  have hd : X ∣ Y * ∏ i, q i := he ▸ Nat.dvd_mul_right X (∏ i, p i)
  have hXY : X ∣ Y := by
    rcases hX.dvd_mul.mp hd with h | h
    · exact h
    · obtain ⟨i, hi⟩ := prime_dvd_prime_product q hq X hX h
      exact (hsep i hi).elim
  have h := (Nat.dvd_prime hY).mp hXY
  have hEq : X = Y := h.resolve_left hX.ne_one
  exact ⟨hEq, Nat.eq_of_mul_eq_mul_left hX.pos (hEq ▸ he)⟩

/-- The full one-giant Fourier factor splits with its exact CRT cofactor.
The regular part is expressed only by its prime product. -/
theorem movingOneGiant_transform_product {J : Type*} [Fintype J]
    (X : ℕ) [Fact X.Prime] (p : J → ℕ) [∀ i, Fact (p i).Prime]
    (hp : Function.Injective p)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (D : ℕ) (v : ℤ) :
    movingRegularTransform (movingOneGiantModuli X p)
        (movingOneGiantFactors X p greg ggiant favorable) D v =
      (if favorable X then
        complexUnitPhase (ggiant X ((v : ZMod X) * ((D * ∏ i, p i : ℕ) : ZMod X)⁻¹))
       else 0) * primeProductTransform greg (D * X) (∏ i, p i) v := by
  calc
    _ = movingRegularTransform (fun _ : Unit => X)
        (fun _ t => if favorable X then complexUnitPhase (ggiant X t) else 0)
        (D * ∏ i, p i) v *
        movingRegularTransform p (fun j => greg (p j)) (D * ∏ _ : Unit, X) v := by
      convert moving_regular_transform_split (fun _ : Unit => X) p
        (fun _ t => if favorable X then complexUnitPhase (ggiant X t) else 0)
        (fun j => greg (p j)) D v using 1
      congr 1
      funext i
      cases i <;> rfl
    _ = _ := by
      rw [movingRegularTransform_eq_primeProduct p hp]
      simp only [movingRegularTransform, tupleCofactor, Finset.univ_unique,
        Finset.erase_singleton, Finset.prod_empty, Finset.prod_singleton, mul_one]

/-- The surviving giant is constant on every supported diagonal fibre.
Its unit phase can therefore be removed after grouping; the regular
prime-product transform and the original grouped coefficient remain. -/
theorem movingOneGiant_pivot_diagonal_le {A J : Type*} [Fintype A] [Fintype J]
    (X : A → ℕ) [∀ a, Fact (X a).Prime]
    (p : A → J → ℕ) [∀ a i, Fact (p a i).Prime]
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (D : ℕ) (v : A → ℤ) (W : A → ℂ)
    (hinj : ∀ a, W a ≠ 0 → Function.Injective (p a))
    (hv : ∀ a, W a ≠ 0 → v a ≠ 0)
    (hvg : ∀ a, W a ≠ 0 → (v a).natAbs < X a)
    (hvr : ∀ a, W a ≠ 0 → ∀ i, (v a).natAbs < p a i)
    (hsep : ∀ a b, W a ≠ 0 → W b ≠ 0 → ∀ i, X a ≠ p b i) :
    (pivotDiagonal (fun a => X a * ∏ i, p a i) v
      (fun a => W a * movingRegularTransform (movingOneGiantModuli (X a) (p a))
        (movingOneGiantFactors (X a) (p a) greg ggiant favorable) D (v a))).re ≤
    ∑ k ∈ Finset.univ.image (fun a => (X a, (∏ i, p a i), v a)),
      ‖primeProductTransform greg (D * k.1) k.2.1 k.2.2‖ ^ 2 *
        ‖groupedCoefficient (fun a => (X a, (∏ i, p a i), v a)) W k‖ ^ 2 := by
  let key := fun a => (X a, (∏ i, p a i), v a)
  let phase := fun k : ℕ × ℕ × ℤ =>
    if favorable k.1 then
      complexUnitPhase (ggiant k.1
        ((k.2.2 : ZMod k.1) * ((D * k.2.1 : ℕ) : ZMod k.1)⁻¹))
    else 0
  let regular := fun k : ℕ × ℕ × ℤ => primeProductTransform greg (D * k.1) k.2.1 k.2.2
  have hphase (k : ℕ × ℕ × ℤ) : ‖phase k‖ ≤ 1 := by
    dsimp only [phase]
    split_ifs
    · exact complexUnitPhase_norm_le _
    · simp only [norm_zero, zero_le_one]
  have hsmall a (ha : W a ≠ 0) q (hq : q.Prime) (hd : q ∣ X a * ∏ i, p a i) :
      (v a).natAbs < q := by
    rcases hq.dvd_mul.mp hd with hd | hd
    · have he := (Nat.dvd_prime (Fact.out : (X a).Prime)).mp hd
      rw [he.resolve_left hq.ne_one]
      exact hvg a ha
    · obtain ⟨i, rfl⟩ := prime_dvd_prime_product (p a) (fun i => Fact.out) q hq hd
      exact hvr a ha i
  have he : pivotDiagonal (fun a => X a * ∏ i, p a i) v
      (fun a => W a * movingRegularTransform (movingOneGiantModuli (X a) (p a))
        (movingOneGiantFactors (X a) (p a) greg ggiant favorable) D (v a)) =
      ∑ a, ∑ b, if key a = key b then
        (W a * (phase (key a) * regular (key a))) *
          conj (W b * (phase (key b) * regular (key b))) else 0 := by
    unfold pivotDiagonal
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases ha : W a = 0
    · simp only [ha, zero_mul, ite_self]
    by_cases hb : W b = 0
    · simp only [hb, zero_mul, map_zero, mul_zero, ite_self]
    have hz := pivot_zero_numerator_iff (X a * ∏ i, p a i) (X b * ∏ i, p b i)
      (Nat.mul_pos (Fact.out : (X a).Prime).pos
        (Finset.prod_pos (fun i _ => (Fact.out : (p a i).Prime).pos)))
      (v a) (v b) (hv a ha) (hv b hb) (hsmall a ha) (hsmall b hb)
    have hk : ((X a * ∏ i, p a i) = X b * ∏ i, p b i) ∧ v a = v b ↔ key a = key b := by
      constructor
      · rintro ⟨hp, hv⟩
        obtain ⟨hX, hR⟩ := oneGiant_product_eq (X a) (X b) Fact.out Fact.out
          (p a) (p b) (fun i => Fact.out) (hsep a b ha hb) hp
        exact Prod.ext hX (Prod.ext hR hv)
      · intro h
        have h' : X a = X b ∧ (∏ i, p a i) = ∏ i, p b i ∧ v a = v b := by
          simpa only [key, Prod.mk.injEq] using h
        exact ⟨by rw [h'.1, h'.2.1], h'.2.2⟩
    simp only [hz.trans hk]
    rw [movingOneGiant_transform_product (X a) (p a) (hinj a ha),
      movingOneGiant_transform_product (X b) (p b) (hinj b hb)]
  rw [he, finite_diagonal_common_transform key W (fun k => phase k * regular k)]
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_of_le_one_left (sq_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (hphase k))

/-- Cauchy on the identified fibre charges exactly its original prior mass.
There is no extra frequency cardinality or bound on each giant factor before
the diagonal has been grouped. -/
theorem movingOneGiant_weighted_pivot_diagonal_le {A J : Type*} [Fintype A] [Fintype J]
    (X : A → ℕ) [∀ a, Fact (X a).Prime]
    (p : A → J → ℕ) [∀ a i, Fact (p a i).Prime]
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (D : ℕ) (v : A → ℤ) (μ : A → ℝ) (W : A → ℂ) (θ : ℕ × ℕ × ℤ → ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hinj : ∀ a, (μ a : ℂ) * W a ≠ 0 → Function.Injective (p a))
    (hv : ∀ a, (μ a : ℂ) * W a ≠ 0 → v a ≠ 0)
    (hvg : ∀ a, (μ a : ℂ) * W a ≠ 0 → (v a).natAbs < X a)
    (hvr : ∀ a, (μ a : ℂ) * W a ≠ 0 → ∀ i, (v a).natAbs < p a i)
    (hsep : ∀ a b, (μ a : ℂ) * W a ≠ 0 → (μ b : ℂ) * W b ≠ 0 → ∀ i, X a ≠ p b i)
    (hmass : ∀ k, (∑ a, if (X a, (∏ i, p a i), v a) = k then μ a else 0) ≤ θ k) :
    (pivotDiagonal (fun a => X a * ∏ i, p a i) v
      (fun a => (μ a : ℂ) * W a * movingRegularTransform (movingOneGiantModuli (X a) (p a))
        (movingOneGiantFactors (X a) (p a) greg ggiant favorable) D (v a))).re ≤
    ∑ a, μ a * θ (X a, (∏ i, p a i), v a) *
      ‖W a * primeProductTransform greg (D * X a) (∏ i, p a i) (v a)‖ ^ 2 := by
  exact (movingOneGiant_pivot_diagonal_le X p greg ggiant favorable D v
    (fun a => (μ a : ℂ) * W a) hinj hv hvg hvr hsep).trans
    (finite_grouped_weighted_energy_le (fun a => (X a, (∏ i, p a i), v a)) μ W
      (fun k => primeProductTransform greg (D * k.1) k.2.1 k.2.2) θ hμ hmass)

end Ostmann

end OAI
