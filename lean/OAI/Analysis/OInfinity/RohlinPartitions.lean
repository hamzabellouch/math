import OAI.Analysis.OInfinity.DyadicProjections

namespace OAI

/-! # Concrete dyadic partitions for an even Cuntz row

The phases are explicit roots of unity. The finite partitions below use the
actual geometric CAR modes of the supplied even row, followed by the proved
Jordan–Wigner construction. Quantitative cyclic shift control is separate
from the exact partition identities.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

/-- The phase with half-period `2^i`. -/
def carDyadicPhase (i : ℕ) : ℂ := Complex.exp (((Real.pi / (2 : ℝ) ^ i : ℝ) : ℂ) * Complex.I)

lemma carDyadicPhase_norm (i : ℕ) : ‖carDyadicPhase i‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma carDyadicPhase_half (i : ℕ) : carDyadicPhase i ^ (2 ^ i) = -1 := by
  rw [carDyadicPhase, ← Complex.exp_nat_mul]
  have hp : (2 : ℂ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : ((2 ^ i : ℕ) : ℂ) * (((Real.pi / (2 : ℝ) ^ i : ℝ) : ℂ) * Complex.I) =
      (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [he, Complex.exp_pi_mul_I]

variable {E : Type*} [CStarAlgebra E] {n : ℕ}

/-- Commuting two-level coordinates of the actual even row. -/
def evenRohlinCoordinate (q : E) (r : Fin 2 × Fin n → E) (L i : ℕ) : E :=
  carJordanWigner q (evenBlockFamily r L carDyadicPhase) i

/-- The `k`th cell at dyadic level `m`. -/
def evenRohlinProjection (q : E) (r : Fin 2 × Fin n → E) (L m k : ℕ) : E :=
  dyadicSpinProjection q (evenRohlinCoordinate q r L) carDyadicPhase m k

variable (q : E) (r : Fin 2 × Fin n → E)
  (hqstar : star q = q) (hqq : q * q = q)
  (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
  (hsum : (∑ i, r i * star (r i)) = q)

include hqstar hqq hrow hsum in
lemma evenRohlinCoordinate_properties (L : ℕ) (hL : 0 < L) :
    (∀ i, q * evenRohlinCoordinate q r L i = evenRohlinCoordinate q r L i) ∧
    (∀ i, evenRohlinCoordinate q r L i * q = evenRohlinCoordinate q r L i) ∧
    (∀ i, evenRohlinCoordinate q r L i * evenRohlinCoordinate q r L i = 0) ∧
    (∀ i, star (evenRohlinCoordinate q r L i) * evenRohlinCoordinate q r L i +
      evenRohlinCoordinate q r L i * star (evenRohlinCoordinate q r L i) = q) ∧
    (∀ i j, Commute (evenRohlinCoordinate q r L i) (evenRohlinCoordinate q r L j)) ∧
    (∀ i j, i ≠ j → Commute (star (evenRohlinCoordinate q r L i))
      (evenRohlinCoordinate q r L j)) := by
  obtain ⟨hl, hr, ha, hg⟩ := evenBlockFamily_CAR q r hqstar hqq hrow hsum L hL
    carDyadicPhase carDyadicPhase_norm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (carJordanWigner_support q _ hqstar hqq hl hr ha hg i).1
  · intro i
    exact (carJordanWigner_support q _ hqstar hqq hl hr ha hg i).2
  · exact carJordanWigner_square_zero q _ hqstar hqq hl hr ha hg
  · exact carJordanWigner_gram q _ hqstar hqq hl hr ha hg
  · exact carJordanWigner_commute q _ hqstar hqq hl hr ha hg
  · exact carJordanWigner_star_commute q _ hqstar hqq hl hr ha hg

include hqstar hqq hrow hsum in
lemma evenRohlinProjection_partition (L : ℕ) (hL : 0 < L) (m : ℕ) :
    (∀ k, IsStarProjection (evenRohlinProjection q r L m k)) ∧
    (∑ k ∈ Finset.range (2 ^ m), evenRohlinProjection q r L m k) = q ∧
    (∀ k l, k < 2 ^ m → l < 2 ^ m → k ≠ l →
      evenRohlinProjection q r L m k * evenRohlinProjection q r L m l = 0) := by
  obtain ⟨hl, hr, hz, hg, hc, hsc⟩ := evenRohlinCoordinate_properties q r hqstar hqq hrow hsum L hL
  refine ⟨?_, ?_, ?_⟩
  · exact dyadicSpinProjection_isStarProjection q _ _ hqstar hqq hl hr hz hg hc hsc
      carDyadicPhase_norm m
  · exact dyadicSpinProjection_sum q _ _ hqstar hqq hl hr carDyadicPhase_half m
  · exact dyadicSpinProjection_orthogonal q _ _ hqstar hqq hl hr hz hg hc hsc
      carDyadicPhase_norm carDyadicPhase_half m

include hqstar hqq hrow hsum in
lemma evenRohlinProjection_support (L : ℕ) (hL : 0 < L) (m k : ℕ) :
    q * evenRohlinProjection q r L m k = evenRohlinProjection q r L m k ∧
      evenRohlinProjection q r L m k * q = evenRohlinProjection q r L m k := by
  obtain ⟨hl, hr, _, _, _, _⟩ := evenRohlinCoordinate_properties q r hqstar hqq hrow hsum L hL
  exact dyadicSpinProjection_support q _ _ hqstar hqq hl hr m k

include hqstar hqq hrow hsum in
lemma evenRohlinBlock_shift_error (L : ℕ) (hL : 0 < L) (i : ℕ) :
    ‖evenRowShift r (evenBlockFamily r L carDyadicPhase i) -
      carDyadicPhase i • evenBlockFamily r L carDyadicPhase i‖ ^ 2 ≤ 18 / (L : ℝ) :=
  evenEigenMode_shift_error q r hqstar hqq hrow hsum _ _ L hL _ (carDyadicPhase_norm i)

end WeakPureInfiniteness

end

end OAI
