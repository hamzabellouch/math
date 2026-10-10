import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularInverseBounds
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MatrixPacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChainWords
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasurePacking

namespace OAI

/-!
# Polynomial path packing for a concrete triangular representation

A proper left invariant metric compatible with an actual positive triangular
matrix embedding has polynomial packing for paths of bounded logarithmic
height. All coordinate and inverse estimates are proved here. No polynomial
packing hypothesis is imposed on this representation.
-/

namespace PolycyclicRecognition

open PositiveTriangular
open scoped Matrix.Norms.Operator

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
variable {n : ℕ} [NeZero n]

/-- Every bounded-height chain has a polynomially bounded endpoint matrix. -/
theorem chain_matrix_bound (ρ : G →* positiveTriangular n)
    (x : G) (L H V : ℝ) (hV : 0 ≤ V)
    (hstep : ∀ a, dist 1 a ≤ L → ‖matrix (ρ a)‖ ≤ V) :
    ∃ A : ℝ, 0 < A ∧ ∀ (t m : ℕ), m ≤ t → ∀ y,
      BoundedHeightChain (fun g => (height (ρ g)).toAdd) L H m x y →
      ‖matrix (ρ y)‖ ≤ A * (1 + (t : ℝ)) ^ n := by
  let c := (n : ℝ) * (1 + (Real.exp (2 * H) * V * Real.exp (2 * H) + 1)) ^ n * Real.exp (2 * H)
  let A := max 1 (‖matrix (ρ x)‖ * c)
  refine ⟨A, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t m hmt y hy
  obtain ⟨l, hlen, hprod, hls, hprefix⟩ := hy.exists_word
  have hx : ‖(height (ρ x)).toAdd‖ ≤ H := by simpa using hprefix [] l rfl
  have hp : ∀ p q : List G, p ++ q = l → ‖(height (ρ p.prod)).toAdd‖ ≤ 2 * H := by
    intro p q hpq
    have heq : (height (ρ p.prod)).toAdd =
        (height (ρ (x * p.prod))).toAdd - (height (ρ x)).toAdd := by
      simp only [map_mul, toAdd_mul]
      abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith [hprefix p q hpq])
  have hw := norm_mapped_word_prod_le ρ l hV (fun a ha => hstep a (hls a ha)) hp
  have hlen' : (l.length : ℝ) ≤ t := by exact_mod_cast hlen ▸ hmt
  have ht0 : 0 ≤ (1 + (l.length : ℝ)) := by positivity
  have hpow : (1 + (l.length : ℝ)) ^ n ≤ (1 + (t : ℝ)) ^ n :=
    pow_le_pow_left₀ ht0 (by linarith) n
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hw' : ‖matrix (ρ l.prod)‖ ≤ c * (1 + (l.length : ℝ)) ^ n := by
    convert hw using 1
    ring
  calc
    ‖matrix (ρ y)‖ = ‖matrix (ρ x) * matrix (ρ l.prod)‖ := by
      rw [← hprod, map_mul]
      rfl
    _ ≤ ‖matrix (ρ x)‖ * ‖matrix (ρ l.prod)‖ := norm_mul_le _ _
    _ ≤ ‖matrix (ρ x)‖ * (c * (1 + (l.length : ℝ)) ^ n) :=
      mul_le_mul_of_nonneg_left hw' (norm_nonneg _)
    _ ≤ ‖matrix (ρ x)‖ * (c * (1 + (t : ℝ)) ^ n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hc) (norm_nonneg _)
    _ = (‖matrix (ρ x)‖ * c) * (1 + (t : ℝ)) ^ n := by ring
    _ ≤ A * (1 + (t : ℝ)) ^ n :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The same region has a polynomial inverse-matrix bound. -/
theorem chain_inverse_matrix_bound (ρ : G →* positiveTriangular n)
    (x : G) (L H : ℝ) {A : ℝ} (hA : 0 < A)
    (hmat : ∀ (t m : ℕ), m ≤ t → ∀ y,
      BoundedHeightChain (fun g => (height (ρ g)).toAdd) L H m x y →
      ‖matrix (ρ y)‖ ≤ A * (1 + (t : ℝ)) ^ n) :
    ∃ B : ℝ, 0 < B ∧ ∀ (t m : ℕ), m ≤ t → ∀ y,
      BoundedHeightChain (fun g => (height (ρ g)).toAdd) L H m x y →
      ‖matrix ((ρ y)⁻¹)‖ ≤ B * (1 + (t : ℝ)) ^ (n * n) := by
  let B := max 1 (Real.exp H * ((n : ℝ) * (1 + (1 + A * Real.exp H)) ^ n))
  refine ⟨B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t m hmt y hy
  obtain ⟨l, _, hprod, _, hp⟩ := hy.exists_word
  have hhy : ‖(height (ρ y)).toAdd‖ ≤ H := by simpa only [hprod] using hp l [] (by simp)
  have hinv := norm_inverse_le (ρ y) (by positivity) (hmat t m hmt y hy) hhy
  have ht : 1 ≤ (1 + (t : ℝ)) ^ n := one_le_pow₀ (by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)])
  have hb : 1 + (1 + (A * (1 + (t : ℝ)) ^ n) * Real.exp H) ≤
      (1 + (1 + A * Real.exp H)) * (1 + (t : ℝ)) ^ n := by
    nlinarith
  calc
    _ ≤ Real.exp H * ((n : ℝ) *
        (1 + (1 + (A * (1 + (t : ℝ)) ^ n) * Real.exp H)) ^ n) := hinv
    _ ≤ Real.exp H * ((n : ℝ) *
        ((1 + (1 + A * Real.exp H)) * (1 + (t : ℝ)) ^ n) ^ n) := by
      gcongr
    _ = (Real.exp H * ((n : ℝ) * (1 + (1 + A * Real.exp H)) ^ n)) *
        (1 + (t : ℝ)) ^ (n * n) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ B * (1 + (t : ℝ)) ^ (n * n) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- A proper group with an actual positive triangular matrix embedding has
polynomial packing of bounded-logarithmic-height chains. This theorem proves
the packing property from the representation and topology. -/
theorem polynomialBoundedChainPacking_of_triangular_representation
    [ProperSpace G] [DecidableEq G]
    (ρ : G →* positiveTriangular n)
    (hρ : Topology.IsInducing (fun g => matrix (ρ g))) :
    PolynomialBoundedChainPacking (fun g => (height (ρ g)).toAdd) := by
  classical
  intro x L H _ _
  let σ : G →* (Matrix (Fin n) (Fin n) ℝ)ˣ := (positiveTriangular n).subtype.comp ρ
  obtain ⟨V, hV, hstep⟩ := exists_bounded_step_matrices σ hρ.continuous L
  obtain ⟨A, hA, hmat⟩ := chain_matrix_bound ρ x L H V hV hstep
  obtain ⟨B, hB, hinv⟩ := chain_inverse_matrix_bound ρ x L H hA hmat
  obtain ⟨ε, hε, hlocal⟩ := exists_local_matrix_metric_bound σ hρ
  obtain ⟨C, d, hpack⟩ := exists_polynomial_matrix_packing σ hε hA hB n (n * n) hlocal
  let S (t : ℕ) : Set G := {y | ∃ m ≤ t,
    BoundedHeightChain (fun g => (height (ρ g)).toAdd) L H m x y}
  have hnet (t : ℕ) : ∃ s : Finset G, (↑s : Set G) ⊆ S t ∧
      s.card ≤ C * (1 + t) ^ d ∧ ∀ y ∈ S t, ∃ z ∈ s, dist y z ≤ 1 := by
    apply finite_cover_set_of_separated_bound (S t) (by norm_num) (C * (1 + t) ^ d)
    intro s hs hsep
    apply hpack t s
    · intro y hy
      obtain ⟨m, hm, hchain⟩ := hs hy
      exact hmat t m hm y hchain
    · intro y hy
      obtain ⟨m, hm, hchain⟩ := hs hy
      exact hinv t m hm y hchain
    · exact hsep
  choose centers _ hcard hcover using hnet
  exact ⟨C, d, centers, hcard, fun t m hm y hy => hcover t y ⟨m, hm, hy⟩⟩

/-- If the diagonal characters of the representation factor through canonical
height, the same polynomial packing theorem applies to canonical-height
chains. Only this concrete factorization is needed from the representation. -/
theorem polynomialBoundedChainPacking_of_factored_triangular_representation
    [ProperSpace G] [DecidableEq G]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (π : G → W) (ρ : G →* positiveTriangular n)
    (hρ : Topology.IsInducing (fun g => matrix (ρ g)))
    (T : W →L[ℝ] (Fin n → ℝ))
    (hheight : ∀ g, (height (ρ g)).toAdd = T (π g)) : PolynomialBoundedChainPacking π := by
  apply polynomialBoundedChainPacking_of_height_domination π
    (fun g => (height (ρ g)).toAdd) ‖T‖ (norm_nonneg _)
  · intro g
    rw [hheight]
    exact T.le_opNorm _
  · exact polynomialBoundedChainPacking_of_triangular_representation ρ hρ

end PolycyclicRecognition

end OAI
