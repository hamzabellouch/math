import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Basic.Complex.Basic

namespace OAI
/-!
# Finite hyperbola reindexing for Vaughan sums

An exact finite change of variables from `n = a*b` to pairs of positive
integers below a hyperbola. The arbitrary weight version is suitable for
both rational additive characters and real-frequency exponential sums.
-/

noncomputable section
open scoped BigOperators

namespace Problem337.Vaughan

/-- Positive lattice points below the multiplicative hyperbola `a*b ≤ N`. -/
def hyperbola (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter (fun ab => ab.1 * ab.2 ≤ N)

@[simp] lemma mem_hyperbola {N a b : ℕ} :
    (a, b) ∈ hyperbola N ↔ 1 ≤ a ∧ 1 ≤ b ∧ a * b ≤ N := by
  change ((a, b) ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun ab => ab.1 * ab.2 ≤ N)) ↔ _
  rw [Finset.mem_filter]
  have hm : (a, b) ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N) ↔
      a ∈ Finset.Icc 1 N ∧ b ∈ Finset.Icc 1 N := Finset.mem_product
  rw [hm]
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha, _⟩, ⟨hb, _⟩⟩, hp⟩
    exact ⟨ha, hb, hp⟩
  · rintro ⟨ha, hb, hp⟩
    have haN : a ≤ N := (Nat.le_mul_of_pos_right a (by omega : 0 < b)).trans hp
    have hbN : b ≤ N := (Nat.le_mul_of_pos_left b (by omega : 0 < a)).trans hp
    exact ⟨⟨⟨ha, haN⟩, ⟨hb, hbN⟩⟩, hp⟩

/-- The divisor-antidiagonal fibers partition the positive hyperbola exactly.
The summand may also depend on the product index `n`. -/
theorem sum_divisor_fibers {A : Type*} [AddCommMonoid A]
    (N : ℕ) (F : ℕ → ℕ → ℕ → A) :
    (∑ n ∈ Finset.Icc 1 N, ∑ ab ∈ n.divisorsAntidiagonal, F n ab.1 ab.2) =
      ∑ ab ∈ hyperbola N, F (ab.1 * ab.2) ab.1 ab.2 := by
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun x : Sigma (fun _n : ℕ => ℕ × ℕ) => x.2)
    (fun ab : ℕ × ℕ => (⟨ab.1 * ab.2, ab⟩ : Sigma (fun _n : ℕ => ℕ × ℕ)))
  · rintro ⟨n, a, b⟩ hx
    obtain ⟨hn, hab⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    apply mem_hyperbola.mpr
    change a * b = n at hprod
    change n ≠ 0 at hn0
    have hab0 : a * b ≠ 0 := by rw [hprod]; exact hn0
    exact ⟨Nat.pos_of_ne_zero (left_ne_zero_of_mul hab0),
      Nat.pos_of_ne_zero (right_ne_zero_of_mul hab0), by rw [hprod]; exact hnN⟩
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb, hp⟩ := mem_hyperbola.mp hab
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨Nat.mul_pos ha hb, hp⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  · rintro ⟨n, a, b⟩ hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    change (⟨a * b, (a, b)⟩ : Sigma (fun _n : ℕ => ℕ × ℕ)) = ⟨n, (a, b)⟩
    rw [hprod]
  · intro ab hab
    rfl
  · rintro ⟨n, a, b⟩ hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    change F n a b = F (a * b) a b
    rw [hprod]

/-- The hyperbola sum as ordinary nested integer intervals. The inner endpoint
is the natural-number quotient `N / a`; the outer interval excludes zero. -/
theorem sum_hyperbola_eq_nested {A : Type*} [AddCommMonoid A]
    (N : ℕ) (F : ℕ → ℕ → A) :
    (∑ ab ∈ hyperbola N, F ab.1 ab.2) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), F a b := by
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ab : ℕ × ℕ => (⟨ab.1, ab.2⟩ : Sigma (fun _a : ℕ => ℕ)))
    (fun x : Sigma (fun _a : ℕ => ℕ) => (x.1, x.2))
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb, hp⟩ := mem_hyperbola.mp hab
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨ha,
        (Nat.le_mul_of_pos_right a (by omega : 0 < b)).trans hp⟩
    · apply Finset.mem_Icc.mpr
      exact ⟨hb, (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr (by simpa [mul_comm] using hp)⟩
  · rintro ⟨a, b⟩ hx
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.mp hx
    obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hb
    change 1 ≤ a at ha1
    change 1 ≤ b at hb1
    change b ≤ N / a at hbN
    apply mem_hyperbola.mpr
    refine ⟨ha1, hb1, ?_⟩
    have hp := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp hbN
    simpa [mul_comm] using hp
  · intro ab hab
    rfl
  · intro x hx
    rfl
  · intro ab hab
    rfl

/-- Exact finite convolution reindexing with an arbitrary multiplicative
weight. No convergence or support hypotheses on the weight are needed. -/
theorem sum_convolution_hyperbola {R : Type*} [Semiring R]
    (N : ℕ) (f g : ArithmeticFunction R) (w : ℕ → R) :
    (∑ n ∈ Finset.Icc 1 N, (f * g) n * w n) =
      ∑ ab ∈ hyperbola N, (f ab.1 * g ab.2) * w (ab.1 * ab.2) := by
  simp_rw [ArithmeticFunction.mul_apply, Finset.sum_mul]
  exact sum_divisor_fibers N (fun n a b => (f a * g b) * w n)

/-- Real arithmetic coefficients with complex weights, the combination used
for the von-Mangoldt exponential sum. -/
theorem sum_real_convolution_hyperbola
    (N : ℕ) (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, ((f * g) n : ℂ) * w n) =
      ∑ ab ∈ hyperbola N, ((f ab.1 * g ab.2 : ℝ) : ℂ) * w (ab.1 * ab.2) := by
  simp_rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Finset.sum_mul]
  exact sum_divisor_fibers N (fun n a b => ((f a * g b : ℝ) : ℂ) * w n)

/-- The traditional nested-interval form of the finite convolution identity. -/
theorem sum_real_convolution_eq_nested
    (N : ℕ) (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, ((f * g) n : ℂ) * w n) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a),
        ((f a * g b : ℝ) : ℂ) * w (a * b) := by
  rw [sum_real_convolution_hyperbola]
  exact sum_hyperbola_eq_nested (A := ℂ) N
    (fun a b => ((f a * g b : ℝ) : ℂ) * w (a * b))

end Problem337.Vaughan

end

end OAI
