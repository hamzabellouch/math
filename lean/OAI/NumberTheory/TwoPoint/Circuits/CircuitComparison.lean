import OAI.NumberTheory.TwoPoint.Circuits.FourierCorrection

namespace OAI

/-!
# Bounded-independence circuit comparison after Fourier correction

The comparison uses the fixed-depth specialization of Mark Braverman,
*Polylogarithmic independence fools AC⁰ circuits*, J. ACM 57 (2010), Article 28,
Corollary 2 in the author's version. We use depth 22, with absolute constants
and natural logarithms. Circuits below have actual finite syntax: literals
and arbitrary finite-fan-in AND/OR gates. They are tree circuits, a subclass
of the circuits covered by Braverman's theorem. The size counts both input
occurrences and gates; the depth counts AND/OR levels.
-/

namespace TwoPointCorrelations

open Finset

/-- Finite AC⁰ syntax in negation normal form. Sharing is not needed for the
finite residue tests; literals can have either polarity. -/
inductive AC0Circuit (n : ℕ) where
  | literal (i : Fin n) (positive : Bool)
  | andGate {k : ℕ} (children : Fin k → AC0Circuit n)
  | orGate {k : ℕ} (children : Fin k → AC0Circuit n)

namespace AC0Circuit

/-- Evaluation on a Boolean input vector. Empty AND/OR gates are true/false. -/
def eval {n : ℕ} : AC0Circuit n → BooleanCube n → Bool
  | .literal i positive, x => if positive then x i else !(x i)
  | .andGate children, x => decide (∀ i, eval (children i) x = true)
  | .orGate children, x => decide (∃ i, eval (children i) x = true)

/-- AND/OR depth, with literals at depth zero. -/
def depth {n : ℕ} : AC0Circuit n → ℕ
  | .literal _ _ => 0
  | .andGate children => 1 + Finset.univ.sup (fun i => depth (children i))
  | .orGate children => 1 + Finset.univ.sup (fun i => depth (children i))

/-- Gates plus input occurrences. -/
def size {n : ℕ} : AC0Circuit n → ℕ
  | .literal _ _ => 1
  | .andGate children => 1 + ∑ i, size (children i)
  | .orGate children => 1 + ∑ i, size (children i)

lemma size_pos {n : ℕ} (c : AC0Circuit n) : 0 < c.size := by
  cases c <;> simp [size]

/-- Real indicator of the circuit accepting its input. -/
noncomputable def indicator {n : ℕ} (c : AC0Circuit n) (x : BooleanCube n) : ℝ :=
  if c.eval x then 1 else 0

lemma abs_centered_indicator {n : ℕ} (c : AC0Circuit n) (x : BooleanCube n) :
    |c.indicator x - 1 / 2| = (1 / 2 : ℝ) := by
  unfold indicator
  cases c.eval x <;> norm_num

end AC0Circuit

/-- Braverman's Corollary 2 at depth twenty-two. The constants absorb a
choice of logarithm base. Distributions are represented by nonnegative
densities relative to the uniform law on the Boolean cube. -/
def BravermanDepth22Input : Prop :=
  ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ (n : ℕ) (c : AC0Circuit n), c.depth ≤ 22 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
      (K : ℝ) * (Real.log ((c.size : ℝ) / ε)) ^ C ≤ (t : ℝ) →
      ∀ g : BooleanCube n → ℝ, (∀ x, 0 ≤ g x) → cubeAverage g = 1 →
        TWiseUniformDensity g t →
        |cubeAverage (fun x => g x * c.indicator x) - cubeAverage c.indicator| ≤ ε

lemma abs_cubeAverage_le {n : ℕ} (f : BooleanCube n → ℝ) :
    |cubeAverage f| ≤ cubeAverage (fun x => |f x|) := by
  unfold cubeAverage
  rw [abs_div, show |(Fintype.card (BooleanCube n) : ℝ)| =
    (Fintype.card (BooleanCube n) : ℝ) from abs_of_nonneg (Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/-- For measures of equal total mass, an event difference is bounded by one
half of the mean absolute density difference. -/
lemma circuit_event_le_totalVariation {n : ℕ} (c : AC0Circuit n)
    (f g : BooleanCube n → ℝ) (hmass : cubeAverage f = cubeAverage g) :
    |cubeAverage (fun x => f x * c.indicator x) -
      cubeAverage (fun x => g x * c.indicator x)| ≤
        cubeAverage (fun x => |f x - g x|) / 2 := by
  have hzero : cubeAverage (fun x => f x - g x) = 0 := by
    rw [cubeAverage_sub, hmass, sub_self]
  have heq : cubeAverage (fun x => f x * c.indicator x) -
      cubeAverage (fun x => g x * c.indicator x) =
      cubeAverage (fun x => (f x - g x) * (c.indicator x - 1 / 2)) := by
    have hpoint : (fun x => (f x - g x) * (c.indicator x - 1 / 2)) =
        (fun x => (f x * c.indicator x - g x * c.indicator x) -
          (1 / 2 : ℝ) * (f x - g x)) := by
      funext x
      ring
    rw [hpoint, cubeAverage_sub, cubeAverage_sub, cubeAverage_mul_const, hzero]
    ring
  rw [heq]
  apply (abs_cubeAverage_le _).trans
  have hpoint : (fun x => |(f x - g x) * (c.indicator x - 1 / 2)|) =
      (fun x => (1 / 2 : ℝ) * |f x - g x|) := by
    funext x
    rw [abs_mul, c.abs_centered_indicator]
    ring
  rw [hpoint, cubeAverage_mul_const]
  exact le_of_eq (by ring)

/-- Fourier correction followed by Braverman's published theorem compares
the original density against uniform inputs, with the correction error
made explicit. -/
theorem BravermanDepth22Input.fourier_comparison (hBraverman : BravermanDepth22Input) :
    ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ (n : ℕ) (c : AC0Circuit n), c.depth ≤ 22 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log ((c.size : ℝ) / ε)) ^ C ≤ (t : ℝ) →
        ∀ (f : BooleanCube n → ℝ) (a : ℝ),
          (∀ x, 0 ≤ f x) → cubeAverage f = 1 → 0 ≤ a → lowWalshMass f t ≤ a →
          |cubeAverage (fun x => f x * c.indicator x) - cubeAverage c.indicator| ≤
            3 * a / 2 + ε := by
  obtain ⟨K, C, hK, hC, hbound⟩ := hBraverman
  refine ⟨K, C, hK, hC, ?_⟩
  intro n c hdepth ε hε hεmax t ht f a hf hmean ha hmass
  let g := correctedCubeDensity f t a
  have hcorr := fourierCorrection f t a hf hmean ha hmass
  have hBrav := hbound n c hdepth ε hε hεmax t ht g hcorr.1 hcorr.2.1 hcorr.2.2.1
  have hTV := circuit_event_le_totalVariation c f g (hmean.trans hcorr.2.1.symm)
  have hTVbound : cubeAverage (fun x => |f x - g x|) / 2 ≤ 3 * a / 2 := by
    simpa only [abs_sub_comm] using hcorr.2.2.2
  calc
    |cubeAverage (fun x => f x * c.indicator x) - cubeAverage c.indicator| ≤
        |cubeAverage (fun x => f x * c.indicator x) -
          cubeAverage (fun x => g x * c.indicator x)| +
        |cubeAverage (fun x => g x * c.indicator x) - cubeAverage c.indicator| :=
      abs_sub_le _ _ _
    _ ≤ 3 * a / 2 + ε := add_le_add (hTV.trans hTVbound) hBrav

end TwoPointCorrelations

end OAI
