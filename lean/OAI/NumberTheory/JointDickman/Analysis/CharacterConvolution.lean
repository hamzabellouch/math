import OAI.NumberTheory.JointDickman.Analysis.CharacterInputs
import OAI.NumberTheory.JointDickman.Arithmetic.RoughSelbergDelange

namespace OAI

/-! # Exact character-twisted roughness convolution -/

namespace JointDickman

open Finset ArithmeticFunction

noncomputable def characterTwist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => (f n : ℂ) * χ (n : ZMod q), by simp⟩

@[simp] theorem characterTwist_apply {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℝ) (n : ℕ) :
    characterTwist χ f n = (f n : ℂ) * χ (n : ZMod q) := rfl

theorem characterTwist_mul {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℝ) :
    characterTwist χ (f * g) = characterTwist χ f * characterTwist χ g := by
  ext n
  simp only [characterTwist_apply, mul_apply, Complex.ofReal_sum]
  rw [sum_mul]
  apply sum_congr rfl
  intro ab hab
  have hmul : ab.1 * ab.2 = n := (Nat.mem_divisorsAntidiagonal.mp hab).1
  rw [← hmul, Nat.cast_mul, map_mul, Complex.ofReal_mul]
  ring

noncomputable def roughCharacterSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (E : Finset ℕ) (z Y : ℝ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊Y⌋₊, (roughSquarefreeWeight E z n : ℂ) * χ (n : ZMod q)

noncomputable def characterConvolutionTail {q : ℕ} (χ : DirichletCharacter ℂ q)
    (E : Finset ℕ) (z : ℝ) (N V : ℕ) : ℂ :=
  ∑ v ∈ Ioc V N, (smoothCorrection E z v : ℂ) * χ (v : ZMod q) *
    squarefreeCharacterSum χ z ((N / v : ℕ) : ℝ)

theorem roughCharacterSum_split {q : ℕ} (χ : DirichletCharacter ℂ q)
    (E : Finset ℕ) (z Y : ℝ) (V : ℕ) (hV : V ≤ ⌊Y⌋₊) :
    roughCharacterSum χ E z Y =
      (∑ v ∈ Ioc 0 V, (smoothCorrection E z v : ℂ) * χ (v : ZMod q) *
        squarefreeCharacterSum χ z (Y / v)) +
      characterConvolutionTail χ E z ⌊Y⌋₊ V := by
  have hconv := congrArg (characterTwist χ) (squarefreeWeight_mul_smoothCorrection E z)
  rw [characterTwist_mul, mul_comm] at hconv
  change (∑ n ∈ Ioc 0 ⌊Y⌋₊, characterTwist χ (roughSquarefreeWeight E z) n) = _
  rw [← hconv, sum_Ioc_mul_eq_sum_sum,
    ← Ioc_union_Ioc_eq_Ioc (Nat.zero_le V) hV, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  congr 1
  · apply sum_congr rfl
    intro v _
    simp only [characterTwist_apply, squarefreeCharacterSum, Nat.floor_div_natCast]
  · simp only [characterConvolutionTail, squarefreeCharacterSum, Nat.floor_natCast,
      characterTwist_apply]

theorem squarefreeCharacterSum_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (N : ℕ) :
    ‖squarefreeCharacterSum χ z N‖ ≤ N := by
  unfold squarefreeCharacterSum
  rw [Nat.floor_natCast]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖(squarefreeWeight z n : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ (1 : ℝ) * 1 := mul_le_mul (squarefreeWeight_abs_le_one hz hz1 n)
          (χ.norm_le_one _) (norm_nonneg _) zero_le_one
        _ = _ := by ring
    _ = _ := by simp

/-- Twisting cannot enlarge the Rankin remainder. -/
theorem characterConvolutionTail_rankin {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) {z ε : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hε : 0 ≤ ε) (N V : ℕ) (hV : 0 < V) :
    ‖characterConvolutionTail χ E z N V‖ ≤
      ((N : ℝ) / (V : ℝ) ^ ε) *
        ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) ^ (1 - ε) := by
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  have htail := harmonic_tail_rankin (Ioc V N) (fun v : ℕ => (v : ℝ))
    (fun v => |smoothCorrection E z v|) hV' hε
    (fun v hv => by exact_mod_cast (mem_Ioc.mp hv).1.le)
    (fun _ _ => abs_nonneg _)
  calc
    _ ≤ (N : ℝ) * ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) := by
      unfold characterConvolutionTail
      rw [mul_sum]
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro v hv
      have hvpos : (0 : ℝ) < v := by exact_mod_cast
        ((mem_Ioc.mp hv).1.trans_le' (Nat.zero_le V))
      have hfloor : ((N / v : ℕ) : ℝ) ≤ (N : ℝ) / v := by
        apply (le_div_iff₀ hvpos).mpr
        exact_mod_cast Nat.div_mul_le_self N v
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ |smoothCorrection E z v| * ((N / v : ℕ) : ℝ) :=
          mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _))
            (squarefreeCharacterSum_norm_le χ hz hz1 _) (norm_nonneg _) (abs_nonneg _)
        _ ≤ |smoothCorrection E z v| * ((N : ℝ) / v) :=
          mul_le_mul_of_nonneg_left hfloor (abs_nonneg _)
        _ = _ := by ring
    _ ≤ (N : ℝ) * ((∑ v ∈ Ioc V N, |smoothCorrection E z v| /
        (v : ℝ) ^ (1 - ε)) / (V : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
    _ = _ := by ring

end JointDickman

end OAI
