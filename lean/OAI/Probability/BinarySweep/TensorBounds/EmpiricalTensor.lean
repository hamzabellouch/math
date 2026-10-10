import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.TensorPhases

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A : Type*} [Fintype A] [DecidableEq A]

def tensorAmplitude (n : ℕ) (r : A → ℝ) (w : Fin n → A) : ℝ := ∏ i, Real.sqrt (r (w i))

def tensorProductVector (n : ℕ) (v : A → ℂ) : (Fin n → A) → ℂ := fun w => ∏ i, v (w i)

def phasedVector (n : ℕ) (r : A → ℝ) (θ : A → ZMod (n+1)) : A → ℂ :=
  fun a => (Real.sqrt (r a) : ℂ) * ZMod.stdAddChar (θ a)

omit [Fintype A] [DecidableEq A] in
lemma tensorProductVector_phased (n : ℕ) (r : A → ℝ) (θ : A → ZMod (n+1)) (w : Fin n → A) :
    tensorProductVector n (phasedVector n r θ) w =
      (tensorAmplitude n r w : ℂ) * tensorPhase n θ w := by
  simp only [tensorProductVector, phasedVector, tensorAmplitude, tensorPhase,
    Finset.prod_mul_distrib, Complex.ofReal_prod]

lemma tensorAmplitude_counts (n : ℕ) (r : A → ℝ) (w : Fin n → A) :
    tensorAmplitude n r w = ∏ a, Real.sqrt (r a)^wordCounts w a :=
  prod_wordCounts (fun a => Real.sqrt (r a)) w

lemma tensorAmplitude_sq (n : ℕ) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a) (w : Fin n → A) :
    tensorAmplitude n r w * tensorAmplitude n r w = ∏ a, (r a)^wordCounts w a := by
  rw [tensorAmplitude_counts, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a ha
  rw [← mul_pow, Real.mul_self_sqrt (hr a)]

def phaseAverage (n : ℕ) (r : A → ℝ) : Matrix (Fin n → A) (Fin n → A) ℂ :=
  (((n+1 : ℕ) : ℂ)^Fintype.card A)⁻¹ •
    ∑ θ : A → ZMod (n+1), rankOne (tensorProductVector n (phasedVector n r θ))

lemma phaseAverage_psd (n : ℕ) (r : A → ℝ) : (phaseAverage n r).PosSemidef := by
  apply Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ (fun θ _ => rankOne_psd _))
  exact inv_nonneg.mpr (pow_nonneg (by exact_mod_cast Nat.zero_le (n+1)) _)

lemma phaseAverage_apply (n : ℕ) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a)
    (w v : Fin n → A) :
    phaseAverage n r w v = if wordCounts w = wordCounts v then
      ((∏ a, r a^wordCounts w a : ℝ) : ℂ) else 0 := by
  simp only [phaseAverage, Matrix.smul_apply, Matrix.sum_apply, rankOne, vecMulVec,
    Matrix.of_apply, Pi.star_apply, tensorProductVector_phased, star_mul, Complex.star_def,
    Complex.conj_ofReal]
  have hfactor : (∑ θ : A → ZMod (n+1),
        ((tensorAmplitude n r w : ℂ) * tensorPhase n θ w) *
          (star (tensorPhase n θ v) * (tensorAmplitude n r v : ℂ))) =
      ((tensorAmplitude n r w : ℂ) * (tensorAmplitude n r v : ℂ)) *
        ∑ θ : A → ZMod (n+1), tensorPhase n θ w * star (tensorPhase n θ v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro θ hθ
    ring
  change (((n+1 : ℕ) : ℂ)^Fintype.card A)⁻¹ * _ = _
  simp only [Complex.star_def] at hfactor
  rw [hfactor]
  change _ * (_ * ∑ θ : A → ZMod (n+1), tensorPhase n θ w * star (tensorPhase n θ v)) = _
  rw [phase_pair_sum]
  by_cases h : wordCounts w = wordCounts v
  · rw [ite_eq_left h, ite_eq_left h]
    have ha : tensorAmplitude n r w = tensorAmplitude n r v := by
      simp only [tensorAmplitude_counts, h]
    rw [← ha, ← Complex.ofReal_mul, tensorAmplitude_sq n r hr w]
    have hp : (((n+1 : ℕ) : ℂ)^Fintype.card A) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero n)
    field_simp
  · simp [h]

lemma phaseAverage_kernel (n : ℕ) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a) :
    phaseAverage n r = ∑ c : WordType A n,
      ((∏ a, r a ^ c.val a : ℝ) : ℂ) • typeOnes (wordType n) c := by
  ext w v
  rw [phaseAverage_apply n r hr, sum_typeOnes]
  simp only [wordType_eq_iff]
  rfl

omit [Fintype A] [DecidableEq A] in
lemma phasedVector_norm (n : ℕ) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a)
    (θ : A → ZMod (n+1)) (a : A) :
    phasedVector n r θ a * star (phasedVector n r θ a) = (r a : ℂ) := by
  have he : ZMod.stdAddChar (θ a) * star (ZMod.stdAddChar (θ a)) = 1 := by
    rw [phase_star, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  simp only [phasedVector, star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (r a) : ℂ) * Real.sqrt (r a)) *
        (ZMod.stdAddChar (θ a) * star (ZMod.stdAddChar (θ a))) := by simp only [Complex.star_def]; ring
    _ = _ := by rw [he, mul_one, ← Complex.ofReal_mul, Real.mul_self_sqrt (hr a)]

omit [DecidableEq A] in
lemma phasedVector_trace (n : ℕ) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a)
    (hs : ∑ a, r a = 1) (θ : A → ZMod (n+1)) :
    Matrix.trace (rankOne (phasedVector n r θ)) = 1 := by
  simp only [Matrix.trace, Matrix.diag, rankOne, vecMulVec, Matrix.of_apply, Pi.star_apply,
    phasedVector_norm n r hr, ← Complex.ofReal_sum, hs, Complex.ofReal_one]

end BinaryCoordinateSweeps.Density

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {A : Type*} [Fintype A] [DecidableEq A]

def empirical (n : ℕ) (c : WordType A n) : A → ℝ := fun a => c.val a / (n : ℝ)

lemma empirical_nonneg (n : ℕ) (c : WordType A n) (a : A) : 0 ≤ empirical n c a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma empirical_sum (n : ℕ) (hn : 0 < n) (c : WordType A n) : ∑ a, empirical n c a = 1 := by
  simp only [empirical, ← Finset.sum_div, ← Nat.cast_sum, wordType_total,
    div_self (by exact_mod_cast Nat.ne_of_gt hn : (n : ℝ) ≠ 0)]

lemma type_mass_inv (n : ℕ) (hn : 0 < n) (c : WordType A n) :
    (Nat.multinomial Finset.univ c.val : ℝ)⁻¹ ≤
      ((n+1 : ℕ) : ℝ)^Fintype.card A * ∏ a, empirical n c a ^ c.val a := by
  have hm : 0 < (Nat.multinomial Finset.univ c.val : ℝ) := by exact_mod_cast Nat.multinomial_pos _ _
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hm).mpr
  have hh := type_mass_lower n hn c.val (wordType_total n c)
  simpa only [empirical, mul_assoc, mul_left_comm, mul_comm] using hh

theorem finite_postselection (n : ℕ) (hn : 0 < n) :
    ((((n+1 : ℕ) : ℂ)^Fintype.card A) •
      (∑ c : WordType A n, phaseAverage n (empirical n c)) - symmetricProjector n).PosSemidef := by
  let d : WordType A n → ℝ := fun t => ((n+1 : ℕ) : ℝ)^Fintype.card A *
    ∑ c : WordType A n, ∏ a, empirical n c a ^ t.val a
  have hd (t : WordType A n) : (Nat.multinomial Finset.univ t.val : ℝ)⁻¹ ≤ d t := by
    refine (type_mass_inv n hn t).trans ?_
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
    exact Finset.single_le_sum (f := fun c : WordType A n => ∏ a, empirical n c a ^ t.val a)
      (fun c _ => Finset.prod_nonneg
        (fun a _ => pow_nonneg (empirical_nonneg n c a) _)) (Finset.mem_univ t)
  convert typeKernel_mono (wordType (A := A) n)
    (fun t => (Nat.multinomial Finset.univ t.val : ℝ)⁻¹) d hd using 1
  apply Iff.of_eq
  congr 1
  ext w v
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
    phaseAverage_apply n _ (empirical_nonneg n _), symmetricProjector, smul_eq_mul,
    wordType_eq_iff, Pi.sub_apply]
  split_ifs with h
  · simp only [d, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast,
      Complex.ofReal_sum, Complex.ofReal_inv]
    rfl
  · simp

end BinaryCoordinateSweeps.Density

end

end OAI
