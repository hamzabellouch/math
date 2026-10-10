import OAI.Algebra.DepthFive.FockMonomials
import OAI.Algebra.DepthFive.MixedOperator

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Occupation update for one derivative or multiplication variable. Natural
subtraction is harmless when the derivative coefficient vanishes. -/
def stepOccupation (isV : σ → Bool) (i : σ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  if isV i then d - Finsupp.single i 1 else d + Finsupp.single i 1

/-- Occupation update for a variable path, in operator-composition order. -/
def pathOccupation (isV : σ → Bool) (l : List σ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  l.foldr (stepOccupation isV) d

/-- The nonnegative coefficient of one normalized creation/annihilation step. -/
def occupationAmplitude (isV : σ → Bool) (d : σ →₀ ℕ) (i : σ) : ℝ :=
  Real.sqrt (if isV i then (d i : ℝ) else (d i : ℝ) + 1)

omit [Fintype σ] [DecidableEq σ] in
lemma occupationAmplitude_nonneg (isV : σ → Bool) (d : σ →₀ ℕ) (i : σ) :
    0 ≤ occupationAmplitude isV d i := Real.sqrt_nonneg _

omit [Fintype σ] [DecidableEq σ] in
lemma stepOccupation_apply_of_ne (isV : σ → Bool) (d : σ →₀ ℕ)
    {i j : σ} (h : i ≠ j) : stepOccupation isV i d j = d j := by
  cases hi : isV i <;> simp [stepOccupation, hi, h]

omit [Fintype σ] [DecidableEq σ] in
lemma pathOccupation_apply_of_not_mem (isV : σ → Bool) (l : List σ)
    (d : σ →₀ ℕ) {i : σ} (h : i ∉ l) : pathOccupation isV l d i = d i := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hij : j ≠ i := by
      intro heq
      exact h (by simp [heq])
    have hil : i ∉ l := fun hi => h (List.mem_cons_of_mem _ hi)
    change stepOccupation isV j (pathOccupation isV l d) i = d i
    rw [stepOccupation_apply_of_ne isV _ hij, ih hil]

lemma variableOperator_complexFockMonomial (isV : σ → Bool)
    (d : σ →₀ ℕ) (i : σ) :
    variableOperator isV i (complexFockMonomial d) =
      (occupationAmplitude isV d i : ℂ) • complexFockMonomial (stepOccupation isV i d) := by
  cases h : isV i
  · simpa [occupationAmplitude, stepOccupation, h] using X_mul_complexFockMonomial d i
  · simpa [occupationAmplitude, stepOccupation, h] using pderiv_complexFockMonomial d i

/-- Exact factorial-normalized action of a product of distinct variables.
This is the sparse path-coefficient formula needed for IMM trace moments. -/
theorem mixedOperator_path_complexFockMonomial (isV : σ → Bool)
    (l : List σ) (hl : l.Nodup) (d : σ →₀ ℕ) :
    mixedOperator isV ((l.map (MvPolynomial.X : σ → MvPolynomial σ ℂ)).prod)
      (complexFockMonomial d) =
    (((l.map (occupationAmplitude isV d)).prod : ℝ) : ℂ) •
      complexFockMonomial (pathOccupation isV l d) := by
  induction l with
  | nil => simp [pathOccupation]
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.prod_cons]
    rw [mixedOperator_mul_apply, ih hl, map_smul, mixedOperator_X,
      variableOperator_complexFockMonomial, smul_smul]
    have hc : occupationAmplitude isV (pathOccupation isV l d) i =
        occupationAmplitude isV d i := by
      unfold occupationAmplitude
      rw [pathOccupation_apply_of_not_mem isV l d hi]
    rw [hc]
    change _ • complexFockMonomial (pathOccupation isV (i :: l) d) = _
    congr 1
    push_cast
    ring

omit [Fintype σ] [DecidableEq σ] in
/-- Squaring the normalized path amplitude gives exactly the occupation
polynomial, with no factorials or square roots left. -/
theorem pathAmplitude_sq (isV : σ → Bool) (l : List σ) (d : σ →₀ ℕ) :
    ((l.map (occupationAmplitude isV d)).prod) ^ 2 =
      (l.map (fun i => if isV i then (d i : ℝ) else (d i : ℝ) + 1)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, mul_pow, ih]
    congr 1
    apply Real.sq_sqrt
    cases isV i <;> positivity

omit [Fintype σ] [DecidableEq σ] in
lemma occupationAmplitude_eq_zero_iff (isV : σ → Bool) (d : σ →₀ ℕ) (i : σ) :
    occupationAmplitude isV d i = 0 ↔ isV i = true ∧ d i = 0 := by
  cases h : isV i
  · have hp : 0 < (d i : ℝ) + 1 := by positivity
    simp [occupationAmplitude, h, (Real.sqrt_pos.2 hp).ne']
  · simp [occupationAmplitude, h, Real.sqrt_eq_zero (Nat.cast_nonneg (d i))]

omit [Fintype σ] [DecidableEq σ] in
lemma pathAmplitude_eq_zero_iff (isV : σ → Bool) (l : List σ) (d : σ →₀ ℕ) :
    (l.map (occupationAmplitude isV d)).prod = 0 ↔
      ∃ i ∈ l, isV i = true ∧ d i = 0 := by
  simp only [List.prod_eq_zero_iff, List.mem_map, occupationAmplitude_eq_zero_iff]

/-- An occupation vector viewed as a signed exponent vector. -/
def signedOccupation (d : σ →₀ ℕ) : σ →₀ ℤ :=
  d.mapRange (fun n : ℕ => (n : ℤ)) (by simp)

omit [Fintype σ] [DecidableEq σ] in
@[simp] lemma signedOccupation_apply (d : σ →₀ ℕ) (i : σ) :
    signedOccupation d i = (d i : ℤ) := rfl

omit [Fintype σ] [DecidableEq σ] in
lemma signedOccupation_injective : Function.Injective (signedOccupation (σ := σ)) := by
  intro d e h
  ext i
  have hi := congrArg (fun x : σ →₀ ℤ => x i) h
  simp only [signedOccupation_apply] at hi
  exact_mod_cast hi

omit [Fintype σ] [DecidableEq σ] in
@[simp] lemma signedOccupation_eq_iff (d e : σ →₀ ℕ) :
    signedOccupation d = signedOccupation e ↔ d = e :=
  signedOccupation_injective.eq_iff

/-- The signed shift of a product of variable operators. -/
def occupationShift (isV : σ → Bool) (l : List σ) : σ →₀ ℤ :=
  (l.map (fun i => Finsupp.single i (if isV i then (-1 : ℤ) else 1))).sum

omit [Fintype σ] [DecidableEq σ] in
lemma signedOccupation_step (isV : σ → Bool) (d : σ →₀ ℕ) (i : σ)
    (hvalid : isV i = true → 0 < d i) :
    signedOccupation (stepOccupation isV i d) =
      signedOccupation d + Finsupp.single i (if isV i then (-1 : ℤ) else 1) := by
  classical
  ext j
  by_cases hij : i = j
  · subst j
    cases hside : isV i
    · simp [signedOccupation, stepOccupation, hside]
    · have hp := hvalid hside
      simp [signedOccupation, stepOccupation, hside]
      omega
  · cases hside : isV i <;> simp [signedOccupation, stepOccupation, hside, hij]

omit [Fintype σ] [DecidableEq σ] in
lemma signedOccupation_path_of_valid (isV : σ → Bool) (l : List σ)
    (hl : l.Nodup) (d : σ →₀ ℕ)
    (hvalid : ∀ i ∈ l, isV i = true → 0 < d i) :
    signedOccupation (pathOccupation isV l d) = signedOccupation d + occupationShift isV l := by
  induction l with
  | nil => simp [pathOccupation, occupationShift]
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
    have hv : isV i = true → 0 < pathOccupation isV l d i := by
      rw [pathOccupation_apply_of_not_mem isV l d hi]
      exact hvalid i (by simp)
    have htail := ih hl (fun j hj => hvalid j (List.mem_cons_of_mem _ hj))
    change signedOccupation (stepOccupation isV i (pathOccupation isV l d)) = _
    rw [signedOccupation_step isV _ i hv, htail]
    simp [occupationShift, add_comm, add_left_comm]

omit [Fintype σ] [DecidableEq σ] in
/-- A nonzero path amplitude guarantees that natural subtraction agrees with
the signed path shift, including at every intermediate occupation. -/
theorem signedOccupation_path_of_amplitude_ne_zero (isV : σ → Bool) (l : List σ)
    (hl : l.Nodup) (d : σ →₀ ℕ)
    (hamp : (l.map (occupationAmplitude isV d)).prod ≠ 0) :
    signedOccupation (pathOccupation isV l d) = signedOccupation d + occupationShift isV l := by
  apply signedOccupation_path_of_valid isV l hl d
  intro i hi hs
  by_contra h
  have hz : d i = 0 := by omega
  exact hamp ((pathAmplitude_eq_zero_iff isV l d).2 ⟨i, hi, hs, hz⟩)

end Problem335

end

end OAI
