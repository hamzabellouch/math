import OAI.NumberTheory.TwoPoint.Bounds.IntegerShiftGeometry

namespace OAI

/-! Exact normalization of a closed numerical word, counting repeated visits. -/

namespace TwoPointCorrelations

open scoped Classical

/-- Multiply departure-indexed edge coefficients along the actual integer walk. -/
noncomputable def scalarWalkProduct (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (n : ℤ) : List SignedStep → ℝ
  | [] => 1
  | a :: w => weight a n * scalarWalkProduct h weight (n + a.displacement h) w

lemma scalarWalkProduct_mul (h : ℕ) (a b : SignedStep → ℤ → ℝ)
    (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h (fun t x => a t x * b t x) n w =
      scalarWalkProduct h a n w * scalarWalkProduct h b n w := by
  induction w generalizing n with
  | nil => simp [scalarWalkProduct]
  | cons t w ih => simp only [scalarWalkProduct, ih]; ring

lemma scalarWalkProduct_congr (h : ℕ) {a b : SignedStep → ℤ → ℝ}
    (hab : ∀ t x, a t x = b t x) (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h a n w = scalarWalkProduct h b n w := by
  have he : a = b := funext (fun t => funext (hab t))
  rw [he]

/-- Each visit contributes its denominator once at departure and once
at arrival; the only uncancelled factors lie at the two endpoints. -/
theorem scalarWalkProduct_normalize (h : ℕ) (a : SignedStep → ℤ → ℝ)
    (g : ℤ → ℝ) (hg : ∀ n, g n ≠ 0) (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h (fun t x => a t x / (g x * g (x + t.displacement h))) n w =
      scalarWalkProduct h (fun t x => a t x / (g x) ^ 2) n w *
        g n / g (n + wordDisplacement h w) := by
  induction w generalizing n with
  | nil => simp [scalarWalkProduct, hg]
  | cons t w ih =>
      rw [scalarWalkProduct, ih, scalarWalkProduct, wordDisplacement_cons]
      rw [← add_assoc]
      field_simp [hg n, hg (n + t.displacement h),
        hg (n + t.displacement h + wordDisplacement h w)]

/-- On a closed word, the exact original edge denominators become the
product of departure weights. Repeated sites remain repeated factors. -/
theorem scalarWalkProduct_closed_normalize (h : ℕ) (a : SignedStep → ℤ → ℝ)
    (g : ℤ → ℝ) (hg : ∀ n, g n ≠ 0) (n : ℤ) (w : List SignedStep)
    (hclosed : wordDisplacement h w = 0) :
    scalarWalkProduct h (fun t x => a t x / (g x * g (x + t.displacement h))) n w =
      scalarWalkProduct h (fun t x => a t x / (g x) ^ 2) n w := by
  rw [scalarWalkProduct_normalize h a g hg, hclosed, add_zero, mul_div_cancel_right₀ _ (hg n)]

/-- Keep every arithmetic, vertex, and orientation condition while moving
the exact matrix denominator to the departure site. -/
theorem signedIntegerWeight_closed_normalize (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (center : SignedStep → ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ) (n : ℤ) (w : List SignedStep)
    (hg : ∀ n, g n ≠ 0)
    (hperiod : ∀ t, ∀ q ∈ Q, ∀ z, center t (z + (h * q * t.tuple : ℕ)) = center t z)
    (hclosed : wordDisplacement h w = 0) :
    scalarWalkProduct h (fun t x =>
      signedIntegerWeight Q u (eligible t) g (center t) L K (extra t) h t x) n w =
      scalarWalkProduct h (fun t x =>
        if t.padding ∈ Q ∧ eligible t t.padding ∧ (t.padding : ℤ) ∣ x ∧
          integerEdgeKeep Q u (eligible t) g L K (extra t) x ∧
          integerEdgeKeep Q u (eligible t) g L K (extra t) (x + t.displacement h)
        then L * u t.padding * center t x / (g x) ^ 2 else 0) n w := by
  let a : SignedStep → ℤ → ℝ := fun t x =>
    if t.padding ∈ Q ∧ eligible t t.padding ∧ (t.padding : ℤ) ∣ x ∧
      integerEdgeKeep Q u (eligible t) g L K (extra t) x ∧
      integerEdgeKeep Q u (eligible t) g L K (extra t) (x + t.displacement h)
    then L * u t.padding * center t x else 0
  calc
    _ = scalarWalkProduct h (fun t x => a t x / (g x * g (x + t.displacement h))) n w := by
      apply scalarWalkProduct_congr
      intro t x
      rw [signedIntegerWeight_departure Q u (eligible t) g (center t) L K (extra t) h t x
        (hperiod t)]
      dsimp only [a]
      split_ifs <;> simp
    _ = scalarWalkProduct h (fun t x => a t x / (g x) ^ 2) n w :=
      scalarWalkProduct_closed_normalize h a g hg n w hclosed
    _ = _ := by
      apply scalarWalkProduct_congr
      intro t x
      dsimp only [a]
      split_ifs <;> simp

end TwoPointCorrelations

end OAI
