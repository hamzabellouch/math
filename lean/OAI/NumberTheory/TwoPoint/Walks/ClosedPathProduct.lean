import OAI.NumberTheory.TwoPoint.Walks.ClosedWalkNormalization

namespace OAI

/-! Join two paths with common endpoints into the literal closed signed word. -/

namespace TwoPointCorrelations

lemma scalarWalkProduct_append (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (n : ℤ) (u v : List SignedStep) :
    scalarWalkProduct h weight n (u ++ v) =
      scalarWalkProduct h weight n u *
        scalarWalkProduct h weight (n + wordDisplacement h u) v := by
  induction u generalizing n with
  | nil => simp [scalarWalkProduct]
  | cons t u ih =>
      simp only [List.cons_append, scalarWalkProduct, ih, wordDisplacement_cons]
      rw [← add_assoc]
      ring

lemma scalarWalkProduct_reverse (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (hflip : ∀ t n, weight t.flip (n + t.displacement h) = weight t n)
    (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h weight (n + wordDisplacement h w) (reverseWord w) =
      scalarWalkProduct h weight n w := by
  induction w generalizing n with
  | nil => simp [scalarWalkProduct]
  | cons t w ih =>
      rw [wordDisplacement_cons, reverseWord_cons, scalarWalkProduct_append]
      rw [show n + (t.displacement h + wordDisplacement h w) =
        (n + t.displacement h) + wordDisplacement h w by ring, ih]
      rw [wordDisplacement_reverseWord]
      have he : n + t.displacement h + wordDisplacement h w + -wordDisplacement h w =
          n + t.displacement h := by ring
      rw [he]
      simp only [scalarWalkProduct, hflip, mul_one]
      ring

theorem scalarWalkProduct_closed_pair (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (hflip : ∀ t n, weight t.flip (n + t.displacement h) = weight t n)
    (n : ℤ) (u v : List SignedStep)
    (hend : wordDisplacement h u = wordDisplacement h v) :
    scalarWalkProduct h weight n u * scalarWalkProduct h weight n v =
      scalarWalkProduct h weight n (u ++ reverseWord v) := by
  rw [scalarWalkProduct_append, hend, scalarWalkProduct_reverse h weight hflip]

theorem signedIntegerWeight_closed_pair (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ) (center : ℕ → ℤ → ℝ) (L K : ℝ)
    (extra : ℕ → ℤ → Prop) (h : ℕ) (n : ℤ) (v w : List SignedStep)
    (hend : wordDisplacement h v = wordDisplacement h w) :
    scalarWalkProduct h (fun t => signedIntegerWeight Q u (eligible t.tuple) g
        (center t.tuple) L K (extra t.tuple) h t) n v *
      scalarWalkProduct h (fun t => signedIntegerWeight Q u (eligible t.tuple) g
        (center t.tuple) L K (extra t.tuple) h t) n w =
      scalarWalkProduct h (fun t => signedIntegerWeight Q u (eligible t.tuple) g
        (center t.tuple) L K (extra t.tuple) h t)
        n (v ++ reverseWord w) :=
  scalarWalkProduct_closed_pair h _
    (fun t x => signedIntegerWeight_flip Q u (eligible t.tuple) g (center t.tuple)
      L K (extra t.tuple) h t x) n v w hend

end TwoPointCorrelations

end OAI
