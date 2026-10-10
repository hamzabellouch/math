import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingProduct

namespace OAI

/-! Separate the actual closed matrix word into centered factors and its retained padding weight. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def retainedEdgeDeparture (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ) (t : SignedStep) (n : ℤ) : ℝ :=
  if t.padding ∈ Q ∧ eligible t t.padding ∧ (t.padding : ℤ) ∣ n ∧
      integerEdgeKeep Q u (eligible t) g L K (extra t) n ∧
      integerEdgeKeep Q u (eligible t) g L K (extra t) (n + t.displacement h)
  then L * u t.padding / (g n) ^ 2 else 0

lemma retainedEdgeDeparture_nonneg (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ) (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (t : SignedStep) (n : ℤ) :
    0 ≤ retainedEdgeDeparture Q u eligible g L K extra h t n := by
  unfold retainedEdgeDeparture
  split_ifs
  · exact div_nonneg (mul_nonneg hL (hu _)) (sq_nonneg _)
  · exact le_rfl

lemma retainedEdgeDeparture_le_atom (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ) (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (t : SignedStep) (n : ℤ) :
    retainedEdgeDeparture Q u eligible g L K extra h t n ≤
      retainedPaddingAtom Q u (eligible t) g L K (extra t) n t.padding := by
  unfold retainedEdgeDeparture
  split_ifs with ht
  · have hs : eligible t t.padding ∧ (t.padding : ℤ) ∣ n ∧
        integerEdgeKeep Q u (eligible t) g L K (extra t) n :=
      ⟨ht.2.1, ht.2.2.1, ht.2.2.2.1⟩
    simp only [retainedPaddingAtom, ite_eq_left hs, le_refl]
  · exact retainedPaddingAtom_nonneg Q u (eligible t) g L K (extra t) n t.padding hL (hu _)

theorem closed_signed_word_factorization (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (center : SignedStep → ℤ → ℝ)
    (L K : ℝ) (extra : SignedStep → ℤ → Prop) (h : ℕ) (n : ℤ) (word : List SignedStep)
    (hg : ∀ n, g n ≠ 0)
    (hperiod : ∀ t, ∀ q ∈ Q, ∀ z, center t (z + (h * q * t.tuple : ℕ)) = center t z)
    (hclosed : wordDisplacement h word = 0) :
    scalarWalkProduct h (fun t x =>
      signedIntegerWeight Q u (eligible t) g (center t) L K (extra t) h t x) n word =
      scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h) n word *
        scalarWalkProduct h center n word := by
  rw [signedIntegerWeight_closed_normalize Q u eligible g center L K extra h n word
    hg hperiod hclosed]
  rw [← scalarWalkProduct_mul]
  apply scalarWalkProduct_congr
  intro t x
  unfold retainedEdgeDeparture
  split_ifs <;> ring

lemma scalarWalkProduct_nonneg (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (hw : ∀ t n, 0 ≤ weight t n) (n : ℤ) (word : List SignedStep) :
    0 ≤ scalarWalkProduct h weight n word := by
  induction word generalizing n with
  | nil => exact zero_le_one
  | cons t word ih => exact mul_nonneg (hw t n) (ih _)

lemma scalarWalkProduct_mono (h : ℕ) (a b : SignedStep → ℤ → ℝ)
    (ha : ∀ t n, 0 ≤ a t n) (hab : ∀ t n, a t n ≤ b t n)
    (n : ℤ) (word : List SignedStep) :
    scalarWalkProduct h a n word ≤ scalarWalkProduct h b n word := by
  induction word generalizing n with
  | nil => exact le_rfl
  | cons t word ih =>
      exact mul_le_mul (hab t n) (ih _) (scalarWalkProduct_nonneg h a ha _ _)
        ((ha t n).trans (hab t n))

theorem closed_word_padding_majorant (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ) (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (n : ℤ) (word : List SignedStep) :
    scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h) n word ≤
      scalarWalkProduct h
        (fun t x => retainedPaddingAtom Q u (eligible t) g L K (extra t) x t.padding) n word :=
  scalarWalkProduct_mono h _ _ (retainedEdgeDeparture_nonneg Q u eligible g L K extra h hL hu)
    (retainedEdgeDeparture_le_atom Q u eligible g L K extra h hL hu) n word

theorem scalarWalkProduct_ofFn {m : ℕ} (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (step : Fin m → SignedStep) (n : ℤ) :
    scalarWalkProduct h weight n (List.ofFn step) =
      ∏ i : Fin m, weight (step i) (n + wordDisplacement h ((List.ofFn step).take i.val)) := by
  induction m generalizing n with
  | zero => simp [scalarWalkProduct]
  | succ m ih =>
      rw [List.ofFn_succ, scalarWalkProduct, ih, Fin.prod_univ_succ]
      simp only [Fin.val_zero, List.take_zero, wordDisplacement_nil, add_zero]
      congr 1
      apply prod_congr rfl
      intro i _
      simp only [Fin.val_succ, List.take_succ_cons, wordDisplacement_cons,
        add_assoc]

end TwoPointCorrelations

end OAI
