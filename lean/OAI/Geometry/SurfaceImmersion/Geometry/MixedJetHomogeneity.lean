import OAI.Geometry.SurfaceImmersion.Geometry.MixedJetCalculus

namespace OAI

/-! Homogeneity in each variation slot, including the zero polynomial. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

inductive DegreeIn (j : Fin 3) : MixedExpression → ℕ → Prop
  | coeff (c) : DegreeIn j (.coeff c) 0
  | zero (n) : DegreeIn j (.coeff (fun _ => 0)) n
  | other {e n} (i w a) (hi : i ≠ j.succ) (h : DegreeIn j e n) :
      DegreeIn j (.atom i w a e) n
  | same {e n} (w a) (h : DegreeIn j e n) : DegreeIn j (.atom j.succ w a e) (n + 1)
  | add {e f n} (he : DegreeIn j e n) (hf : DegreeIn j f n) : DegreeIn j (.add e f) n

lemma degree_sumList {ι : Type*} (j : Fin 3) (n : ℕ) (l : List ι) (f : ι → MixedExpression)
    (h : ∀ i ∈ l, DegreeIn j (f i) n) : DegreeIn j (sumList l f) n := by
  induction l with
  | nil => exact DegreeIn.zero n
  | cons i l ih =>
    exact DegreeIn.add (h i (List.mem_cons_self ..))
      (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)))

lemma degree_ofExpression (j : Fin 3) (e : Expression) : DegreeIn j (ofExpression e) 0 := by
  induction e with
  | coeff c => exact DegreeIn.coeff c
  | atom w a e ih => exact DegreeIn.other 0 w a (Ne.symm (Fin.succ_ne_zero j)) ih
  | add e f ihe ihf => exact DegreeIn.add ihe ihf

lemma coefficientDerivative_zero (i : Fin 7 × Fin 4) :
    coefficientDerivative (fun _ => 0) i = fun _ => 0 := by
  funext z
  simp [coefficientDerivative]

/-- Differentiating the base map adds exactly one occurrence of the chosen
variation slot to each monomial. -/
theorem DegreeIn.differentiate {j : Fin 3} {e : MixedExpression} {n : ℕ}
    (h : DegreeIn j e n) (k : Fin 3) :
    DegreeIn j (e.differentiate k) (n + if k = j then 1 else 0) := by
  induction h with
  | coeff c =>
    apply degree_sumList
    intro i _
    by_cases hk : k = j
    · subst k
      simpa only [↓reduceIte, Nat.zero_add] using
        DegreeIn.same (j := j) (lowWord i.1) i.2 (DegreeIn.coeff (coefficientDerivative c i))
    · simpa only [hk, ↓reduceIte, Nat.zero_add] using
        DegreeIn.other k.succ (lowWord i.1) i.2 (by simpa using hk)
          (DegreeIn.coeff (coefficientDerivative c i))
  | zero n =>
    apply degree_sumList
    intro i _
    rw [coefficientDerivative_zero]
    by_cases hk : k = j
    · subst k
      simpa only [↓reduceIte] using
        DegreeIn.same (j := j) (lowWord i.1) i.2 (DegreeIn.zero n)
    · simpa only [hk, ↓reduceIte, Nat.add_zero] using
        DegreeIn.other k.succ (lowWord i.1) i.2 (by simpa using hk) (DegreeIn.zero n)
  | @other e n i w a hi h ih =>
    by_cases hi0 : i = 0
    · subst i
      simp only [MixedExpression.differentiate, ↓reduceIte]
      apply DegreeIn.add
      · by_cases hk : k = j
        · subst k
          simpa only [↓reduceIte] using DegreeIn.same w a h
        · simpa only [hk, ↓reduceIte, Nat.add_zero] using
            DegreeIn.other k.succ w a (by simpa using hk) h
      · exact DegreeIn.other 0 w a hi ih
    · simpa only [MixedExpression.differentiate, hi0, ↓reduceIte] using DegreeIn.other i w a hi ih
  | @same e n w a h ih =>
    simpa only [MixedExpression.differentiate, Fin.succ_ne_zero, ↓reduceIte, Nat.add_right_comm n 1]
      using DegreeIn.same w a ih
  | add he hf ihe ihf => exact DegreeIn.add ihe ihf

def scaleSlot (G : Fin 4 → Base → Space) (j : Fin 3) (c : ℝ) : Fin 4 → Base → Space :=
  fun i p => if i = j.succ then c • G i p else G i p

lemma scaleSlot_base (G : Fin 4 → Base → Space) (j : Fin 3) (c : ℝ) :
    scaleSlot G j c 0 = G 0 := by
  funext p
  simp only [scaleSlot, Ne.symm (Fin.succ_ne_zero j), ↓reduceIte]

lemma scaleSlot_smooth {G : Fin 4 → Base → Space} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (j : Fin 3) (c : ℝ) : ∀ i, ContDiff ℝ ∞ (scaleSlot G j c i) := by
  intro i
  change ContDiff ℝ ∞ (fun p => if i = j.succ then c • G i p else G i p)
  by_cases hi : i = j.succ
  · simpa only [scaleSlot, hi, ↓reduceIte] using ContDiff.const_smul c (hG j.succ)
  · simpa only [scaleSlot, hi, ↓reduceIte] using hG i

theorem DegreeIn.eval_scaleSlot {j : Fin 3} {e : MixedExpression} {n : ℕ}
    (h : DegreeIn j e n) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (c : ℝ) (z : Base × ℝ) :
    e.eval (scaleSlot G j c) z = c ^ n * e.eval G z := by
  induction h with
  | coeff d => simp only [eval, scaleSlot_base, pow_zero, one_mul]
  | zero n => simp only [eval, mul_zero]
  | other i w a hi h ih =>
    have he : scaleSlot G j c i = G i := by
      funext p
      simp only [scaleSlot, hi, ↓reduceIte]
    simp only [eval, he, ih]
    ring
  | same w a h ih =>
    have he : scaleSlot G j c j.succ = fun p => c • G j.succ p := by
      funext p
      simp only [scaleSlot, ↓reduceIte]
    simp only [eval, he, jet_smul (hG j.succ), ih, pow_succ]
    ring
  | add he hf ihe ihf => simp only [eval, ihe, ihf, mul_add]

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
