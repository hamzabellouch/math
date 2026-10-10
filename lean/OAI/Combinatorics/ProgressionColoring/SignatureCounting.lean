import OAI.Combinatorics.ProgressionColoring.Arrangement
import OAI.Combinatorics.ProgressionColoring.ComparisonOutputs
import OAI.Combinatorics.ProgressionColoring.LabelCounts
import OAI.Combinatorics.ProgressionColoring.NormBands
import OAI.Combinatorics.ProgressionColoring.CyclicModel
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Counting literal signatures on affine progressions

Only coefficient triples whose evaluations lie in the specified bounded
interval are counted. Integer threshold comparisons, including equality,
determine their floor words. The proved arrangement estimate in dimension
three gives `25 * (k * (B + 1) + 1)^8`; no cubic arrangement bound is asserted.

The full label word and the floor word determine each original color and
literal `(box, integer band)` key. The product count never renames keys.
-/

noncomputable section

universe uLabel uBox uIndex uU uV uK uL

namespace QuantitativeVanDerWaerden

open scoped BigOperators

/-- Evaluation of the three actual quadratic coefficients. -/
def quadraticValue (θ : Fin 3 → ℝ) (j : ℕ) : ℝ :=
  θ 0 + θ 1 * (j : ℝ) + θ 2 * (j : ℝ) ^ 2

def quadraticFloorWord (k : ℕ) (θ : Fin 3 → ℝ) : Fin k → ℤ :=
  fun j => ⌊quadraticValue θ j.val⌋

/-- The evaluation restriction is essential: unrestricted coefficient triples
have infinitely many literal integer floor words. -/
def boundedQuadraticDomain (k B : ℕ) : Set (Fin 3 → ℝ) :=
  {θ | ∀ j : Fin k, 0 ≤ quadraticValue θ j.val ∧ quadraticValue θ j.val ≤ (B : ℝ)}

def quadraticComparisonForm (j b : ℕ) : AffineForm 3 where
  linear := ![1, (j : ℝ), (j : ℝ) ^ 2]
  constant := -(b : ℝ)

theorem quadraticComparisonForm_eval (j b : ℕ) (θ : Fin 3 → ℝ) :
    (quadraticComparisonForm j b).eval θ = quadraticValue θ j - b := by
  simp [quadraticComparisonForm, AffineForm.eval, quadraticValue, Fin.sum_univ_succ]
  ring

/-- One form for every position and every threshold `0,...,B`. -/
def quadraticComparisonForms (k B : ℕ) : Fin (k * (B + 1)) → AffineForm 3 :=
  fun i =>
    let p : Fin k × Fin (B + 1) := finProdFinEquiv.symm i
    quadraticComparisonForm p.1.val p.2.val

@[simp] theorem quadraticComparisonForms_eval (k B : ℕ)
    (j : Fin k) (b : Fin (B + 1)) (θ : Fin 3 → ℝ) :
    (quadraticComparisonForms k B (finProdFinEquiv (j, b))).eval θ =
      quadraticValue θ j.val - b.val := by
  simp only [quadraticComparisonForms, Equiv.symm_apply_apply,
    quadraticComparisonForm_eval]

/-- Testing the threshold equal to the first floor forces the corresponding
lower bound for the second floor. The threshold is an original integer. -/
private theorem floor_le_of_comparisons {B : ℕ} {x y : ℝ}
    (hx0 : 0 ≤ x) (hxB : x ≤ (B : ℝ))
    (h : ∀ b : Fin (B + 1), ternarySign (x - b.val) = ternarySign (y - b.val)) :
    ⌊x⌋ ≤ ⌊y⌋ := by
  have hxI : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx0
  have hxIB : ⌊x⌋ ≤ (B : ℤ) := by
    exact_mod_cast (Int.floor_le x).trans hxB
  let b : Fin (B + 1) := ⟨⌊x⌋.toNat, by omega⟩
  have hbI : (b.val : ℤ) = ⌊x⌋ := by dsimp [b]; omega
  have hbR : (b.val : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast hbI
  have hy : (b.val : ℝ) ≤ y := by
    by_contra hy
    have hneg : ternarySign (y - b.val) = 0 :=
      (ternarySign_eq_zero _).mpr (sub_neg.mpr (lt_of_not_ge hy))
    have hxneg := (ternarySign_eq_zero _).mp ((h b).trans hneg)
    rw [hbR] at hxneg
    exact (not_lt_of_ge (sub_nonneg.mpr (Int.floor_le x))) hxneg
  apply Int.le_floor.mpr
  simpa only [hbR] using hy

theorem floor_eq_of_comparisons {B : ℕ} {x y : ℝ}
    (hx : 0 ≤ x ∧ x ≤ (B : ℝ)) (hy : 0 ≤ y ∧ y ≤ (B : ℝ))
    (h : ∀ b : Fin (B + 1), ternarySign (x - b.val) = ternarySign (y - b.val)) :
    ⌊x⌋ = ⌊y⌋ :=
  le_antisymm (floor_le_of_comparisons hx.1 hx.2 h)
    (floor_le_of_comparisons hy.1 hy.2 (fun b => (h b).symm))

/-- Sign equality determines the entire floor word, with both zero and upper
boundary evaluations allowed. -/
theorem quadraticFloorWord_eq_of_signVector_eq (k B : ℕ)
    {θ η : Fin 3 → ℝ} (hθ : θ ∈ boundedQuadraticDomain k B)
    (hη : η ∈ boundedQuadraticDomain k B)
    (h : signVector (quadraticComparisonForms k B) θ =
      signVector (quadraticComparisonForms k B) η) :
    quadraticFloorWord k θ = quadraticFloorWord k η := by
  funext j
  apply floor_eq_of_comparisons (hθ j) (hη j)
  intro b
  have hb := congrFun h (finProdFinEquiv (j, b))
  simpa only [signVector, quadraticComparisonForms_eval] using hb

/-- The genuine coefficients of the squared norm on an affine line. -/
def normSqCoefficients {D : ℕ} (A B : Vec D) : Fin 3 → ℝ :=
  ![normSq A, 2 * (∑ i, A i * B i), normSq B]

theorem quadraticValue_normSqCoefficients {D : ℕ} (A B : Vec D) (j : ℕ) :
    quadraticValue (normSqCoefficients A B) j =
      normSq (fun i => A i + (j : ℝ) * B i) := by
  rw [normSq_affine]
  simp [quadraticValue, normSqCoefficients]
  ring

/-- Coarse natural bound used in the counting estimate. Centered coordinate
bounds imply this for the actual `q`-scaled representative. -/
theorem normSq_scaled_le {D : ℕ} (q : ℕ) (x : Vec D)
    (hx : ∀ i, -(1 / 2 : ℝ) ≤ x i ∧ x i < 1 / 2) :
    normSq (fun i => (q : ℝ) * x i) ≤ ((D * q ^ 2 : ℕ) : ℝ) := by
  have hterm (i : Fin D) : ((q : ℝ) * x i) ^ 2 ≤ (q : ℝ) ^ 2 := by
    have hs : (x i) ^ 2 ≤ 1 := by
      have hp : 0 ≤ (x i + 1 / 2) * (1 / 2 - x i) :=
        mul_nonneg (by linarith [(hx i).1]) (by linarith [(hx i).2])
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (q : ℝ))]
  calc
    normSq (fun i => (q : ℝ) * x i) ≤ ∑ _i : Fin D, (q : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = ((D * q ^ 2 : ℕ) : ℝ) := by simp

theorem normSq_scaled_yRep_bounds (q D dilation : ℕ) (n : CyclicGroup q D) :
    0 ≤ normSq (fun i => (q : ℝ) * yRep q D dilation n i) ∧
      normSq (fun i => (q : ℝ) * yRep q D dilation n i) ≤ ((D * q ^ 2 : ℕ) : ℝ) :=
  ⟨normSq_nonneg _, normSq_scaled_le q _ (fun i => yRep_mem q D dilation n i)⟩

/-- The exact finite image of bounded quadratic floor words. In particular,
the family also covers triples not arising from squared norms. -/
theorem finite_quadraticFloorWords (k B : ℕ) :
    ∃ W : Finset (Fin k → ℤ),
      (∀ w, w ∈ W ↔ ∃ θ ∈ boundedQuadraticDomain k B, quadraticFloorWord k θ = w) ∧
      W.card ≤ 25 * (k * (B + 1) + 1) ^ 8 := by
  obtain ⟨W, hW, hcard⟩ := finite_outputs_of_comparisons
    (quadraticComparisonForms k B) (boundedQuadraticDomain k B) (quadraticFloorWord k)
    (fun _ hθ _ hη h => quadraticFloorWord_eq_of_signVector_eq k B hθ hη h)
  exact ⟨W, hW, hcard⟩

/-- The color and box are fixed functions of the full label, while the band
is the literal integer value. No signature-dependent coding is used. -/
def literalSignature {Label : Type uLabel} {Box : Type uBox} {k : ℕ}
    (color : Label → Bool) (boxOf : Label → Box)
    (labels : Fin k → Label) (bands : Fin k → ℤ) : Fin k → Bool × (Box × ℤ) :=
  fun j => (color (labels j), (boxOf (labels j), bands j))

/-- Finite-image factorization: one full label word and one band word suffice.
The ambient label and box types need not be finite. -/
theorem card_literalSignatures_le_mul {ι : Type uIndex} {Label : Type uLabel} {Box : Type uBox} {k : ℕ}
    [DecidableEq Label] [DecidableEq Box]
    (P : Finset ι) (labels : ι → Fin k → Label) (bands : ι → Fin k → ℤ)
    (color : Label → Bool) (boxOf : Label → Box) (W : Finset (Fin k → ℤ))
    (hW : ∀ p ∈ P, bands p ∈ W) :
    (P.image (fun p => literalSignature color boxOf (labels p) (bands p))).card ≤
      (P.image labels).card * W.card := by
  classical
  let decode : ((Fin k → Label) × (Fin k → ℤ)) → (Fin k → Bool × (Box × ℤ)) :=
    fun x => literalSignature color boxOf x.1 x.2
  have hsub : P.image (fun p => literalSignature color boxOf (labels p) (bands p)) ⊆
      ((P.image labels).product W).image decode := by
    intro σ hσ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hσ
    exact Finset.mem_image.mpr ⟨(labels p, bands p),
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, hW p hp⟩, rfl⟩
  calc
    _ ≤ (((P.image labels).product W).image decode).card := Finset.card_le_card hsub
    _ ≤ ((P.image labels).product W).card := Finset.card_image_le
    _ = (P.image labels).card * W.card := Finset.card_product _ _

theorem card_quadraticSignatures_le {ι : Type uIndex} {Label : Type uLabel} {Box : Type uBox} {k B : ℕ}
    [DecidableEq Label] [DecidableEq Box]
    (P : Finset ι) (labels : ι → Fin k → Label) (θ : ι → Fin 3 → ℝ)
    (color : Label → Bool) (boxOf : Label → Box)
    (hθ : ∀ p ∈ P, θ p ∈ boundedQuadraticDomain k B) :
    (P.image (fun p => literalSignature color boxOf (labels p)
      (quadraticFloorWord k (θ p)))).card ≤
      (P.image labels).card * (25 * (k * (B + 1) + 1) ^ 8) := by
  obtain ⟨W, hW, hcard⟩ := finite_quadraticFloorWords k B
  exact (card_literalSignatures_le_mul P labels (fun p => quadraticFloorWord k (θ p))
    color boxOf W (fun p hp => (hW _).mpr ⟨θ p, hθ p hp, rfl⟩)).trans
    (Nat.mul_le_mul_left _ hcard)

/-- Actual affine squared-norm words have the preceding coefficient witnesses.
Affinity and the evaluation bound are stated for the finite family being counted. -/
theorem card_affineNormSignatures_le {ι : Type uIndex} {Label : Type uLabel} {Box : Type uBox} {k D B : ℕ}
    [DecidableEq Label] [DecidableEq Box]
    (P : Finset ι) (labels : ι → Fin k → Label) (point : ι → Fin k → Vec D)
    (color : Label → Bool) (boxOf : Label → Box)
    (haff : ∀ p ∈ P, ∃ A C : Vec D,
      ∀ j : Fin k, point p j = fun i => A i + (j.val : ℝ) * C i)
    (hbound : ∀ p ∈ P, ∀ j, normSq (point p j) ≤ (B : ℝ)) :
    (P.image (fun p => literalSignature color boxOf (labels p)
      (fun j => ⌊normSq (point p j)⌋))).card ≤
      (P.image labels).card * (25 * (k * (B + 1) + 1) ^ 8) := by
  obtain ⟨W, hW, hcard⟩ := finite_quadraticFloorWords k B
  have hmem (p : ι) (hp : p ∈ P) : (fun j => ⌊normSq (point p j)⌋) ∈ W := by
    obtain ⟨A, C, hAC⟩ := haff p hp
    apply (hW _).mpr
    refine ⟨normSqCoefficients A C, ?_, ?_⟩
    · intro j
      rw [quadraticValue_normSqCoefficients, ← hAC j]
      exact ⟨normSq_nonneg _, hbound p hp j⟩
    · funext j
      change ⌊quadraticValue (normSqCoefficients A C) j.val⌋ = _
      rw [quadraticValue_normSqCoefficients, ← hAC j]
  exact (card_literalSignatures_le_mul P labels (fun p j => ⌊normSq (point p j)⌋)
    color boxOf W hmem).trans (Nat.mul_le_mul_left _ hcard)

/-- The concrete centered cyclic representative supplies its own bounded
evaluation domain. The coarse natural threshold is exactly `D*q^2`. -/
theorem card_affine_yRep_signatures_le {ι : Type uIndex} {Label : Type uLabel} {Box : Type uBox} {k q D dilation : ℕ}
    [DecidableEq Label] [DecidableEq Box]
    (P : Finset ι) (labels : ι → Fin k → Label)
    (n : ι → Fin k → CyclicGroup q D) (color : Label → Bool) (boxOf : Label → Box)
    (haff : ∀ p ∈ P, ∃ A C : Vec D, ∀ j : Fin k,
      (fun i => (q : ℝ) * yRep q D dilation (n p j) i) =
        fun i => A i + (j.val : ℝ) * C i) :
    (P.image (fun p => literalSignature color boxOf (labels p)
      (fun j => ⌊normSq (fun i => (q : ℝ) * yRep q D dilation (n p j) i)⌋))).card ≤
      (P.image labels).card * (25 * (k * (D * q ^ 2 + 1) + 1) ^ 8) := by
  apply card_affineNormSignatures_le P labels
    (fun p j i => (q : ℝ) * yRep q D dilation (n p j) i) color boxOf haff
  intro p _ j
  exact (normSq_scaled_yRep_bounds q D dilation (n p j)).2

/-- With full labels the original second-system box is precisely the second
projection, an entire vector of literal interval identities. -/
theorem card_affine_yRep_fullLabel_signatures_le {ι : Type uIndex} {U : Type uU} {V : Type uV} {k q D dilation : ℕ}
    [DecidableEq U] [DecidableEq V]
    (P : Finset ι) (labels : ι → Fin k → FullLabel D U V)
    (n : ι → Fin k → CyclicGroup q D) (color : FullLabel D U V → Bool)
    (haff : ∀ p ∈ P, ∃ A C : Vec D, ∀ j : Fin k,
      (fun i => (q : ℝ) * yRep q D dilation (n p j) i) =
        fun i => A i + (j.val : ℝ) * C i) :
    (P.image (fun p => literalSignature color Prod.snd (labels p)
      (fun j => ⌊normSq (fun i => (q : ℝ) * yRep q D dilation (n p j) i)⌋))).card ≤
      (P.image labels).card * (25 * (k * (D * q ^ 2 + 1) + 1) ^ 8) :=
  card_affine_yRep_signatures_le P labels n color Prod.snd haff

/-- In the finite-key application this map is the subtype's injective
inclusion into the ambient literal box/band pairs. -/
def signatureKeyMap {K : Type uK} {L : Type uL} {k : ℕ} (f : K → L)
    (σ : Fin k → Bool × K) : Fin k → Bool × L :=
  fun j => ((σ j).1, f (σ j).2)

theorem signatureKeyMap_injective {K : Type uK} {L : Type uL} {k : ℕ} {f : K → L}
    (hf : Function.Injective f) : Function.Injective (@signatureKeyMap K L k f) := by
  intro σ τ h
  funext j
  have hj := congrFun h j
  exact Prod.ext (congrArg (fun z : Bool × L => z.1) hj)
    (hf (congrArg (fun z : Bool × L => z.2) hj))

theorem card_signatureKeyMap_image {K : Type uK} {L : Type uL} {k : ℕ}
    [DecidableEq L] (f : K → L) (hf : Function.Injective f)
    (S : Finset (Fin k → Bool × K)) :
    (S.image (signatureKeyMap f)).card = S.card :=
  Finset.card_image_of_injective _ (signatureKeyMap_injective hf)

end QuantitativeVanDerWaerden

end

end OAI
