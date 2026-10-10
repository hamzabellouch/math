import Mathlib
import OAI.Computability.MaxCut.Games.Basic

namespace OAI

noncomputable section

/-!
Finite threshold-overlap estimates used in the Dinur--Steurer argument.
These statements are numerical inequalities, not parallel-repetition premises.
The Boolean gate keeps the constraint predicate inside the overlap energy.
Weights need not be normalized: a finite auxiliary measure is permitted.
-/

namespace MaxCutGames.Repetition.Analytic

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def quadraticMass (w f g : ι → ℝ) : ℝ :=
  ∑ i, w i * ((f i) ^ 2 + (g i) ^ 2) / 2

def gatedCorrelation (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * f i * g i else 0

def gatedMinimum (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * min ((f i) ^ 2) ((g i) ^ 2) else 0

def gatedMaximum (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * max ((f i) ^ 2) ((g i) ^ 2) else 0

theorem quadraticMass_nonnegative (w f g : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ quadraticMass w f g := by
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (mul_nonneg (hw i) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (by norm_num)

theorem gatedCorrelation_nonnegative (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    0 ≤ gatedCorrelation w f g gate := by
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (mul_nonneg (hw i) (hf i)) (hg i)
  · exact le_rfl

theorem gatedCorrelation_le_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : gatedCorrelation w f g gate ≤ quadraticMass w f g := by
  apply Finset.sum_le_sum
  intro i _
  split
  · have hfg : f i * g i ≤ ((f i) ^ 2 + (g i) ^ 2) / 2 := by
      nlinarith [sq_nonneg (f i - g i)]
    simpa only [← mul_assoc, mul_div_assoc] using mul_le_mul_of_nonneg_left hfg (hw i)
  · exact div_nonneg (mul_nonneg (hw i) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (by norm_num)

theorem gatedMinimum_nonnegative (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ gatedMinimum w f g gate := by
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (hw i) (le_min (sq_nonneg _) (sq_nonneg _))
  · exact le_rfl

theorem gatedMinimum_le_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : gatedMinimum w f g gate ≤ quadraticMass w f g := by
  apply Finset.sum_le_sum
  intro i _
  split
  · have hmin : min ((f i) ^ 2) ((g i) ^ 2) ≤ ((f i) ^ 2 + (g i) ^ 2) / 2 := by
      have h₁ := min_le_left ((f i) ^ 2) ((g i) ^ 2)
      have h₂ := min_le_right ((f i) ^ 2) ((g i) ^ 2)
      linarith
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hmin (hw i)
  · exact div_nonneg (mul_nonneg (hw i) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (by norm_num)

theorem gatedMinimum_add_maximum_le (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedMinimum w f g gate + gatedMaximum w f g gate ≤ 2 * quadraticMass w f g := by
  unfold gatedMinimum gatedMaximum quadraticMass
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : gate i = true
  · simp only [hi, ↓reduceIte]
    have h := min_add_max ((f i) ^ 2) ((g i) ^ 2)
    rw [← mul_add, h]
    ring_nf ; exact le_rfl
  · simp only [hi, Bool.false_eq_true, ↓reduceIte, zero_add]
    have := hw i
    positivity

/-- A gated finite Cauchy--Schwarz estimate. This is the algebraic heart of
the threshold-rounding inequality, with no independence assumption. -/
theorem gatedCorrelation_sq_le_min_mul_max (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedCorrelation w f g gate ^ 2 ≤
      gatedMinimum w f g gate * gatedMaximum w f g gate := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _
    split
    · exact mul_nonneg (hw i) (le_min (sq_nonneg _) (sq_nonneg _))
    · exact le_rfl
  · intro i _
    split
    · exact mul_nonneg (hw i) ((sq_nonneg (f i)).trans (le_max_left _ _))
    · exact le_rfl
  · intro i _
    by_cases hi : gate i = true
    · simp only [hi, ↓reduceIte]
      rcases le_total ((f i) ^ 2) ((g i) ^ 2) with h | h
      · rw [min_eq_left h, max_eq_right h]
        ring_nf ; exact le_rfl
      · rw [min_eq_right h, max_eq_left h]
        ring_nf ; exact le_rfl
    · simp [hi]

theorem gatedCorrelation_sq_le_min_quadratic (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedCorrelation w f g gate ^ 2 ≤
      gatedMinimum w f g gate *
        (2 * quadraticMass w f g - gatedMinimum w f g gate) := by
  have hmax := gatedMinimum_add_maximum_le w f g gate hw
  have hmin := gatedMinimum_nonnegative w f g gate hw
  exact (gatedCorrelation_sq_le_min_mul_max w f g gate hw).trans
    (mul_le_mul_of_nonneg_left (by linarith) hmin)

/-- Sharp homogeneous Cheeger form. The expression under the square root
is nonnegative by the preceding proved inequality. -/
theorem gatedMinimum_cheeger (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    quadraticMass w f g -
        Real.sqrt (quadraticMass w f g ^ 2 - gatedCorrelation w f g gate ^ 2) ≤
      gatedMinimum w f g gate := by
  have h := gatedCorrelation_sq_le_min_quadratic w f g gate hw
  have hsq : (quadraticMass w f g - gatedMinimum w f g gate) ^ 2 ≤
      quadraticMass w f g ^ 2 - gatedCorrelation w f g gate ^ 2 := by
    nlinarith
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  linarith

/-- The near-perfect form suffices for alphabet-independent repetition.
The total squared mass may be at most one, rather than exactly one. -/
theorem gatedMinimum_near_one (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) {η : ℝ} (_hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hmass : quadraticMass w f g ≤ 1)
    (hcorrelation : 1 - η ≤ gatedCorrelation w f g gate) :
    1 - Real.sqrt (2 * η) ≤ gatedMinimum w f g gate := by
  have hmin := gatedMinimum_nonnegative w f g gate hw
  have h := gatedCorrelation_sq_le_min_quadratic w f g gate hw
  have hcorr : 0 ≤ gatedCorrelation w f g gate := by linarith
  have hsqcorr : (1 - η) ^ 2 ≤ gatedCorrelation w f g gate ^ 2 := by
    nlinarith
  have hupper : gatedMinimum w f g gate *
      (2 * quadraticMass w f g - gatedMinimum w f g gate) ≤
      gatedMinimum w f g gate * (2 - gatedMinimum w f g gate) := by
    apply mul_le_mul_of_nonneg_left _ hmin
    linarith
  have hsq : (1 - gatedMinimum w f g gate) ^ 2 ≤ 2 * η := by
    nlinarith [sq_nonneg η]
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  linarith

/-- Unit-mass form for the joint question-pair and auxiliary-coordinate law. -/
theorem gatedMinimum_unit_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hmass : quadraticMass w f g = 1) :
    1 - Real.sqrt (2 * (1 - gatedCorrelation w f g gate)) ≤
      gatedMinimum w f g gate := by
  have hc₀ := gatedCorrelation_nonnegative w f g gate hw hf hg
  have hc₁ := gatedCorrelation_le_mass w f g gate hw
  rw [hmass] at hc₁
  apply gatedMinimum_near_one w f g gate hw
  · linarith
  · linarith
  · exact hmass.le
  · linarith

end MaxCutGames.Repetition.Analytic

/-! Finite vertex-specific padding of nonnegative vectors to unit squared row
mass. The new coordinates can only increase any nonnegative relation energy. -/

namespace MaxCutGames.Repetition

section

open scoped BigOperators
open Foundations.Games

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

def rowSquareMass (f : V → Ω → ℝ) (v : V) : ℝ := ∑ ω, (f v ω) ^ 2

def paddedAmplitude [DecidableEq V] (f : V → Ω → ℝ) (v : V) : Ω ⊕ V → ℝ
  | Sum.inl ω => f v ω
  | Sum.inr w => if v = w then Real.sqrt (1 - rowSquareMass f v) else 0

def paddedLabel (a : V → Ω → A) (fallback : A) (v : V) : Ω ⊕ V → A
  | Sum.inl ω => a v ω
  | Sum.inr _ => fallback

omit [Fintype V] in
theorem paddedAmplitude_nonnegative [DecidableEq V] (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (v : V) (ω : Ω ⊕ V) :
    0 ≤ paddedAmplitude f v ω := by
  cases ω with
  | inl ω => exact hf v ω
  | inr w =>
      simp only [paddedAmplitude]
      split
      · exact Real.sqrt_nonneg _
      · exact le_rfl

theorem paddedAmplitude_row [DecidableEq V] (f : V → Ω → ℝ)
    (hrow : ∀ v, rowSquareMass f v ≤ 1) (v : V) :
    rowSquareMass (paddedAmplitude f) v = 1 := by
  have hs : Real.sqrt (1 - rowSquareMass f v) ^ 2 = 1 - rowSquareMass f v :=
    Real.sq_sqrt (sub_nonneg.mpr (hrow v))
  simp only [rowSquareMass] at hs
  simp only [rowSquareMass, Fintype.sum_sum_type, paddedAmplitude]
  simp only [ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ v), hs]
  ring

def pairEnergy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) : ℝ :=
  ν.expectation fun e => ∑ ω,
    if R e (a (left e) ω) (a (right e) ω)
      then f (left e) ω * f (right e) ω else 0

def pairOverlap (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) : ℝ :=
  ν.expectation fun e => ∑ ω,
    if R e (a (left e) ω) (a (right e) ω)
      then min ((f (left e) ω) ^ 2) ((f (right e) ω) ^ 2) else 0

omit [Fintype V] in
theorem pairEnergy_nonnegative (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) : 0 ≤ pairEnergy ν left right R a f := by
  apply Finset.sum_nonneg
  intro e _
  apply mul_nonneg (ν.nonnegative e)
  apply Finset.sum_nonneg
  intro ω _
  split
  · exact mul_nonneg (hf (left e) ω) (hf (right e) ω)
  · exact le_rfl

theorem pairEnergy_le_padded [DecidableEq V] (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (fallback : A) :
    pairEnergy ν left right R a f ≤
      pairEnergy ν left right R (paddedLabel a fallback) (paddedAmplitude f) := by
  unfold pairEnergy FiniteDistribution.expectation
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (ν.nonnegative e)
  dsimp only
  rw [Fintype.sum_sum_type]
  simp only [paddedLabel, paddedAmplitude]
  have hnonneg : 0 ≤ ∑ w : V,
      if R e fallback fallback then
        (if left e = w then Real.sqrt (1 - rowSquareMass f (left e)) else 0) *
          (if right e = w then Real.sqrt (1 - rowSquareMass f (right e)) else 0)
      else 0 := by
    apply Finset.sum_nonneg
    intro w _
    split
    · exact mul_nonneg (paddedAmplitude_nonnegative f hf (left e) (Sum.inr w))
        (paddedAmplitude_nonnegative f hf (right e) (Sum.inr w))
    · exact le_rfl
  exact le_add_of_nonneg_right hnonneg

end

/-! Flatten the genuine finite occurrence law together with the auxiliary
coordinate into the Cheeger inequality. The occurrence may retain hidden
information; both endpoint label tables still depend only on their vertex. -/

open scoped BigOperators
open Foundations.Games

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

omit [Fintype V] in
theorem pairQuadraticMass_eq_one (ν : FiniteDistribution E) (left right : E → V)
    (f : V → Ω → ℝ) (hrow : ∀ v, rowSquareMass f v = 1) :
    Analytic.quadraticMass (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2) = 1 := by
  unfold Analytic.quadraticMass
  rw [Fintype.sum_prod_type]
  have he (e : E) :
      (∑ ω, ν.weight e * ((f (left e) ω) ^ 2 + (f (right e) ω) ^ 2) / 2) =
        ν.weight e := by
    calc
      _ = ν.weight e *
          ((∑ ω, (f (left e) ω) ^ 2) + (∑ ω, (f (right e) ω) ^ 2)) / 2 := by
        simp only [div_eq_mul_inv, mul_add, add_mul, Finset.sum_add_distrib,
          Finset.mul_sum, Finset.sum_mul]
      _ = ν.weight e := by
        change ν.weight e * (rowSquareMass f (left e) + rowSquareMass f (right e)) / 2 = _
        rw [hrow, hrow]
        ring
  simp_rw [he]
  exact ν.normalized

omit [Fintype V] in
theorem pairGatedCorrelation_eq_energy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) :
    Analytic.gatedCorrelation (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
      (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2)) =
      pairEnergy ν left right R a f := by
  simp only [Analytic.gatedCorrelation, pairEnergy, FiniteDistribution.expectation,
    Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

omit [Fintype V] in
theorem pairGatedMinimum_eq_overlap (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) :
    Analytic.gatedMinimum (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
      (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2)) =
      pairOverlap ν left right R a f := by
  simp only [Analytic.gatedMinimum, pairOverlap, FiniteDistribution.expectation,
    Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

omit [Fintype V] in
theorem pairEnergy_le_one_of_unit_rows (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hrow : ∀ v, rowSquareMass f v = 1) : pairEnergy ν left right R a f ≤ 1 := by
  have h := Analytic.gatedCorrelation_le_mass (fun p : E × Ω => ν.weight p.1)
    (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
    (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2))
    (fun p => ν.nonnegative p.1)
  rw [pairGatedCorrelation_eq_energy, pairQuadraticMass_eq_one ν left right f hrow] at h
  exact h

omit [Fintype V] in
/-- The overlap used by finite threshold sampling is large whenever the
actual weighted occurrence energy is large. -/
theorem pairOverlap_ge_energy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v = 1) :
    1 - Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
      pairOverlap ν left right R a f := by
  have h := Analytic.gatedMinimum_unit_mass (fun p : E × Ω => ν.weight p.1)
    (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
    (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2))
    (fun p => ν.nonnegative p.1) (fun p => hf (left p.1) p.2)
    (fun p => hf (right p.1) p.2) (pairQuadraticMass_eq_one ν left right f hrow)
  rw [pairGatedCorrelation_eq_energy, pairGatedMinimum_eq_overlap] at h
  exact h

end MaxCutGames.Repetition

end

end OAI
