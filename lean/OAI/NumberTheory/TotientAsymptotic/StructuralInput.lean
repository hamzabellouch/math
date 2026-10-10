import OAI.NumberTheory.TotientAsymptotic.Renewal

namespace OAI

/-!
Minimal structural inputs from Ford, *The distribution of totients*,
arXiv:1104.3264v2 (14 July 2013), Theorems 10 and 16.

The exceptional sets count values with **some** failing preimage, as in the
convention preceding Theorem 10, p. 5.  Consequently every preimage of a value
outside the exceptional set satisfies the property.  Ford's coordinates in
(4.2), p. 17, are clamped double logarithms.  Theorem 16, (6.1)--(6.2), p. 29,
also supplies the terminal lower bound that allows removing this clamp.

The band center below is Ford's B*rho^i*(1-i/m), not the phase-dependent
`bandScale` in Basic.lean.  Passing between these two centers is an additional
analytic step, governed by the manuscript's equation alpha-comparison.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- Prime factors with multiplicity, largest first, padded by 1. -/
def fordPrime (n i : ℕ) : ℕ := (n.primeFactorsList.reverse[i]?).getD 1

def primeDoubleLog (n i : ℕ) : ℝ := Real.log (Real.log (fordPrime n i : ℝ))

def fordPrimeCoordinate (n i : ℕ) : ℝ := max 0 (primeDoubleLog n i)

def fordBandScale (x : ℝ) (i : ℕ) : ℝ :=
  B x * rho^i * (1 - (i : ℝ) / m x)

def fordBandCondition (x η : ℝ) (i n : ℕ) : Prop :=
  |fordPrimeCoordinate n i / fordBandScale x i - 1| ≤ η

/-- Theorem 10 is used only on positive coordinates, where the indicated
prime exists and its raw and clamped double logarithms agree.  Missing or
nonpositive coordinates are handled separately by Theorem 16. -/
def fordPositiveBandCondition (x η : ℝ) (i n : ℕ) : Prop :=
  0 < fordPrimeCoordinate n i → fordBandCondition x η i n

def preimageExceptionValues (x : ℝ) (Q : ℕ → Prop) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 ⌊x⌋₊).filter
    (fun v => ∃ n : ℕ, 0 < n ∧ n.totient = v ∧ ¬ Q n)

def preimageExceptionCount (x : ℝ) (Q : ℕ → Prop) : ℝ :=
  (preimageExceptionValues x Q).card

/-- Ford Theorem 10(a),(b), restricted to positive coordinates, the indices
and the errors needed here.  This does not assign a value to the raw
double logarithm of a missing prime.  The endpoint i=m is omitted because
the application uses i≤m-P<m. -/
def FordTheorem10Input : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i < m x → ∀ η : ℝ, 0 < η → η ≤ 1/8 →
      (η ≤ (i : ℝ) / (3*m x) →
        preimageExceptionCount x (fordPositiveBandCondition x η i) ≤
          C * V x * ((i : ℝ)/(η*m x)) *
            Real.exp (-η^2 * m x * (m x-i : ℕ) / (4*i))) ∧
      ((i : ℝ) / (3*m x) ≤ η →
        preimageExceptionCount x (fordPositiveBandCondition x η i) ≤
          C * V x * Real.exp (-η*m x/13))

def fordSimplexCoordinate (x : ℝ) (n i : ℕ) : ℝ :=
  if i = 0 then B x else fordPrimeCoordinate n i

def rawSimplexCoordinate (x : ℝ) (n i : ℕ) : ℝ :=
  if i = 0 then B x else primeDoubleLog n i

/-- The needed consequence of membership in Ford's S_L(xi).  It retains
the last adjacent inequality with coefficient 1 and coordinate ordering. -/
def fordSimplexCondition (x : ℝ) (Ψ n : ℕ) : Prop :=
  let J := m x-Ψ
  2 < fordPrimeCoordinate n J ∧
  (∀ i ∈ Finset.Icc 1 J,
    fordPrimeCoordinate n J ≤ fordPrimeCoordinate n i ∧ fordPrimeCoordinate n i ≤ B x) ∧
  ∀ i ∈ Finset.Ico 0 J,
    (if i+1 = J then fordSimplexCoordinate x n J
     else ∑ r ∈ Finset.Icc (i+1) J, a (r-i) * fordSimplexCoordinate x n r) ≤
      xi x i * fordSimplexCoordinate x n i

/-- Ford Theorem 16, with its uniform exp(-Psi^2/4) exceptional-value bound. -/
def FordTheorem16Input : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ Ψ : ℕ, Ψ < m x →
      preimageExceptionCount x (fordSimplexCondition x Ψ) ≤
        C * V x * Real.exp (-(Ψ : ℝ)^2/4)

lemma fordSimplexCondition_coordinate_pos {x : ℝ} {Ψ n i : ℕ}
    (h : fordSimplexCondition x Ψ n) (hi : i ∈ Finset.Icc 1 (m x-Ψ)) :
    0 < fordPrimeCoordinate n i := by
  exact lt_of_lt_of_le (lt_trans (by norm_num) h.1) ((h.2.1 i hi).1)

/-- The weaker, unclamped simplex used in equation ford-simplex of the manuscript. -/
def extractedSimplexCondition (x : ℝ) (Ψ n : ℕ) : Prop :=
  let J := m x-Ψ
  2 < primeDoubleLog n J ∧
  ∀ i ∈ Finset.Ico 0 J,
    (∑ r ∈ Finset.Icc (i+1) J, a (r-i) * rawSimplexCoordinate x n r) ≤
      xi x i * rawSimplexCoordinate x n i

lemma outside_preimageExceptions_iff {x : ℝ} {Q : ℕ → Prop} {v : ℕ}
    (hv : v ∈ Finset.Icc 1 ⌊x⌋₊) :
    v ∉ preimageExceptionValues x Q ↔
      ∀ n : ℕ, 0 < n → n.totient = v → Q n := by
  classical
  constructor
  · intro h n hn hφ
    by_contra hnQ
    exact h (Finset.mem_filter.mpr ⟨hv, n, hn, hφ, hnQ⟩)
  · intro h hmem
    obtain ⟨_, n, hn, hφ, hnQ⟩ := Finset.mem_filter.mp hmem
    exact hnQ (h n hn hφ)

lemma preimageExceptionCount_mono {x : ℝ} {P Q : ℕ → Prop}
    (hPQ : ∀ n : ℕ, P n → Q n) :
    preimageExceptionCount x Q ≤ preimageExceptionCount x P := by
  classical
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hv, n, hn, hφ, hQ⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hv, n, hn, hφ, fun hP => hQ (hPQ n hP)⟩

lemma fordPrimeCoordinate_eq_raw_of_pos {n i : ℕ}
    (h : 0 < fordPrimeCoordinate n i) :
    fordPrimeCoordinate n i = primeDoubleLog n i := by
  have hraw : 0 < primeDoubleLog n i :=
    (lt_max_iff.mp h).resolve_left (lt_irrefl 0)
  exact max_eq_right hraw.le

lemma fordBandScale_pos {x : ℝ} {i : ℕ} (hB : 0 < B x) (hi : i < m x) :
    0 < fordBandScale x i := by
  have hm : (0 : ℝ) < m x := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le i) hi)
  have hi' : (i : ℝ) < m x := Nat.cast_lt.mpr hi
  exact mul_pos (mul_pos hB (pow_pos rho_pos _))
    (sub_pos.mpr ((div_lt_one hm).mpr hi'))

lemma fordBandCondition_removes_clamp {x η : ℝ} {i n : ℕ}
    (hscale : 0 < fordBandScale x i) (hη : η < 1)
    (hband : fordBandCondition x η i n) :
    fordPrimeCoordinate n i = primeDoubleLog n i ∧
      |primeDoubleLog n i / fordBandScale x i - 1| ≤ η := by
  change |fordPrimeCoordinate n i / fordBandScale x i - 1| ≤ η at hband
  have hratio : 0 < fordPrimeCoordinate n i / fordBandScale x i := by
    have hlow := (abs_le.mp hband).1
    linarith
  have hcoord : 0 < fordPrimeCoordinate n i := by
    have h := mul_pos hratio hscale
    simpa only [div_mul_cancel₀ _ hscale.ne'] using h
  have heq := fordPrimeCoordinate_eq_raw_of_pos hcoord
  exact ⟨heq, by simpa only [← heq] using hband⟩

lemma fordSimplexCondition_implies_extracted {x : ℝ} {Ψ n : ℕ}
    (hΨ : Ψ < m x) (h : fordSimplexCondition x Ψ n) :
    extractedSimplexCondition x Ψ n := by
  let J := m x-Ψ
  have hJ : 0 < J := Nat.sub_pos_of_lt hΨ
  change 2 < fordPrimeCoordinate n J ∧ _ at h
  obtain ⟨hterminal, horder, hinequalities⟩ := h
  have hraw (i : ℕ) (hi : i ∈ Finset.Icc 1 J) :
      fordPrimeCoordinate n i = primeDoubleLog n i :=
    fordPrimeCoordinate_eq_raw_of_pos
      (lt_of_lt_of_le (by linarith : (0 : ℝ) < fordPrimeCoordinate n J) (horder i hi).1)
  have hcoord (i : ℕ) (hi : i ≤ J) :
      fordSimplexCoordinate x n i = rawSimplexCoordinate x n i := by
    by_cases hi0 : i = 0
    · simp [fordSimplexCoordinate, rawSimplexCoordinate, hi0]
    · simp only [fordSimplexCoordinate, rawSimplexCoordinate, ite_eq_right hi0]
      exact hraw i (Finset.mem_Icc.mpr ⟨by omega, hi⟩)
  have hterminalraw : 2 < primeDoubleLog n J := by
    rwa [hraw J (Finset.mem_Icc.mpr ⟨hJ, le_rfl⟩)] at hterminal
  change 2 < primeDoubleLog n J ∧ _
  refine ⟨hterminalraw, ?_⟩
  intro i hi
  have hiJ : i < J := (Finset.mem_Ico.mp hi).2
  have hsource := hinequalities i hi
  rw [hcoord i hiJ.le] at hsource
  by_cases hlast : i+1 = J
  · rw [ite_eq_left hlast, hcoord J le_rfl] at hsource
    have hdiff : J-i = 1 := by omega
    rw [hlast, Finset.Icc_self, Finset.sum_singleton, hdiff]
    have hnonneg : 0 ≤ rawSimplexCoordinate x n J := by
      simp only [rawSimplexCoordinate, ite_eq_right (Nat.ne_of_gt hJ)]
      exact (lt_trans (by norm_num) hterminalraw).le
    have hmul : a 1 * rawSimplexCoordinate x n J ≤ rawSimplexCoordinate x n J := by
      simpa using mul_le_mul_of_nonneg_right (a_le_index (j := 1) le_rfl) hnonneg
    exact hmul.trans hsource
  · rw [ite_eq_right hlast] at hsource
    convert hsource using 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [hcoord r (Finset.mem_Icc.mp hr).2]

/-- Theorem 16 controls the weaker unclamped condition without changing its
exceptional-set constant or its quantifier over all preimages. -/
theorem extracted_simplex_exception_bound (hford : FordTheorem16Input) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ Ψ : ℕ, Ψ < m x →
        preimageExceptionCount x (extractedSimplexCondition x Ψ) ≤
          C * V x * Real.exp (-(Ψ : ℝ)^2/4) := by
  obtain ⟨C, hC, hbound⟩ := hford
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with x hx
  intro Ψ hΨ
  exact (preimageExceptionCount_mono
    (fun _ h => fordSimplexCondition_implies_extracted hΨ h)).trans (hx Ψ hΨ)

end TotientAsymptotic

end

end OAI
