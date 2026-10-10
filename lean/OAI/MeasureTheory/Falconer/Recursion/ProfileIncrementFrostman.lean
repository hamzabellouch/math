import OAI.MeasureTheory.Falconer.Measures.ConditionalFrostman

namespace OAI

/-! # Turning a contact-interval profile inequality into actual conditional ball bounds -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem profileDrop_le_of_increment (m : ℝ → ℝ) (N : ℕ) (s E : ℝ)
    {p t : ℕ} (hpt : p ≤ t)
    (hinc : ∀ n, p ≤ n → n ≤ t → s*(n-p:ℕ)/N-E ≤ m n-m p) :
    profileDrop m N s p t ≤ E := by
  obtain ⟨i,hpi,hit,hmin⟩ := PlanarFalconer.intervalMin_attained
    (fun n : ℕ => m n-s*(n:ℝ)/N) hpt
  unfold profileDrop
  rw [hmin]
  have hh := hinc i hpi hit
  rw [Nat.cast_sub hpi] at hh
  have he : s*((i:ℝ)-(p:ℝ))/N = s*(i:ℝ)/N-s*(p:ℝ)/N := by ring
  rw [he] at hh
  linarith

theorem sourceClass_conditional_frostman_of_increment (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^(t-p) ≤ r → r ≤ 1 →
      (Measure.map (cellScaleMap p (Q.descendant P).center)
        (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)) (ball x r) ≤
      ENNReal.ofReal ((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam)*r^s) := by
  intro x r hr hr1
  apply (sourceClass_conditional_frostman Q hQ μ hN hB hs hwidth hlarge hp₀ hpt htN hP hPpos x r hr hr1).trans
  apply ENNReal.ofReal_le_ofReal
  have hr0 : 0 ≤ r := (show 0 ≤ 1/(2:ℝ)^(t-p) by positivity).trans hr
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr0 s)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  exact add_le_add (profileDrop_le_of_increment _ N s E hpt hinc) le_rfl

end Falconer.Regularization

end OAI
