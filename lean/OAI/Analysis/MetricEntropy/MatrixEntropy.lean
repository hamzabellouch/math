import OAI.Analysis.MetricEntropy.EntropyPair
import OAI.Analysis.MetricEntropy.MatrixToBody
import OAI.Analysis.MetricEntropy.EntropyBounds
import OAI.Analysis.MetricEntropy.EntropyComparison
import OAI.Analysis.MetricEntropy.PrimeChoice

namespace OAI

universe uX uY

/-!
# Entropy bounds for the actual matrix-to-body output

This intermediate lemma joins the proved geometric conversion to the scalar
entropy estimates. The final construction supplies its literal matrix,
separation and approximation list from the finite-field and compression
theorems; none of these inputs is left as a final endpoint premise.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped Pointwise

/-- Turn an actual separated and compressed matrix into the complete output
record, including finite-cover witnesses and positivity of both cover counts. -/
theorem entropyPair_of_matrix {X : Type uX} {Y : Type uY} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (a : ℝ) (ha : 1 ≤ a) (r : ℕ) (hr : 0 < r)
    (B : ℝ) (hB : 0 < B) (p : ℕ) (hp : p.Prime)
    (hprime : Real.exp (B * encodingCost (compressionRadius a) (accuracy a)
      (directionCount r (compressionRadius a) (accuracy a)) /
        (formDimension r (compressionRadius a) : ℝ)) < (p : ℝ))
    (g : Y → X → ℝ)
    (hrows : Fintype.card X = p ^ formDimension r (compressionRadius a))
    (hcolumns : Fintype.card X ≤ Fintype.card Y)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|)
    (A : Finset (RealSpace X))
    (hA : UniformApproximation g (6 * accuracy a) A)
    (Q : ℕ) (hAQ : A.card ≤ Q ^ 2)
    (hQ : Real.log (Q : ℝ) ≤
      (compressionRadius a : ℝ) * (pivotSlots (accuracy a) : ℝ) *
        Real.log ((p : ℝ) ^ formDimension r (compressionRadius a - 1)) +
          encodingCost (compressionRadius a) (accuracy a)
            (directionCount r (compressionRadius a) (accuracy a))) :
    Nonempty (EntropyPair a r B) := by
  have hθ := accuracy_pos ha
  have hh := compressionRadius_pos a
  have hD := formDimension_pos (j := compressionRadius a) hr
  obtain ⟨hn, K, hK, hcube, hfin, hdualfin, hlo, hhi⟩ :=
    matrix_to_body_fin g (by positivity : 0 ≤ 6 * accuracy a) hθ hsep A hA
  have hscale : 6 * (6 * accuracy a) + 2 * accuracy a = 38 * accuracy a := by ring
  rw [hscale] at hdualfin hhi
  obtain ⟨hdualfin', hmono⟩ := polar_cover_enlarge K
    (by positivity : 0 < 38 * accuracy a) (accuracy_cover_scale ha).le hdualfin
  have hdualpos : 0 < coveringNumber (polar (cube (Fin (Fintype.card Y))))
      (a⁻¹ • polar K) := by
    apply coveringNumber_pos _ hdualfin'
    refine ⟨0, ?_⟩
    intro x hx
    simp
  have hN : p ^ formDimension r (compressionRadius a) ≤
      coveringNumber K (cube (Fin (Fintype.card Y))) := by
    simpa only [hrows] using hlo
  have hm : 1 < p ^ formDimension r (compressionRadius a) :=
    Nat.one_lt_pow (Nat.ne_of_gt hD) hp.one_lt
  have hNpos := hm.trans_le hN
  have hdualQ := hmono.trans (hhi.trans hAQ)
  have hmR : (1 : ℝ) < (p : ℝ) ^ formDimension r (compressionRadius a) := by
    exact_mod_cast hm
  have hNR : (p : ℝ) ^ formDimension r (compressionRadius a) ≤
      (coveringNumber K (cube (Fin (Fintype.card Y))) : ℝ) := by
    exact_mod_cast hN
  have hdualR : (1 : ℝ) ≤
      (coveringNumber (polar (cube (Fin (Fintype.card Y)))) (a⁻¹ • polar K) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hdualpos)
  have hdualQR :
      (coveringNumber (polar (cube (Fin (Fintype.card Y)))) (a⁻¹ • polar K) : ℝ) ≤
        (Q : ℝ) ^ 2 := by exact_mod_cast hdualQ
  have hratios := entropy_ratio_bounds hmR hNR hdualR hdualQR
  have hcompression := form_entropy_ratio_le hr hh hp.one_lt hQ
  have hencoding := prime_choice_encoding_ratio_lt hp hD hB hprime
  have hratiosmall : entropyRatio a K < entropyBudget a r B := by
    apply lt_of_le_of_lt hratios.2
    exact hcompression.trans_lt (add_lt_add_of_le_of_lt (le_refl _) hencoding)
  have hrn : r ≤ Fintype.card Y :=
    rank_le_ambientDimension hr hh hp.two_le (by simpa only [hrows] using hcolumns)
  exact ⟨{
    dimension := Fintype.card Y
    dimension_pos := hn
    rank_le_dimension := hrn
    body := K
    body_isSymmetricConvexBody := hK
    cube_isSymmetricConvexBody := hcube
    primal_coverable := hfin
    dual_coverable := hdualfin'
    primal_one_lt := hNpos
    dual_pos := hdualpos
    primal_log_pos := Real.log_pos (by exact_mod_cast hNpos)
    ratio_nonneg := hratios.1
    ratio_lt := hratiosmall
  }⟩

end MetricEntropyDuality

end

end OAI
