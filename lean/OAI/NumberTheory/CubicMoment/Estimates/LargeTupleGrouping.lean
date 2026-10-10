import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleExponents

namespace OAI

/-! Uniform grouping for the actual large-row prime tuples, outside the
specified neighborhood of the exceptional three-prime configuration. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def largePrimeTupleExceptional {i j : ℕ} (δ : ℝ)
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) : Prop :=
  i+j = 3 ∧ (∑ a, |largePrimeTupleExponent q a-1/3|) < δ

theorem largePrimeTuple_grouping_gap (i j : ℕ) {ξ δ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (ℓ : ℤ) (Ct : ℕ) (H X : ℝ),
      1 ≤ X → 200 ≤ Real.log X →
      ∀ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0 →
        ¬largePrimeTupleExceptional δ q →
        ∃ s : Finset (Fin i ⊕ Fin j),
          1/3+ε ≤ ∑ a ∈ s, largePrimeTupleExponent q a ∧
          (∑ a ∈ s, largePrimeTupleExponent q a) ≤ 2/3-ε := by
  obtain ⟨ε,hε,hgap⟩ := uniform_prime_grouping_gap (ι := Fin i ⊕ Fin j)
    (by positivity : (0:ℝ) < ξ/2) (by norm_num : (13/20:ℝ) < 2/3) hδ
  refine ⟨ε,hε,?_⟩
  intro ℓ Ct H X hX hlog q hq hne hordinary
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hlo := Real.log_le_log (by positivity : (0:ℝ) < X/2)
    (largePrimeTupleTerm_product_range hXp hne).1
  rw [Real.log_div hXp.ne' (by norm_num)] at hlo
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have hn : Real.log (norm (largePrimeTupleProduct q)) ≠ 0 := by
    dsimp only [largePrimeTupleProduct]
    linarith
  apply hgap (largePrimeTupleExponent q)
    (largePrimeTupleExponent_bounds hX hlog hξ hξz hq hne)
    (largePrimeTupleExponent_sum hq hn)
  intro hc
  have hij : i+j = 3 := by simpa using hc
  exact le_of_not_gt (fun hd => hordinary ⟨hij,hd⟩)

lemma largePrimeTuple_short_subset {i j : ℕ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hsum : (∑ a, largePrimeTupleExponent q a) = 1) {ε : ℝ}
    {s : Finset (Fin i ⊕ Fin j)}
    (hl : 1/3+ε ≤ ∑ a ∈ s, largePrimeTupleExponent q a)
    (hu : (∑ a ∈ s, largePrimeTupleExponent q a) ≤ 2/3-ε) :
    ∃ t : Finset (Fin i ⊕ Fin j),
      1/3+ε ≤ ∑ a ∈ t, largePrimeTupleExponent q a ∧
      (∑ a ∈ t, largePrimeTupleExponent q a) ≤ 1/2 := by
  classical
  by_cases hhalf : (∑ a ∈ s, largePrimeTupleExponent q a) ≤ 1/2
  · exact ⟨s,hl,hhalf⟩
  · refine ⟨Finset.univ\s,?_,?_⟩
    all_goals have he := Finset.sum_sdiff (Finset.subset_univ s) (f := largePrimeTupleExponent q)
    all_goals rw [hsum] at he
    · linarith
    · linarith [not_le.mp hhalf]

lemma largePrimeTuple_subset_norm_bounds {i j : ℕ} {X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hn : 0 < norm (largePrimeTupleProduct q))
    (hln : 0 < Real.log (norm (largePrimeTupleProduct q)))
    (s : Finset (Fin i ⊕ Fin j)) {l u : ℝ}
    (hl : l ≤ ∑ a ∈ s, largePrimeTupleExponent q a)
    (hu : (∑ a ∈ s, largePrimeTupleExponent q a) ≤ u) :
    norm (largePrimeTupleProduct q)^l ≤ ∏ a ∈ s, largePrimeTupleNorm q a ∧
      (∏ a ∈ s, largePrimeTupleNorm q a) ≤ norm (largePrimeTupleProduct q)^u := by
  have hp : 0 < ∏ a ∈ s, largePrimeTupleNorm q a :=
    Finset.prod_pos (fun a _ha => zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1)
  have he : Real.log (∏ a ∈ s, largePrimeTupleNorm q a) =
      (∑ a ∈ s, largePrimeTupleExponent q a)*Real.log (norm (largePrimeTupleProduct q)) := by
    rw [Real.log_prod (fun a _ha =>
      (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1).ne')]
    simp only [largePrimeTupleExponent]
    rw [←Finset.sum_div,div_mul_cancel₀ _ hln.ne']
  constructor
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hn l) hp).mp
    rw [Real.log_rpow hn,he]
    nlinarith [mul_le_mul_of_nonneg_right hl hln.le]
  · apply (Real.log_le_log_iff hp (Real.rpow_pos_of_pos hn u)).mp
    rw [Real.log_rpow hn,he]
    nlinarith [mul_le_mul_of_nonneg_right hu hln.le]

end CubicFirstMoment

end

end OAI
