import OAI.Combinatorics.BalancedRyser.Incidence.UnusedOffsetIncidence
import OAI.Combinatorics.BalancedRyser.Probability.UniformConditionalProduct

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Balanced.UnusedOffsetIncidence

theorem pmf_sum_real {α : Type*} [Fintype α] (μ : PMF α) :
    ∑ a, (μ a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => μ.apply_ne_top a)]
  have h : ∑ a, μ a = 1 := by simpa only [tsum_fintype] using μ.tsum_coe
  rw [h]
  simp

theorem pmf_outer_ne_top {α : Type*} (μ : PMF α) (E : Set α) :
    μ.toOuterMeasure E ≠ ⊤ := by
  rw [PMF.toOuterMeasure_apply]
  exact μ.tsum_coe_indicator_ne_top E

theorem bind_probability_le {α β : Type*} [Fintype α]
    (μ : PMF α) (ν : α → PMF β) (E : Set β) (r : ℝ)
    (h : ∀ a, ((ν a).toOuterMeasure E).toReal ≤ r) :
    ((μ.bind ν).toOuterMeasure E).toReal ≤ r := by
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype,
    ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top
      (μ.apply_ne_top a) (pmf_outer_ne_top (ν a) E))]
  simp_rw [ENNReal.toReal_mul]
  calc
    (∑ a, (μ a).toReal * ((ν a).toOuterMeasure E).toReal) ≤
        ∑ a, (μ a).toReal * r :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)
    _ = r := by rw [← Finset.sum_mul, pmf_sum_real μ, one_mul]

theorem uniform_product_probability_le {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (E : α → β → Prop) (r : ℝ)
    (h : ∀ a, probability (E a) ≤ r) :
    probability (fun z : α × β => E z.1 z.2) ≤ r := by
  rw [probability_eq_pmf, UniformConditionalProduct.uniform_product_eq_bind]
  apply bind_probability_le
  intro a
  rw [PMF.toOuterMeasure_map_apply]
  exact (probability_eq_pmf (E a)).symm ▸ h a

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def mixedUnusedLaw {α : Type*} (D : Finset (Direction F)) (μ : PMF α) :
    PMF (α × Offsets D) :=
  μ.bind (fun a => (PMF.uniformOfFintype (Offsets D)).map (fun o => (a, o)))

theorem mixed_precoverage_probability_le {α : Type*} [Fintype α]
    (D : Finset (Direction F)) (μ : PMF α) (p : α → Point F)
    (P : α → Finset (Point F)) (n : ℕ) (hP : ∀ a, (P a).card ≤ n) :
    ((mixedUnusedLaw D μ).toOuterMeasure
      {z | Precoverage D (p z.1) (P z.1) z.2}).toReal ≤
      2 * (D.card : ℝ) * (n : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  apply bind_probability_le
  intro a
  rw [PMF.toOuterMeasure_map_apply]
  change ((PMF.uniformOfFintype (Offsets D)).toOuterMeasure
    {o | Precoverage D (p a) (P a) o}).toReal ≤ _
  rw [← probability_eq_pmf]
  apply (precoverage_probability_le D (p a) (P a)).trans
  gcongr
  exact_mod_cast hP a

theorem mixed_noncollinearTriple_probability_le {α : Type*} [Fintype α]
    (D : Finset (Direction F)) (μ : PMF α)
    (P : α → Finset (Point F)) (n : ℕ) (hP : ∀ a, (P a).card ≤ n) :
    ((mixedUnusedLaw D μ).toOuterMeasure
      {z | NoncollinearTripleInPair D (P z.1) z.2}).toReal ≤
      6 * (n : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 2 := by
  apply bind_probability_le
  intro a
  rw [PMF.toOuterMeasure_map_apply]
  change ((PMF.uniformOfFintype (Offsets D)).toOuterMeasure
    {o | NoncollinearTripleInPair D (P a) o}).toReal ≤ _
  rw [← probability_eq_pmf]
  apply (noncollinearTripleInPair_probability_le D (P a)).trans
  gcongr
  exact_mod_cast hP a

theorem uniform_product_noncollinearTriple_probability_le {α : Type*}
    [Fintype α] [Nonempty α] (D : Finset (Direction F))
    (P : α → Finset (Point F)) (n : ℕ) (hP : ∀ a, (P a).card ≤ n) :
    probability (fun z : α × Offsets D => NoncollinearTripleInPair D (P z.1) z.2) ≤
      6 * (n : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 2 := by
  apply uniform_product_probability_le
    (fun a o => NoncollinearTripleInPair D (P a) o)
  intro a
  apply (noncollinearTripleInPair_probability_le D (P a)).trans
  gcongr
  exact_mod_cast hP a

end Balanced.UnusedOffsetIncidence

end

end OAI
