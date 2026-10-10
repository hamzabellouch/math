import OAI.Analysis.FiniteFactor.Coupling.Bayes
import Mathlib.Analysis.PSeries

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The source's kappa_s, with natural indices shifted to start at one. -/
def sourceKappa (s : ℕ) : ℝ := 1 / (100*((s : ℝ)+1))

theorem sourceKappa_sq_summable : Summable (fun s => sourceKappa s ^ 2) := by
  have hs : Summable (fun s : ℕ => 1/(s : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs' := (summable_nat_add_iff 1).2 hs
  have heq (s : ℕ) : sourceKappa s ^ 2 = (1/10000 : ℝ) * (1/((s+1 : ℕ) : ℝ)^2) := by
    simp only [sourceKappa, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  simp_rw [heq]
  exact hs'.mul_left _

namespace CouplingParameters

theorem block_energy_cancellation (p : CouplingParameters) :
    p.m * (2*p.kappa^2/p.m + p.tagMass) = 2*p.kappa^2 + if p.tagged then 1 else 0 := by
  unfold tagMass
  split <;> field_simp [p.m_pos.ne']
  simp

/-- The sum over arbitrary finite sets of whole blocks is uniformly bounded.
The unique tagged block contributes at most one, even when it is absent. -/
theorem uniform_block_budget (p : ℕ → CouplingParameters) (j : ℕ)
    (htag : ∀ s, (p s).tagged = decide (s=j))
    (hκ : Summable (fun s => (p s).kappa^2)) (B : Finset ℕ) :
    (∑ s ∈ B, (p s).m * (2*(p s).kappa^2/(p s).m + (p s).tagMass)) ≤
      2*(∑' s, (p s).kappa^2) + 1 := by
  simp_rw [block_energy_cancellation, htag, decide_eq_true_eq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hs := hκ.sum_le_tsum B (fun s _ => sq_nonneg ((p s).kappa))
  have ht : (∑ s ∈ B, if s=j then (1 : ℝ) else 0) ≤ 1 := by
    simp only [Finset.sum_ite_eq']
    split <;> norm_num
  linarith

/-- A coordinate may be omitted altogether, and every included coordinate may
choose its endpoint independently of every other coordinate. -/
def selectedDensity (p : CouplingParameters) (enabled right : Bool) (t : ℝ) : ℝ :=
  if enabled then p.endpointDensity right t else 1

theorem selectedDensity_energy (p : CouplingParameters) (enabled right : Bool) :
    (∫ t, p.selectedDensity enabled right t ^ 2 ∂unitIntervalMeasure) ≤
      1 + 20*(2*p.kappa^2/p.m + p.tagMass) := by
  cases enabled
  · simp only [selectedDensity, Bool.false_eq_true, ↓reduceIte, one_pow]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    have he : 0 ≤ 20*(2*p.kappa^2/p.m + p.tagMass) :=
      mul_nonneg (by norm_num) (add_nonneg
        (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) p.m_pos.le) p.tagMass_nonneg)
    linarith
  · exact p.endpointDensity_source_energy right

/-- Actual finite product of the chosen coordinate densities. -/
def finiteProductDensity {ι : Type*} [Fintype ι] (p : ι → CouplingParameters)
    (enabled right : ι → Bool) (x : ι → ℝ) : ℝ :=
  ∏ i, (p i).selectedDensity (enabled i) (right i) (x i)

theorem finiteProductDensity_energy {ι : Type*} [Fintype ι]
    (p : ι → CouplingParameters) (enabled right : ι → Bool) :
    (∫ x, finiteProductDensity p enabled right x ^ 2
      ∂Measure.pi (fun _ : ι => unitIntervalMeasure)) ≤
      Real.exp (∑ i, 20*(2*(p i).kappa^2/(p i).m + (p i).tagMass)) := by
  unfold finiteProductDensity
  rw [product_density_sq_integral]
  exact product_energy_le_exp _ _ (fun i => integral_nonneg (fun _ => sq_nonneg _))
    (fun i => (p i).selectedDensity_energy (enabled i) (right i))

/-- Prefixes and all intermediate endpoint selections have a common square
integral bound. A finite prefix is represented by enabling its coordinates
inside any finite collection of blocks containing that prefix. -/
theorem finite_block_product_uniform (p : ℕ → CouplingParameters) (m : ℕ → ℕ)
    (hm : ∀ s, (p s).m = (m s : ℝ)) (j : ℕ)
    (htag : ∀ s, (p s).tagged = decide (s=j))
    (hκ : Summable (fun s => (p s).kappa^2)) (B : Finset ℕ)
    (enabled right : (Σ s : B, Fin (m s)) → Bool) :
    (∫ x, finiteProductDensity (fun i : Σ s : B, Fin (m s) => p i.1)
      enabled right x ^ 2 ∂Measure.pi (fun _ : Σ s : B, Fin (m s) => unitIntervalMeasure)) ≤
      Real.exp (20*(2*(∑' s, (p s).kappa^2)+1)) := by
  apply (finiteProductDensity_energy _ enabled right).trans
  apply Real.exp_le_exp.mpr
  have heq : (∑ i : Σ s : B, Fin (m s), 20*(2*(p i.1).kappa^2/(p i.1).m + (p i.1).tagMass)) =
      20 * ∑ s ∈ B, (p s).m * (2*(p s).kappa^2/(p s).m + (p s).tagMass) := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change (∑ s : B, (fun s : ℕ => (m s : ℝ) * (20*(2*(p s).kappa^2/(p s).m + (p s).tagMass))) s) = _
    rw [Finset.sum_coe_sort B (fun s => (m s : ℝ) * (20*(2*(p s).kappa^2/(p s).m + (p s).tagMass)))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [hm s]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (uniform_block_budget p j htag hκ B) (by norm_num)

theorem selectedDensity_nonneg (p : CouplingParameters) (enabled right : Bool) (t : ℝ) :
    0 ≤ p.selectedDensity enabled right t := by
  cases enabled
  · exact zero_le_one
  · exact (p.diagonalMass_pos.trans_le (p.endpointDensity_lower right t)).le

theorem selectedDensity_le_ten (p : CouplingParameters) (enabled right : Bool) (t : ℝ) :
    p.selectedDensity enabled right t ≤ 10 := by
  cases enabled
  · norm_num [selectedDensity]
  · exact (p.endpointDensity_lt_ten right t).le

theorem selectedDensity_measurable (p : CouplingParameters) (enabled right : Bool) :
    Measurable (p.selectedDensity enabled right) := by
  cases enabled
  · exact measurable_const
  · exact p.endpointDensity_measurable right

theorem selectedDensity_memLp (p : CouplingParameters) (enabled right : Bool) :
    MemLp (p.selectedDensity enabled right) 2 unitIntervalMeasure := by
  cases enabled
  · exact memLp_const 1
  · exact p.endpointDensity_memLp right

theorem selectedDensity_integral (p : CouplingParameters) (enabled right : Bool) :
    ∫ t, p.selectedDensity enabled right t ∂unitIntervalMeasure = 1 := by
  cases enabled
  · simp [selectedDensity]
  · exact p.endpointDensity_integral right

theorem finiteProductDensity_measurable {ι : Type*} [Fintype ι]
    (p : ι → CouplingParameters) (enabled right : ι → Bool) :
    Measurable (finiteProductDensity p enabled right) := by
  exact Finset.measurable_prod _ fun i _ =>
    ((p i).selectedDensity_measurable (enabled i) (right i)).comp (measurable_pi_apply i)

/-- Membership in L2 is proved, so the uniform square-integral bound is not
an assertion about a Bochner integral of a nonintegrable function. -/
theorem finiteProductDensity_memLp {ι : Type*} [Fintype ι]
    (p : ι → CouplingParameters) (enabled right : ι → Bool) :
    MemLp (finiteProductDensity p enabled right) 2 (Measure.pi (fun _ : ι => unitIntervalMeasure)) := by
  apply MemLp.of_bound (finiteProductDensity_measurable p enabled right).aestronglyMeasurable
    ((10 : ℝ)^(Fintype.card ι))
  apply Filter.Eventually.of_forall
  intro x
  have hnon : 0 ≤ finiteProductDensity p enabled right x :=
    Finset.prod_nonneg fun i _ => (p i).selectedDensity_nonneg (enabled i) (right i) (x i)
  rw [Real.norm_of_nonneg hnon]
  unfold finiteProductDensity
  calc
    _ ≤ ∏ _i : ι, (10 : ℝ) := Finset.prod_le_prod₀
      (fun i _ => (p i).selectedDensity_nonneg (enabled i) (right i) (x i))
      (fun i _ => (p i).selectedDensity_le_ten (enabled i) (right i) (x i))
    _ = _ := by simp

theorem finiteProductDensity_integral {ι : Type*} [Fintype ι]
    (p : ι → CouplingParameters) (enabled right : ι → Bool) :
    ∫ x, finiteProductDensity p enabled right x ∂Measure.pi (fun _ : ι => unitIntervalMeasure) = 1 := by
  unfold finiteProductDensity
  rw [integral_fintype_prod_eq_prod (fun i => (p i).selectedDensity (enabled i) (right i))]
  simp [selectedDensity_integral]

/-- Exact source kappa, independent of the tagged stage, yields one fixed bound. -/
theorem finite_block_product_source_uniform (p : ℕ → CouplingParameters) (m : ℕ → ℕ)
    (hm : ∀ s, (p s).m = (m s : ℝ)) (j : ℕ)
    (htag : ∀ s, (p s).tagged = decide (s=j)) (hκ : ∀ s, (p s).kappa = sourceKappa s)
    (B : Finset ℕ) (enabled right : (Σ s : B, Fin (m s)) → Bool) :
    (∫ x, finiteProductDensity (fun i : Σ s : B, Fin (m s) => p i.1)
      enabled right x ^ 2 ∂Measure.pi (fun _ : Σ s : B, Fin (m s) => unitIntervalMeasure)) ≤
      Real.exp (20*(2*(∑' s, sourceKappa s ^ 2)+1)) := by
  have hs : Summable (fun s => (p s).kappa^2) := by simpa only [hκ] using sourceKappa_sq_summable
  simpa only [hκ] using finite_block_product_uniform p m hm j htag hs B enabled right

end CouplingParameters
end
end FiniteFactor

end OAI
