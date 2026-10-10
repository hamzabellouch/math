import OAI.Analysis.LipschitzHilbert.Trees.PathExpansion
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-!
# Integrating the vertex amount

The actual finite terminal flow gives pointwise good-path domination on the
large-mass region. Integrating that domination together with the
small-mass estimate extracts the normalized vertex energy from its
nonnegative amount. This is the finite nonnegative assembly in §11.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ ι : Type*} [MeasurableSpace α] [Fintype κ] [Fintype ι] {N : ℕ}

attribute [local instance] Classical.propDecidable

def goodPathSet (bad : α → Finset ι) (i : ι) : Set α := {x | i ∉ bad x}

def goodPathContribution (bad : α → Finset ι) (h Q : ι → α → ℝ) (i : ι) (x : α) : ℝ :=
  (goodPathSet bad i).indicator (fun y => h i y * Q i y) x

omit [MeasurableSpace α] [Fintype κ] in
theorem sum_goodPathContribution (bad : α → Finset ι) (h Q : ι → α → ℝ) (x : α) :
    (∑ i, goodPathContribution bad h Q i x) =
      ∑ i ∈ Finset.univ \ bad x, h i x * Q i x := by
  have hset : Finset.univ \ bad x = Finset.univ.filter (fun i => i ∉ bad x) := by
    ext i
    simp
  rw [hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ bad x <;> simp [goodPathContribution, goodPathSet, Set.indicator, hi]

omit [MeasurableSpace α] in
/-- The two spatial mass regimes fit into one nonnegative pointwise bound. -/
theorem vertex_amount_pointwise (F : α → TerminalFlow κ ι N)
    (bad : α → Finset ι) (n V : α → ℝ) (h e Q : ι → α → ℝ) (M C : ℝ)
    (hC : 0 ≤ C) (hn : ∀ x, 0 ≤ n x)
    (hh : ∀ i x, 0 ≤ h i x) (hQ : ∀ i x, 0 ≤ Q i x)
    (hsmallMass : ∀ x, n x ≤ M → V x ≤ C * n x)
    (hV : ∀ x, M < n x → 0 < V x)
    (he : ∀ x, M < n x → ∀ i, e i x ≤ C * h i x)
    (hprob : ∀ x, M < n x → ∀ i, (F x).terminalProbability i = e i x * Q i x / V x)
    (hrate : ∀ x, M < n x → ∀ i, (F x).exitRate i ≤ C * h i x)
    (hbad : ∀ x, M < n x → C * ∑ i ∈ bad x, h i x ≤ 1 / 2) (x : α) :
    V x ≤ C * n x + 2 * C * ∑ i, goodPathContribution bad h Q i x := by
  have hsum : 0 ≤ ∑ i, goodPathContribution bad h Q i x := by
    apply Finset.sum_nonneg
    intro i _
    exact Set.indicator_nonneg (fun y _ => mul_nonneg (hh i y) (hQ i y)) x
  by_cases hx : n x ≤ M
  · exact (hsmallMass x hx).trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hsum))
  · have hlarge : M < n x := lt_of_not_ge hx
    have hdom := good_path_amount_domination (F x) (bad x) (V x) C
      (fun i => h i x) (fun i => e i x) (fun i => Q i x) (hV x hlarge)
      (fun i => hQ i x) (he x hlarge) (hprob x hlarge) (hrate x hlarge) (hbad x hlarge)
    rw [← sum_goodPathContribution bad h Q x] at hdom
    exact hdom.trans (le_add_of_nonneg_left (mul_nonneg hC (hn x)))

/-- Integrate the vertex amount from actual good-path contributions. The only
analytic inputs are their proved restricted integral bounds. -/
theorem vertex_amount_integral (μ : Measure α) (F : α → TerminalFlow κ ι N)
    (bad : α → Finset ι) (n V : α → ℝ) (h e Q : ι → α → ℝ) (M C P : ℝ)
    (hC : 0 ≤ C)
    (hn : ∀ x, 0 ≤ n x) (hV0 : ∀ x, 0 ≤ V x)
    (hh : ∀ i x, 0 ≤ h i x) (hQ : ∀ i x, 0 ≤ Q i x)
    (hnmeas : AEStronglyMeasurable n μ) (hVmeas : AEStronglyMeasurable V μ)
    (hhint : ∀ i, Integrable (h i) μ) (hnmass : ∀ x, n x ≤ ∑ i, h i x)
    (hgood : ∀ i, MeasurableSet (goodPathSet bad i))
    (hpathInt : ∀ i, IntegrableOn (fun x => h i x * Q i x) (goodPathSet bad i) μ)
    (hpathBound : ∀ i, (∫ x in goodPathSet bad i, h i x * Q i x ∂μ) ≤ P * ∫ x, h i x ∂μ)
    (hsmallMass : ∀ x, n x ≤ M → V x ≤ C * n x)
    (hV : ∀ x, M < n x → 0 < V x)
    (he : ∀ x, M < n x → ∀ i, e i x ≤ C * h i x)
    (hprob : ∀ x, M < n x → ∀ i, (F x).terminalProbability i = e i x * Q i x / V x)
    (hrate : ∀ x, M < n x → ∀ i, (F x).exitRate i ≤ C * h i x)
    (hbad : ∀ x, M < n x → C * ∑ i ∈ bad x, h i x ≤ 1 / 2) :
    Integrable V μ ∧ (∫ x, V x ∂μ) ≤ C * (1 + 2 * P) * ∑ i, ∫ x, h i x ∂μ := by
  have hnint : Integrable n μ := (integrable_finsetSum _ (fun i _ => hhint i)).mono' hnmeas
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hn x)]
      exact hnmass x)
  have htermInt (i : ι) : Integrable (goodPathContribution bad h Q i) μ :=
    (integrable_indicator_iff (hgood i)).2 (hpathInt i)
  have hsumInt : Integrable (fun x => ∑ i, goodPathContribution bad h Q i x) μ :=
    integrable_finsetSum _ (fun i _ => htermInt i)
  have hpoint := vertex_amount_pointwise F bad n V h e Q M C hC hn hh hQ
    hsmallMass hV he hprob hrate hbad
  have hVint : Integrable V μ := ((hnint.const_mul C).add (hsumInt.const_mul (2 * C))).mono'
    hVmeas (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hV0 x)]
      exact hpoint x)
  have hnBound : (∫ x, n x ∂μ) ≤ ∑ i, ∫ x, h i x ∂μ := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hhint i)]
    exact integral_mono hnint (integrable_finsetSum _ (fun i _ => hhint i)) hnmass
  have hsumBound : (∫ x, ∑ i, goodPathContribution bad h Q i x ∂μ) ≤
      P * ∑ i, ∫ x, h i x ∂μ := by
    rw [integral_finsetSum Finset.univ (fun i _ => htermInt i), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change (∫ x, (goodPathSet bad i).indicator (fun y => h i y * Q i y) x ∂μ) ≤ _
    rw [integral_indicator (hgood i)]
    exact hpathBound i
  refine ⟨hVint, ?_⟩
  calc
    (∫ x, V x ∂μ) ≤ ∫ x, (C * n x + (2 * C) * ∑ i, goodPathContribution bad h Q i x) ∂μ :=
      integral_mono hVint ((hnint.const_mul C).add (hsumInt.const_mul (2 * C))) hpoint
    _ = C * (∫ x, n x ∂μ) + (2 * C) * ∫ x, ∑ i, goodPathContribution bad h Q i x ∂μ := by
      rw [integral_add (hnint.const_mul C) (hsumInt.const_mul (2 * C)),
        integral_const_mul, integral_const_mul]
    _ ≤ C * (∑ i, ∫ x, h i x ∂μ) + (2 * C) * (P * ∑ i, ∫ x, h i x ∂μ) :=
      add_le_add (mul_le_mul_of_nonneg_left hnBound hC)
        (mul_le_mul_of_nonneg_left hsumBound (by positivity))
    _ = _ := by ring

section Energy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual vertex amount from §11. -/
def vertexAmount (n : ℝ) (A : E) (a p : ℝ) : ℝ := n + n ^ (a - p) * ‖A‖ ^ p

omit [MeasurableSpace α] [Fintype κ] [Fintype ι] in
theorem normalized_vertex_energy_eq {n a p : ℝ} (hn : 0 < n) (hp : p ≠ 0) (A : E) :
    ‖(n ^ (a / p - 1)) • A‖ ^ p = n ^ (a - p) * ‖A‖ ^ p := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn.le _),
    Real.mul_rpow (Real.rpow_nonneg hn.le _) (norm_nonneg _), ← Real.rpow_mul hn.le]
  have heq : (a / p - 1) * p = a - p := by
    have h := div_mul_cancel₀ a hp
    nlinarith
  rw [heq]

omit [Fintype κ] [Fintype ι] in
/-- Subtracting the integrable mass baseline extracts the normalized energy
without any extra domination or measurability assumption on that energy. -/
theorem normalized_vertex_energy_integrable (μ : Measure α)
    (n : α → ℝ) (A : α → E) {a p : ℝ} (hn : ∀ x, 0 < n x) (hp : p ≠ 0)
    (hnint : Integrable n μ) (hVint : Integrable (fun x => vertexAmount (n x) (A x) a p) μ) :
    Integrable (fun x => ‖(n x ^ (a / p - 1)) • A x‖ ^ p) μ := by
  have heq : (fun x => ‖(n x ^ (a / p - 1)) • A x‖ ^ p) =
      fun x => vertexAmount (n x) (A x) a p - n x := by
    funext x
    rw [normalized_vertex_energy_eq (hn x) hp]
    unfold vertexAmount
    ring
  rw [heq]
  exact hVint.sub hnint

omit [Fintype κ] [Fintype ι] in
/-- An integrated amount bound gives the desired vertex Lp energy bound. -/
theorem normalized_vertex_moment_le (μ : Measure α)
    (n : α → ℝ) (A : α → E) {a p T : ℝ} (hn : ∀ x, 0 < n x) (hp : 0 < p)
    (hnint : Integrable n μ) (hVint : Integrable (fun x => vertexAmount (n x) (A x) a p) μ)
    (hbound : (∫ x, vertexAmount (n x) (A x) a p ∂μ) ≤ T) :
    (∫ x, ‖(n x ^ (a / p - 1)) • A x‖ ^ p ∂μ) ^ (1 / p) ≤ T ^ (1 / p) := by
  have henergy := normalized_vertex_energy_integrable μ n A hn hp.ne' hnint hVint
  have hle : (∫ x, ‖(n x ^ (a / p - 1)) • A x‖ ^ p ∂μ) ≤ T := by
    apply (integral_mono henergy hVint _).trans hbound
    intro x
    change ‖(n x ^ (a / p - 1)) • A x‖ ^ p ≤ vertexAmount (n x) (A x) a p
    rw [normalized_vertex_energy_eq (hn x) hp.ne']
    exact le_add_of_nonneg_left (hn x).le
  exact Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
    hle (one_div_nonneg.mpr hp.le)

end Energy

end LipschitzHilbert

end

end OAI
