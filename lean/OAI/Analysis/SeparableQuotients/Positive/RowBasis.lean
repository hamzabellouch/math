import Mathlib

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Rows
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev ClosedSpan (v : ℕ → V) : Submodule ℝ V :=
  (Submodule.span ℝ (Set.range v)).topologicalClosure

def spanVector (v : ℕ → V) (i : ℕ) : ClosedSpan v :=
  ⟨v i, Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self i))⟩

def spanCombination (v : ℕ → V) : (ℕ →₀ ℝ) →ₗ[ℝ] ClosedSpan v :=
  Finsupp.linearCombination ℝ (spanVector v)

lemma spanCombination_coe (v : ℕ → V) (c : ℕ →₀ ℝ) :
    (spanCombination v c : V) = c.sum (fun i a => a • v i) := by
  simp [spanCombination, Finsupp.linearCombination_apply, Finsupp.sum, spanVector]

lemma denseRange_spanCombination (v : ℕ → V) : DenseRange (spanCombination v) := by
  rw [DenseRange, Subtype.dense_iff]
  have hr : (Subtype.val : ClosedSpan v → V) '' Set.range (spanCombination v) =
      (Submodule.span ℝ (Set.range v) : Set V) := by
    rw [← Set.range_comp]
    change Set.range (fun c => (spanCombination v c : V)) = _
    simp only [spanCombination_coe]
    change Set.range (Finsupp.linearCombination ℝ v) = _
    exact congrArg (fun s : Submodule ℝ V => (s : Set V))
      (Finsupp.range_linearCombination ℝ (v := v))
  change (ClosedSpan v : Set V) ⊆ closure ((Subtype.val : ClosedSpan v → V) '' Set.range (spanCombination v))
  rw [hr]
  exact Set.Subset.rfl


def PrefixBoundTwo (v : ℕ → V) : Prop :=
  ∀ (c : ℕ →₀ ℝ) (m : ℕ),
    ‖∑ i ∈ Finset.range m, c i • v i‖ ≤ 2 * ‖c.sum (fun i a => a • v i)‖

lemma prefix_coefficient_bound (v : ℕ → V) (h : PrefixBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (c : ℕ →₀ ℝ) (i : ℕ) :
    ‖c i‖ ≤ (4 / a) * ‖spanCombination v c‖ := by
  have hdiff : c i • v i = (∑ j ∈ Finset.range (i+1), c j • v j) -
      (∑ j ∈ Finset.range i, c j • v j) := by rw [Finset.sum_range_succ]; abel
  have hh : ‖c i • v i‖ ≤ 4 * ‖c.sum (fun i a => a • v i)‖ := by
    rw [hdiff]
    exact (norm_sub_le _ _).trans ((add_le_add (h c (i+1)) (h c i)).trans_eq (by ring))
  rw [norm_smul] at hh
  have hb : ‖c i‖ * a ≤ 4 * ‖spanCombination v c‖ := by
    exact (mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)).trans
      (by simpa only [← spanCombination_coe, Submodule.norm_coe] using hh)
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ ha).mpr hb


def prefixCoord (v : ℕ → V) (i : ℕ) : StrongDual ℝ (ClosedSpan v) :=
  (Finsupp.lapply i).extendOfNorm (spanCombination v)

lemma prefixCoord_combination (v : ℕ → V) (h : PrefixBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (c : ℕ →₀ ℝ) (i : ℕ) :
    prefixCoord v i (spanCombination v c) = c i := by
  apply LinearMap.extendOfNorm_eq (denseRange_spanCombination v)
  exact ⟨4 / a, fun c => prefix_coefficient_bound v h ha hv c i⟩

lemma prefixCoord_bound (v : ℕ → V) (h : PrefixBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (x : ClosedSpan v) (i : ℕ) :
    ‖prefixCoord v i x‖ ≤ (4 / a) * ‖x‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le (denseRange_spanCombination v) _
    (fun c => prefix_coefficient_bound v h ha hv c i) x

lemma prefixCoord_ortho (v : ℕ → V) (h : PrefixBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (i j : ℕ) :
    prefixCoord v i (spanVector v j) = (Pi.single j (1 : ℝ) : ℕ → ℝ) i := by
  have hc : spanCombination v (Finsupp.single j 1) = spanVector v j := by
    simp [spanCombination]
  rw [← hc, prefixCoord_combination v h ha hv]
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]


def prefixProjection (v : ℕ → V) (s : Finset ℕ) :
    ClosedSpan v →L[ℝ] ClosedSpan v :=
  ∑ i ∈ s, (prefixCoord v i).smulRight (spanVector v i)

lemma prefixProjection_apply (v : ℕ → V) (s : Finset ℕ) (x : ClosedSpan v) :
    prefixProjection v s x = ∑ i ∈ s, prefixCoord v i x • spanVector v i := by
  simp [prefixProjection]

lemma prefixProjection_bound (v : ℕ → V) (h : PrefixBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (m : ℕ) (x : ClosedSpan v) :
    ‖prefixProjection v (Finset.range m) x‖ ≤ 2 * ‖x‖ := by
  refine (denseRange_spanCombination v).induction_on x (p := fun x =>
    ‖prefixProjection v (Finset.range m) x‖ ≤ 2 * ‖x‖) ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro c
    rw [prefixProjection_apply]
    simp only [prefixCoord_combination v h ha hv]
    have hh := h c m
    change ‖((∑ i ∈ Finset.range m, c i • spanVector v i : ClosedSpan v) : V)‖ ≤
      2 * ‖(spanCombination v c : V)‖
    simpa only [Submodule.coe_sum, Submodule.coe_smul, spanVector, spanCombination_coe] using hh

lemma prefixProjection_combination (v : ℕ → V) (h : PrefixBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (c : ℕ →₀ ℝ)
    (s : Finset ℕ) (hs : c.support ⊆ s) :
    prefixProjection v s (spanCombination v c) = spanCombination v c := by
  rw [prefixProjection_apply]
  simp only [prefixCoord_combination v h ha hv]
  exact (Finsupp.sum_of_support_subset c hs (fun i a => a • spanVector v i) (by simp)).symm

lemma prefix_expansion (v : ℕ → V) (h : PrefixBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) (x : ClosedSpan v) :
    HasSum (fun i => prefixCoord v i x • spanVector v i) x (SummationFilter.conditional ℕ) := by
  have hequi : Equicontinuous (fun m : ℕ =>
      (prefixProjection v (Finset.range m) : ClosedSpan v → ClosedSpan v)) := by
    have hb : ∃ C : ℝ, ∀ (m : ℕ) (y : ClosedSpan v),
        ‖prefixProjection v (Finset.range m) y‖ ≤ C * ‖y‖ :=
      ⟨2, fun m y => prefixProjection_bound v h ha hv m y⟩
    exact ((NormedSpace.equicontinuous_TFAE (fun m => prefixProjection v (Finset.range m))).out 4 2).mp hb
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  change Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, prefixCoord v i x • spanVector v i)
    atTop (𝓝 x)
  simp only [← prefixProjection_apply]
  refine (denseRange_spanCombination v).induction_on x (p := fun x =>
    Tendsto (fun m : ℕ => prefixProjection v (Finset.range m) x) atTop (𝓝 x)) ?_ ?_
  · exact hequi.isClosed_setOfPred_tendsto continuous_id
  · intro c
    obtain ⟨N, hN⟩ := c.support.exists_nat_subset_range
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with m hm
    exact (prefixProjection_combination v h ha hv c (Finset.range m)
      (hN.trans (Finset.range_mono hm))).symm


def basisOfPrefix (v : ℕ → V) (h : PrefixBoundTwo v)
    {a : ℝ} (ha : 0 < a) (hv : ∀ i, a ≤ ‖v i‖) :
    SchauderBasis ℝ (ClosedSpan v) where
  basis := spanVector v
  coord := prefixCoord v
  ortho := by
    intro i j
    rw [prefixCoord_ortho v h ha hv]
    by_cases hij : i = j <;> simp [hij]
  expansion := prefix_expansion v h ha hv

end SeparableQuotient.Positive.Rows

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Rows
open Set
open scoped Classical BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]



lemma prefixBound_of_half_normers (f : ℕ → StrongDual ℝ X) (D : ℕ → Finset X)
    (hD : ∀ m x, x ∈ D m → ‖x‖ ≤ 1)
    (hnorm : ∀ m (v : StrongDual ℝ X), v ∈ Submodule.span ℝ (f '' (Finset.range m : Set ℕ)) →
      ∃ d ∈ D m, ‖v‖ ≤ 2 * |v d|)
    (hann : ∀ m i, m ≤ i → ∀ d ∈ D m, f i d = 0) : PrefixBoundTwo f := by
  classical
  intro c m
  let v := ∑ i ∈ Finset.range m, c i • f i
  have hv : v ∈ Submodule.span ℝ (f '' (Finset.range m : Set ℕ)) := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  obtain ⟨d, hd, hnormd⟩ := hnorm m v hv
  have heval : (c.sum (fun i a => a • f i)) d = v d := by
    simp only [Finsupp.sum, sum_apply, smul_apply, smul_eq_mul, v]
    calc
      ∑ i ∈ c.support, c i * f i d = ∑ i ∈ c.support ∪ Finset.range m, c i * f i d := by
        apply Finset.sum_subset Finset.subset_union_left
        intro i _ hi
        simp [Finsupp.notMem_support_iff.mp hi]
      _ = ∑ i ∈ Finset.range m, c i * f i d := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro i _ hi
        simp [hann m i (Nat.le_of_not_gt (by simpa using hi)) d hd]
  calc
    ‖v‖ ≤ 2 * |v d| := hnormd
    _ = 2 * |(c.sum (fun i a => a • f i)) d| := by rw [heval]
    _ ≤ 2 * ‖c.sum (fun i a => a • f i)‖ := by
      gcongr
      simpa only [Real.norm_eq_abs, mul_one] using
        (c.sum (fun i a => a • f i)).le_opNorm_of_le (hD m d hd)
end SeparableQuotient.Positive.Rows

end

end

end OAI
