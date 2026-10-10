import OAI.Analysis.SeparableQuotients.Positive.RowBasis
import OAI.Analysis.SeparableQuotients.Positive.RealAdjoint

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Rows
open Set Filter TopologicalSpace
open scoped Classical BigOperators Topology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
local instance dualSubmoduleNormedGroup (F : Submodule ℝ (StrongDual ℝ X)) :
    NormedAddCommGroup F := Submodule.normedAddCommGroup F
local instance dualSubmoduleNormedSpace (F : Submodule ℝ (StrongDual ℝ X)) :
    NormedSpace ℝ F := Submodule.normedSpace F

def evaluation (G : Submodule ℝ (StrongDual ℝ X)) : X →L[ℝ] StrongDual ℝ G := G.subtypeL.flip

lemma map_eq_of_spanVector {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (v : ℕ → V)
    (φ ψ : ClosedSpan v →L[ℝ] W)
    (he : ∀ i, φ (spanVector v i) = ψ (spanVector v i)) : φ = ψ := by
  apply DFunLike.ext'
  apply (denseRange_spanCombination v).equalizer φ.continuous ψ.continuous
  funext c
  change φ (spanCombination v c) = ψ (spanCombination v c)
  simp only [spanCombination, Finsupp.linearCombination_apply, map_finsuppSum, map_smul, he]

lemma evaluation_eq_prefix_at_normer (f : ℕ → StrongDual ℝ X) (hp : PrefixBoundTwo f)
    {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖) (m : ℕ) (d : X)
    (hann : ∀ i, m ≤ i → f i d = 0) :
    evaluation (ClosedSpan f) d = ∑ i ∈ Finset.range m, (f i d) • prefixCoord f i := by
  apply map_eq_of_spanVector f
  intro j
  have he : evaluation (ClosedSpan f) d (spanVector f j) = f j d := rfl
  rw [he]
  simp only [sum_apply, smul_apply, prefixCoord_ortho f hp ha hf, Pi.single_apply]
  by_cases hj : j < m
  · simp [Finset.mem_range, hj, eq_comm]
  · simp [Finset.mem_range, hj, eq_comm, hann j (Nat.le_of_not_gt hj)]


theorem prefix_evaluation_adjoint_lower (f : ℕ → StrongDual ℝ X)
    {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖)
    (D : ℕ → Finset X) (hD : ∀ m d, d ∈ D m → ‖d‖ ≤ 1)
    (hnorm : ∀ m (v : StrongDual ℝ X), v ∈ Submodule.span ℝ (f '' (Finset.range m : Set ℕ)) →
      ∃ d ∈ D m, ‖v‖ ≤ 2 * |v d|)
    (hann : ∀ m i, m ≤ i → ∀ d ∈ D m, f i d = 0)
    (hrange : ∀ x : X, evaluation (ClosedSpan f) x ∈ ClosedSpan (prefixCoord f)) :
    let T := (evaluation (ClosedSpan f)).codRestrict (ClosedSpan (prefixCoord f)) hrange
    ∀ h : StrongDual ℝ (ClosedSpan (prefixCoord f)), ‖h‖ ≤ 2 * ‖h.comp T‖ := by
  intro T h
  have hp : PrefixBoundTwo f := prefixBound_of_half_normers f D hD hnorm hann
  let vm (m : ℕ) : ClosedSpan f :=
    ∑ i ∈ Finset.range m, h (spanVector (prefixCoord f) i) • spanVector f i
  have hvnorm (m : ℕ) : ‖vm m‖ ≤ 2 * ‖h.comp T‖ := by
    have hvm : (vm m : StrongDual ℝ X) ∈ Submodule.span ℝ (f '' (Finset.range m : Set ℕ)) := by
      simp only [vm, Submodule.coe_sum, Submodule.coe_smul, spanVector]
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    obtain ⟨d, hd, hv⟩ := hnorm m (vm m) hvm
    have hdT : T d = ∑ i ∈ Finset.range m, (f i d) • spanVector (prefixCoord f) i := by
      apply Subtype.ext
      change evaluation (ClosedSpan f) d = _
      simpa only [Submodule.coe_sum, Submodule.coe_smul, spanVector] using
        evaluation_eq_prefix_at_normer f hp ha hf m d (fun i hi => hann m i hi d hd)
    have he : (vm m : StrongDual ℝ X) d = h (T d) := by
      rw [hdT]
      simp only [vm, Submodule.coe_sum, Submodule.coe_smul, spanVector, sum_apply,
        smul_apply, map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hb : |h (T d)| ≤ ‖h.comp T‖ := by
      simpa only [ContinuousLinearMap.comp_apply, Real.norm_eq_abs, mul_one] using
        (h.comp T).le_opNorm_of_le (hD m d hd)
    calc
      ‖vm m‖ ≤ 2 * |(vm m : StrongDual ℝ X) d| := hv
      _ = 2 * |h (T d)| := by rw [he]
      _ ≤ 2 * ‖h.comp T‖ := mul_le_mul_of_nonneg_left hb (by norm_num)
  have hi (m j : ℕ) : prefixCoord f j (vm m) =
      if j < m then h (spanVector (prefixCoord f) j) else 0 := by
    simp only [vm, map_sum, map_smul, prefixCoord_ortho f hp ha hf, Pi.single_apply]
    simp [Finset.mem_range]
  apply h.opNorm_le_bound (by positivity)
  intro z
  refine (denseRange_spanCombination (prefixCoord f)).induction_on z
    (p := fun z => ‖h z‖ ≤ 2 * ‖h.comp T‖ * ‖z‖) ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro c
    obtain ⟨m, hm⟩ := c.support.exists_nat_subset_range
    have he : (spanCombination (prefixCoord f) c : StrongDual ℝ (ClosedSpan f)) (vm m) =
        h (spanCombination (prefixCoord f) c) := by
      rw [spanCombination_coe]
      simp only [spanCombination, Finsupp.linearCombination_apply, Finsupp.sum,
        map_sum, map_smul, sum_apply, smul_apply, hi, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i hi'
      simp only [ite_eq_left (Finset.mem_range.mp (hm hi'))]
    rw [← he]
    have hb := (spanCombination (prefixCoord f) c : StrongDual ℝ (ClosedSpan f)).le_opNorm (vm m)
    exact hb.trans ((mul_le_mul_of_nonneg_left (hvnorm m) (norm_nonneg _)).trans_eq (by
      change ‖spanCombination (prefixCoord f) c‖ * (2 * ‖h.comp T‖) = _
      ring))


lemma closedSpan_separable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : ℕ → V) : SeparableSpace (ClosedSpan v) := by
  exact ((Set.countable_range v).isSeparable.span (R := ℝ)).closure.separableSpace

lemma prefixCoord_linearIndependent (f : ℕ → StrongDual ℝ X) (hp : PrefixBoundTwo f)
    {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖) :
    LinearIndependent ℝ (spanVector (prefixCoord f)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc j hj
  have he := congrArg (fun z : ClosedSpan (prefixCoord f) =>
    (z : StrongDual ℝ (ClosedSpan f)) (spanVector f j)) hc
  have hh (i : ℕ) : (spanVector (prefixCoord f) i : StrongDual ℝ (ClosedSpan f)) =
      prefixCoord f i := rfl
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
    sum_apply, smul_apply, zero_apply, hh, prefixCoord_ortho f hp ha hf,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', ite_eq_left hj] using he


theorem prefix_evaluation_surjective [CompleteSpace X]
    (f : ℕ → StrongDual ℝ X) {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖)
    (D : ℕ → Finset X) (hD : ∀ m d, d ∈ D m → ‖d‖ ≤ 1)
    (hnorm : ∀ m (v : StrongDual ℝ X), v ∈ Submodule.span ℝ (f '' (Finset.range m : Set ℕ)) →
      ∃ d ∈ D m, ‖v‖ ≤ 2 * |v d|)
    (hann : ∀ m i, m ≤ i → ∀ d ∈ D m, f i d = 0)
    (hrange : ∀ x : X, evaluation (ClosedSpan f) x ∈ ClosedSpan (prefixCoord f)) :
    Function.Surjective ((evaluation (ClosedSpan f)).codRestrict (ClosedSpan (prefixCoord f)) hrange) ∧
      SeparableSpace (ClosedSpan (prefixCoord f)) ∧
      ¬ FiniteDimensional ℝ (ClosedSpan (prefixCoord f)) := by
  let T := (evaluation (ClosedSpan f)).codRestrict (ClosedSpan (prefixCoord f)) hrange
  have hlower (h : StrongDual ℝ (ClosedSpan (prefixCoord f))) :
      (1 / 2 : ℝ) * ‖h‖ ≤ ‖h.comp T‖ := by
    have hh := prefix_evaluation_adjoint_lower f ha hf D hD hnorm hann hrange h
    change ‖h‖ ≤ 2 * ‖h.comp T‖ at hh
    linarith
  refine ⟨fun z => ?_, closedSpan_separable _, ?_⟩
  · obtain ⟨x, hx, _⟩ := surjective_of_adjoint_lower T (by norm_num : (0:ℝ) < 1 / 2) hlower z
    exact ⟨x, hx⟩
  · intro hfd
    let : FiniteDimensional ℝ (ClosedSpan (prefixCoord f)) := hfd
    have hi := prefixCoord_linearIndependent f (prefixBound_of_half_normers f D hD hnorm hann) ha hf
    have hh := hi.lt_aleph0_of_finiteDimensional
    simp at hh



lemma mem_coefficient_span_of_summable (f : ℕ → StrongDual ℝ X) (hp : PrefixBoundTwo f)
    {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖)
    (u : StrongDual ℝ (ClosedSpan f))
    (hu : Summable (fun n => |u (spanVector f n)|)) :
    u ∈ ClosedSpan (prefixCoord f) := by
  have hb (n : ℕ) : ‖prefixCoord f n‖ ≤ 4 / a :=
    (prefixCoord f n).opNorm_le_bound (by positivity) (fun z => prefixCoord_bound f hp ha hf z n)
  let t (n : ℕ) : StrongDual ℝ (ClosedSpan f) := u (spanVector f n) • prefixCoord f n
  have ht : Summable t := by
    apply (hu.mul_right (4 / a)).of_norm_bounded
    intro n
    simpa only [t, norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (hb n) (abs_nonneg (u (spanVector f n)))
  have hm : ∑' n, t n ∈ ClosedSpan (prefixCoord f) := by
    apply tsum_mem (Submodule.isClosed_topologicalClosure _)
    intro n
    exact (ClosedSpan (prefixCoord f)).smul_mem _ (spanVector (prefixCoord f) n).property
  have he : (∑' n, t n) = u := by
    apply map_eq_of_spanVector f
    intro j
    have hh := (ContinuousLinearMap.apply ℝ ℝ (spanVector f j)).map_tsum ht
    change (∑' n, t n) (spanVector f j) = ∑' n, t n (spanVector f j) at hh
    rw [hh]
    simp only [t, smul_apply,
      prefixCoord_ortho f hp ha hf, Pi.single_apply, smul_eq_mul]
    simp [eq_comm]
  rwa [he] at hm




theorem eval_range_of_dense_summable
    (E : Submodule ℝ (StrongDual ℝ X)) (hE : IsClosed (E : Set (StrongDual ℝ X)))
    (g : ℕ → E) (hp : PrefixBoundTwo (fun i => (g i : StrongDual ℝ X)))
    {a : ℝ} (ha : 0 < a) (hg : ∀ i, a ≤ ‖(g i : StrongDual ℝ X)‖)
    (A : Set (StrongDual ℝ E))
    (hA : evaluation E '' Metric.closedBall (0 : X) 1 ⊆ closure A)
    (hs : ∀ y ∈ A, Summable (fun n => |y (g n)|)) :
    ∀ x : X, evaluation (ClosedSpan (fun i => (g i : StrongDual ℝ X))) x ∈
      ClosedSpan (prefixCoord (fun i => (g i : StrongDual ℝ X))) := by
  let f : ℕ → StrongDual ℝ X := fun i => g i
  have hGE : ClosedSpan f ≤ E :=
    Submodule.topologicalClosure_minimal _
      (Submodule.span_le.mpr (by rintro z ⟨i, rfl⟩; exact (g i).property)) hE
  let I : ClosedSpan f →L[ℝ] E := (ClosedSpan f).subtypeL.codRestrict E (fun z => hGE z.property)
  let Z := ClosedSpan (prefixCoord f)
  have hclosed : IsClosed {y : StrongDual ℝ E | y.comp I ∈ Z} :=
    (Submodule.isClosed_topologicalClosure _).preimage (continuous_id.clm_comp_const I)
  have hdense : closure A ⊆ {y : StrongDual ℝ E | y.comp I ∈ Z} := by
    apply closure_minimal _ hclosed
    intro y hy
    exact mem_coefficient_span_of_summable f hp ha hg (y.comp I) (hs y hy)
  have hunit (x : X) (hx : ‖x‖ ≤ 1) : evaluation (ClosedSpan f) x ∈ Z := by
    exact hdense (hA ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, rfl⟩)
  intro x
  by_cases hx : x = 0
  · simpa only [hx, map_zero] using Z.zero_mem
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
    simp only [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm, inv_mul_cancel₀ hn.ne']
    exact le_rfl
  have hy := Z.smul_mem ‖x‖ (hunit (‖x‖⁻¹ • x) hu)
  simpa only [map_smul, smul_smul, mul_inv_cancel₀ hn.ne', one_smul] using hy

end SeparableQuotient.Positive.Rows

end

end

end OAI
