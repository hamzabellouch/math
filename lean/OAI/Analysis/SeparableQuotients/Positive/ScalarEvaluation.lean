import OAI.Analysis.SeparableQuotients.Positive.ScalarBasis
import OAI.Analysis.SeparableQuotients.Positive.ScalarAdjoint

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields.Scalar
open Set Filter TopologicalSpace
open scoped Classical BigOperators Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
local instance dualSubmoduleNormedGroup (F : Submodule 𝕜 (StrongDual 𝕜 X)) :
    NormedAddCommGroup F := Submodule.normedAddCommGroup F
local instance dualSubmoduleNormedSpace (F : Submodule 𝕜 (StrongDual 𝕜 X)) :
    NormedSpace 𝕜 F := Submodule.normedSpace F

def evaluation (G : Submodule 𝕜 (StrongDual 𝕜 X)) : X →L[𝕜] StrongDual 𝕜 G := G.subtypeL.flip

lemma map_eq_of_spanVector {V W : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] (v : ℕ → V)
    (φ ψ : ClosedSpan 𝕜 v →L[𝕜] W)
    (he : ∀ i, φ (spanVector 𝕜 v i) = ψ (spanVector 𝕜 v i)) : φ = ψ := by
  apply DFunLike.ext'
  apply (denseRange_spanCombination 𝕜 v).equalizer φ.continuous ψ.continuous
  funext c
  change φ (spanCombination 𝕜 v c) = ψ (spanCombination 𝕜 v c)
  simp only [spanCombination, Finsupp.linearCombination_apply, map_finsuppSum, map_smul, he]

lemma evaluation_eq_prefix_at_normer (f : ℕ → StrongDual 𝕜 X) (hp : PrefixBoundTwo 𝕜 f)
    {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖) (m : ℕ) (d : X)
    (hann : ∀ i, m ≤ i → f i d = 0) :
    evaluation (ClosedSpan 𝕜 f) d = ∑ i ∈ Finset.range m, (f i d) • prefixCoord 𝕜 f i := by
  apply map_eq_of_spanVector f
  intro j
  have he : evaluation (ClosedSpan 𝕜 f) d (spanVector 𝕜 f j) = f j d := rfl
  rw [he]
  simp only [sum_apply, smul_apply, prefixCoord_ortho 𝕜 f hp ha hf, Pi.single_apply]
  by_cases hj : j < m
  · simp [Finset.mem_range, hj, eq_comm]
  · simp [Finset.mem_range, hj, eq_comm, hann j (Nat.le_of_not_gt hj)]

def adjointPrefixVector (f : ℕ → StrongDual 𝕜 X)
    (h : StrongDual 𝕜 (ClosedSpan 𝕜 (prefixCoord 𝕜 f))) (m : ℕ) : ClosedSpan 𝕜 f :=
  ∑ i ∈ Finset.range m, h (spanVector 𝕜 (prefixCoord 𝕜 f) i) • spanVector 𝕜 f i

lemma adjointPrefixVector_bound (f : ℕ → StrongDual 𝕜 X)
    {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖)
    (D : ℕ → Finset X) (hD : ∀ m d, d ∈ D m → ‖d‖ ≤ 1)
    (hnorm : ∀ m (v : StrongDual 𝕜 X), v ∈ Submodule.span 𝕜 (f '' (Finset.range m : Set ℕ)) →
      ∃ d ∈ D m, ‖v‖ ≤ 2 * ‖v d‖)
    (hann : ∀ m i, m ≤ i → ∀ d ∈ D m, f i d = 0)
    (hrange : ∀ x : X, evaluation (ClosedSpan 𝕜 f) x ∈ ClosedSpan 𝕜 (prefixCoord 𝕜 f)) :
    let T := (evaluation (ClosedSpan 𝕜 f)).codRestrict (ClosedSpan 𝕜 (prefixCoord 𝕜 f)) hrange
    ∀ (h : StrongDual 𝕜 (ClosedSpan 𝕜 (prefixCoord 𝕜 f))) (m : ℕ),
      ‖adjointPrefixVector f h m‖ ≤ 2 * ‖h.comp T‖ := by
  intro T h
  have hp : PrefixBoundTwo 𝕜 f := prefixBound_of_half_normers 𝕜 f D hD hnorm hann
  intro m
  have hvm : (adjointPrefixVector f h m : StrongDual 𝕜 X) ∈ Submodule.span 𝕜 (f '' (Finset.range m : Set ℕ)) := by
    simp only [adjointPrefixVector, Submodule.coe_sum, Submodule.coe_smul, spanVector]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  obtain ⟨d, hd, hv⟩ := hnorm m (adjointPrefixVector f h m) hvm
  have hdT : T d = ∑ i ∈ Finset.range m, (f i d) • spanVector 𝕜 (prefixCoord 𝕜 f) i := by
    apply Subtype.ext
    change evaluation (ClosedSpan 𝕜 f) d = _
    simpa only [Submodule.coe_sum, Submodule.coe_smul, spanVector] using
      evaluation_eq_prefix_at_normer f hp ha hf m d (fun i hi => hann m i hi d hd)
  have he : (adjointPrefixVector f h m : StrongDual 𝕜 X) d = h (T d) := by
    rw [hdT]
    simp only [adjointPrefixVector, Submodule.coe_sum, Submodule.coe_smul, spanVector, sum_apply,
      smul_apply, map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hb : ‖h (T d)‖ ≤ ‖h.comp T‖ := by
    simpa only [ContinuousLinearMap.comp_apply, mul_one] using
      (h.comp T).le_opNorm_of_le (hD m d hd)
  calc
    ‖adjointPrefixVector f h m‖ ≤ 2 * ‖(adjointPrefixVector f h m : StrongDual 𝕜 X) d‖ := hv
    _ = 2 * ‖h (T d)‖ := by rw [he]
    _ ≤ 2 * ‖h.comp T‖ := mul_le_mul_of_nonneg_left hb (by norm_num)

lemma prefixCoord_adjointPrefixVector (f : ℕ → StrongDual 𝕜 X) (hp : PrefixBoundTwo 𝕜 f)
    {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖)
    (h : StrongDual 𝕜 (ClosedSpan 𝕜 (prefixCoord 𝕜 f))) (m j : ℕ) :
    prefixCoord 𝕜 f j (adjointPrefixVector f h m) =
      if j < m then h (spanVector 𝕜 (prefixCoord 𝕜 f) j) else 0 := by
  simp only [adjointPrefixVector, map_sum, map_smul, prefixCoord_ortho 𝕜 f hp ha hf, Pi.single_apply]
  simp [Finset.mem_range]

lemma coefficient_pairing_adjointPrefixVector (f : ℕ → StrongDual 𝕜 X)
    (hp : PrefixBoundTwo 𝕜 f) {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖)
    (h : StrongDual 𝕜 (ClosedSpan 𝕜 (prefixCoord 𝕜 f)))
    (c : ℕ →₀ 𝕜) (m : ℕ) (hm : c.support ⊆ Finset.range m) :
    (spanCombination 𝕜 (prefixCoord 𝕜 f) c : StrongDual 𝕜 (ClosedSpan 𝕜 f))
      (adjointPrefixVector f h m) = h (spanCombination 𝕜 (prefixCoord 𝕜 f) c) := by
  rw [spanCombination_coe]
  simp only [spanCombination, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, sum_apply, smul_apply,
    prefixCoord_adjointPrefixVector f hp ha hf, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ite_eq_left (Finset.mem_range.mp (hm hi))]


theorem prefix_evaluation_adjoint_lower (f : ℕ → StrongDual 𝕜 X)
    {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖)
    (D : ℕ → Finset X) (hD : ∀ m d, d ∈ D m → ‖d‖ ≤ 1)
    (hnorm : ∀ m (v : StrongDual 𝕜 X), v ∈ Submodule.span 𝕜 (f '' (Finset.range m : Set ℕ)) →
      ∃ d ∈ D m, ‖v‖ ≤ 2 * ‖v d‖)
    (hann : ∀ m i, m ≤ i → ∀ d ∈ D m, f i d = 0)
    (hrange : ∀ x : X, evaluation (ClosedSpan 𝕜 f) x ∈ ClosedSpan 𝕜 (prefixCoord 𝕜 f)) :
    let T := (evaluation (ClosedSpan 𝕜 f)).codRestrict (ClosedSpan 𝕜 (prefixCoord 𝕜 f)) hrange
    ∀ h : StrongDual 𝕜 (ClosedSpan 𝕜 (prefixCoord 𝕜 f)), ‖h‖ ≤ 2 * ‖h.comp T‖ := by
  intro T h
  have hp : PrefixBoundTwo 𝕜 f := prefixBound_of_half_normers 𝕜 f D hD hnorm hann
  apply h.opNorm_le_bound (by positivity)
  intro z
  refine (denseRange_spanCombination 𝕜 (prefixCoord 𝕜 f)).induction_on z
    (p := fun z => ‖h z‖ ≤ 2 * ‖h.comp T‖ * ‖z‖) ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro c
    obtain ⟨m, hm⟩ := c.support.exists_nat_subset_range
    have he := coefficient_pairing_adjointPrefixVector f hp ha hf h c m hm
    rw [← he]
    have hb := (spanCombination 𝕜 (prefixCoord 𝕜 f) c : StrongDual 𝕜 (ClosedSpan 𝕜 f)).le_opNorm (adjointPrefixVector f h m)
    exact hb.trans ((mul_le_mul_of_nonneg_left (adjointPrefixVector_bound f ha hf D hD hnorm hann hrange h m) (norm_nonneg _)).trans_eq (by
      change ‖spanCombination 𝕜 (prefixCoord 𝕜 f) c‖ * (2 * ‖h.comp T‖) = _
      ring))


lemma closedSpan_separable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (v : ℕ → V) : SeparableSpace (ClosedSpan 𝕜 v) := by
  exact ((Set.countable_range v).isSeparable.span (R := 𝕜)).closure.separableSpace

lemma prefixCoord_linearIndependent (f : ℕ → StrongDual 𝕜 X) (hp : PrefixBoundTwo 𝕜 f)
    {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖) :
    LinearIndependent 𝕜 (spanVector 𝕜 (prefixCoord 𝕜 f)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc j hj
  have he := congrArg (fun z : ClosedSpan 𝕜 (prefixCoord 𝕜 f) =>
    (z : StrongDual 𝕜 (ClosedSpan 𝕜 f)) (spanVector 𝕜 f j)) hc
  have hh (i : ℕ) : (spanVector 𝕜 (prefixCoord 𝕜 f) i : StrongDual 𝕜 (ClosedSpan 𝕜 f)) =
      prefixCoord 𝕜 f i := rfl
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
    sum_apply, smul_apply, zero_apply, hh, prefixCoord_ortho 𝕜 f hp ha hf,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', ite_eq_left hj] using he


theorem prefix_evaluation_surjective [CompleteSpace X]
    (f : ℕ → StrongDual 𝕜 X) {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖)
    (D : ℕ → Finset X) (hD : ∀ m d, d ∈ D m → ‖d‖ ≤ 1)
    (hnorm : ∀ m (v : StrongDual 𝕜 X), v ∈ Submodule.span 𝕜 (f '' (Finset.range m : Set ℕ)) →
      ∃ d ∈ D m, ‖v‖ ≤ 2 * ‖v d‖)
    (hann : ∀ m i, m ≤ i → ∀ d ∈ D m, f i d = 0)
    (hrange : ∀ x : X, evaluation (ClosedSpan 𝕜 f) x ∈ ClosedSpan 𝕜 (prefixCoord 𝕜 f)) :
    Function.Surjective ((evaluation (ClosedSpan 𝕜 f)).codRestrict (ClosedSpan 𝕜 (prefixCoord 𝕜 f)) hrange) ∧
      SeparableSpace (ClosedSpan 𝕜 (prefixCoord 𝕜 f)) ∧
      ¬ FiniteDimensional 𝕜 (ClosedSpan 𝕜 (prefixCoord 𝕜 f)) := by
  let T := (evaluation (ClosedSpan 𝕜 f)).codRestrict (ClosedSpan 𝕜 (prefixCoord 𝕜 f)) hrange
  have hlower (h : StrongDual 𝕜 (ClosedSpan 𝕜 (prefixCoord 𝕜 f))) :
      (1 / 2 : ℝ) * ‖h‖ ≤ ‖h.comp T‖ := by
    have hh := prefix_evaluation_adjoint_lower f ha hf D hD hnorm hann hrange h
    change ‖h‖ ≤ 2 * ‖h.comp T‖ at hh
    linarith
  refine ⟨fun z => ?_, closedSpan_separable _, ?_⟩
  · obtain ⟨x, hx, _⟩ := surjective_of_adjoint_lower 𝕜 T (by norm_num : (0:ℝ) < 1 / 2) hlower z
    exact ⟨x, hx⟩
  · intro hfd
    let := hfd
    have hi := prefixCoord_linearIndependent f (prefixBound_of_half_normers 𝕜 f D hD hnorm hann) ha hf
    have hh := hi.lt_aleph0_of_finiteDimensional
    simp at hh



lemma mem_coefficient_span_of_summable (f : ℕ → StrongDual 𝕜 X) (hp : PrefixBoundTwo 𝕜 f)
    {a : ℝ} (ha : 0 < a) (hf : ∀ i, a ≤ ‖f i‖)
    (u : StrongDual 𝕜 (ClosedSpan 𝕜 f))
    (hu : Summable (fun n => ‖u (spanVector 𝕜 f n)‖)) :
    u ∈ ClosedSpan 𝕜 (prefixCoord 𝕜 f) := by
  have hb (n : ℕ) : ‖prefixCoord 𝕜 f n‖ ≤ 4 / a :=
    (prefixCoord 𝕜 f n).opNorm_le_bound (by positivity) (fun z => prefixCoord_bound 𝕜 f hp ha hf z n)
  let t (n : ℕ) : StrongDual 𝕜 (ClosedSpan 𝕜 f) := u (spanVector 𝕜 f n) • prefixCoord 𝕜 f n
  have ht : Summable t := by
    apply (hu.mul_right (4 / a)).of_norm_bounded
    intro n
    simpa only [t, norm_smul] using
      mul_le_mul_of_nonneg_left (hb n) (norm_nonneg (u (spanVector 𝕜 f n)))
  have hm : ∑' n, t n ∈ ClosedSpan 𝕜 (prefixCoord 𝕜 f) := by
    apply tsum_mem (Submodule.isClosed_topologicalClosure _)
    intro n
    exact (ClosedSpan 𝕜 (prefixCoord 𝕜 f)).smul_mem _ (spanVector 𝕜 (prefixCoord 𝕜 f) n).property
  have he : (∑' n, t n) = u := by
    apply map_eq_of_spanVector f
    intro j
    have hh := (ContinuousLinearMap.apply 𝕜 𝕜 (spanVector 𝕜 f j)).map_tsum ht
    change (∑' n, t n) (spanVector 𝕜 f j) = ∑' n, t n (spanVector 𝕜 f j) at hh
    rw [hh]
    simp only [t, smul_apply,
      prefixCoord_ortho 𝕜 f hp ha hf, Pi.single_apply, smul_eq_mul]
    simp [eq_comm]
  rwa [he] at hm




theorem eval_range_of_dense_summable
    (E : Submodule 𝕜 (StrongDual 𝕜 X)) (hE : IsClosed (E : Set (StrongDual 𝕜 X)))
    (g : ℕ → E) (hp : PrefixBoundTwo 𝕜 (fun i => (g i : StrongDual 𝕜 X)))
    {a : ℝ} (ha : 0 < a) (hg : ∀ i, a ≤ ‖(g i : StrongDual 𝕜 X)‖)
    (A : Set (StrongDual 𝕜 E))
    (hA : evaluation E '' Metric.closedBall (0 : X) 1 ⊆ closure A)
    (hs : ∀ y ∈ A, Summable (fun n => ‖y (g n)‖)) :
    ∀ x : X, evaluation (ClosedSpan 𝕜 (fun i => (g i : StrongDual 𝕜 X))) x ∈
      ClosedSpan 𝕜 (prefixCoord 𝕜 (fun i => (g i : StrongDual 𝕜 X))) := by
  let f : ℕ → StrongDual 𝕜 X := fun i => g i
  have hGE : ClosedSpan 𝕜 f ≤ E :=
    Submodule.topologicalClosure_minimal _
      (Submodule.span_le.mpr (by rintro z ⟨i, rfl⟩; exact (g i).property)) hE
  let I : ClosedSpan 𝕜 f →L[𝕜] E := (ClosedSpan 𝕜 f).subtypeL.codRestrict E (fun z => hGE z.property)
  let Z := ClosedSpan 𝕜 (prefixCoord 𝕜 f)
  have hclosed : IsClosed {y : StrongDual 𝕜 E | y.comp I ∈ Z} :=
    (Submodule.isClosed_topologicalClosure _).preimage (continuous_id.clm_comp_const I)
  have hdense : closure A ⊆ {y : StrongDual 𝕜 E | y.comp I ∈ Z} := by
    apply closure_minimal _ hclosed
    intro y hy
    exact mem_coefficient_span_of_summable f hp ha hg (y.comp I) (hs y hy)
  have hunit (x : X) (hx : ‖x‖ ≤ 1) : evaluation (ClosedSpan 𝕜 f) x ∈ Z := by
    exact hdense (hA ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, rfl⟩)
  intro x
  by_cases hx : x = 0
  · simpa only [hx, map_zero] using Z.zero_mem
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖(‖x‖ : 𝕜)⁻¹ • x‖ ≤ 1 := by
    simp only [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ hn.ne']
    exact le_rfl
  have hy := Z.smul_mem (‖x‖ : 𝕜) (hunit ((‖x‖ : 𝕜)⁻¹ • x) hu)
  simpa only [map_smul, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne' : (‖x‖ : 𝕜) ≠ 0), one_smul] using hy

end SeparableQuotient.Positive.Fields.Scalar

end

end

end OAI
