import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.WeakClosure

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
lemma exists_weak_cluster_of_mass_bound
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X k} (hcur : ∀ j, IsMetricCurrent (Ts j))
    (M : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M) :
    ∃ (l' : Filter ι), NeBot l' ∧ l' ≤ l ∧
      ∃ T : Functional X k, ∀ b π, Tendsto (fun j => Ts j b π) l' (𝓝 (T b π)) := by
  have hbound (b : X → ℝ) (π : Fin k → X → ℝ) :
      ∃ R : ℝ, 0 ≤ R ∧ ∀ j, |Ts j b π| ≤ R := by
    by_cases h : Admissible b π
    · choose Ks hKs using h.2
      obtain ⟨B, hB⟩ := h.1.2
      refine ⟨((∏ i, (Ks i : ℝ)) * max B 0) * M, by positivity, ?_⟩
      intro j
      refine ((hcur j).mass_bound_uniform h.1 Ks hKs
        (fun x => (hB x).trans (le_max_left B 0))).trans ?_
      exact mul_le_mul_of_nonneg_left (hM j) (by positivity)
    · exact ⟨0, le_rfl, fun j => by rw [(hcur j).offDomain b π h, abs_zero]⟩
  choose R _ hR using hbound
  let C : Set (Functional X k) := {U | ∀ b π, U b π ∈ Icc (-R b π) (R b π)}
  have hC : IsCompact C :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_Icc
  have hTsC (j : ι) : Ts j ∈ C := fun b π => abs_le.mp (hR b π j)
  obtain ⟨T, _, hcluster⟩ := hC.exists_mapClusterPt_of_frequently (l := l)
    (Eventually.of_forall hTsC).frequently
  let l' := comap Ts (𝓝 T) ⊓ l
  have hl' : NeBot l' := neBot_inf_comap_iff_map'.mpr hcluster
  have hT : Tendsto Ts l' (𝓝 T) := tendsto_iff_comap.mpr inf_le_left
  exact ⟨l', hl', inf_le_right, T, fun b π =>
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hT b) π⟩

lemma exists_normal_weak_cluster_of_integral_mass_bound
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X (k + 1 + 1)}
    (hTs : ∀ j, IsIntegral (k + 1 + 1) (Ts j))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N) :
    ∃ (l' : Filter ι), NeBot l' ∧ l' ≤ l ∧
      ∃ T : Functional X (k + 1 + 1), IsMetricCurrent T ∧
        IsMetricCurrent (boundarySucc T) ∧ mass T ≤ M ∧
        mass (boundarySucc T) ≤ N ∧
        ∀ b π, Tendsto (fun j => Ts j b π) l' (𝓝 (T b π)) := by
  obtain ⟨l', hl', hle, T, hlim⟩ := exists_weak_cluster_of_mass_bound
    (l := l) (fun j => (hTs j).1) M hM
  let := hl'
  obtain ⟨hT, hbd⟩ := normal_of_bounded_integral_weak_limit hTs M N hM hN hlim
  refine ⟨l', hl', hle, T, hT, hbd, ?_, ?_, hlim⟩
  · exact mass_le_of_bounded_weak_limit M (fun j => (hTs j).1) hM (fun b π _ => hlim b π)
  · exact mass_le_of_bounded_weak_limit N (fun j => (hTs j).2.2.1) hN
      (fun b π _ => boundarySucc_weak_limit hlim b π)

lemma IsMetricCurrent.first_difference_bound {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b c : X → ℝ} (hb : BoundedLip b) (hc : BoundedLip c)
    (π : Fin k → X → ℝ) (K : ℝ≥0) (hπ : ∀ i, LipschitzWith K (π i))
    (ε : ℝ≥0) (hε : ∀ x, |b x - c x| ≤ ε) :
    |T b π - T c π| ≤ (K : ℝ) ^ k * ε * mass T := by
  have hsub : BoundedLip (fun x => b x - c x) := by
    simpa [sub_eq_add_neg] using hb.add (hc.const_mul (-1))
  have heq : T (fun x => b x - c x) π = T b π - T c π := by
    simpa [sub_eq_add_neg] using hT.linearFirst b c π 1 (-1) hb hc (fun i => ⟨K, hπ i⟩)
  rw [← heq]
  simpa using hT.mass_bound_uniform hsub (fun _ => K) hπ hε

abbrev TestClass (d : ℕ) (K : ℕ) :=
  {p : C(X, ℝ) × (Fin d → C(X, ℝ)) //
    LipschitzWith K p.1 ∧ ‖p.1‖ ≤ K ∧ ∀ i, LipschitzWith K (p.2 i)}

instance testClass_nonempty (d K : ℕ) : Nonempty (TestClass (X := X) d K) := by
  refine ⟨⟨(0, fun _ => 0), ?_⟩⟩
  refine ⟨(LipschitzWith.const 0).weaken (by positivity), ?_, ?_⟩
  · simp
  · intro i
    exact (LipschitzWith.const 0).weaken (by positivity)

noncomputable def TestClass.eval {d K : ℕ} (T : Functional X d)
    (p : TestClass (X := X) d K) : ℝ := T p.val.1 (fun i => p.val.2 i)

omit [MeasurableSpace X] [BorelSpace X] in
lemma TestClass.boundedLip {d K : ℕ} (p : TestClass (X := X) d K) :
    BoundedLip (p.val.1 : X → ℝ) :=
  ⟨⟨K, p.property.1⟩, K, fun x => (p.val.1.norm_coe_le_norm x).trans p.property.2.1⟩

lemma IntegerRectifiable.testClass_lipschitz {k : ℕ} {T : Functional X (k+1)}
    (hT : IntegerRectifiable T) (hcur : IsMetricCurrent T)
    (hbd : IsMetricCurrent (boundarySucc T))
    (M N : ℝ≥0) (hM : mass T ≤ M) (hN : mass (boundarySucc T) ≤ N) (K : ℕ) :
    LipschitzWith ((K : ℝ≥0) ^ (k+1) * M +
      (k+1) * ((K : ℝ≥0) + K) ^ k * (K * N + K * M))
      (TestClass.eval (K := K) T) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro p q
  let ε : ℝ≥0 := nndist p q
  have hb : ∀ x, |p.val.1 x - q.val.1 x| ≤ ε := by
    intro x
    exact (ContinuousMap.dist_apply_le_dist x).trans
      (le_max_left (dist p.val.1 q.val.1) (dist p.val.2 q.val.2))
  have hπ : ∀ i x, |p.val.2 i x - q.val.2 i x| ≤ ε := by
    intro i x
    exact ((ContinuousMap.dist_apply_le_dist x).trans
      (dist_le_pi_dist p.val.2 q.val.2 i)).trans (le_max_right _ _)
  have hB (x : X) : |q.val.1 x| ≤ (K : ℝ≥0) :=
    (q.val.1.norm_coe_le_norm x).trans q.property.2.1
  have hfirst := IsMetricCurrent.first_difference_bound hcur p.boundedLip q.boundedLip
    (fun i => p.val.2 i) K p.property.2.2 ε hb
  have hcoord := IntegerRectifiable.test_difference_bound hT hcur hbd q.property.1
    (fun i => p.val.2 i) (fun i => q.val.2 i) K p.property.2.2 q.property.2.2 K ε hB hπ
  have hfirst' : |T p.val.1 (fun i => p.val.2 i) - T q.val.1 (fun i => p.val.2 i)| ≤
      (K : ℝ) ^ (k+1) * M * ε := by
    refine hfirst.trans ?_
    calc (K : ℝ) ^ (k+1) * ε * mass T ≤ (K : ℝ) ^ (k+1) * ε * M :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by ring
  have hcoord' : |T q.val.1 (fun i => p.val.2 i) - T q.val.1 (fun i => q.val.2 i)| ≤
      (k+1 : ℝ) * (K + K : ℝ) ^ k * ((K : ℝ) * N + K * M) * ε := by
    refine hcoord.trans ?_
    apply mul_le_mul_of_nonneg_right _ ε.coe_nonneg
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left hN (by positivity))
      (mul_le_mul_of_nonneg_left hM (by positivity))
  calc dist (TestClass.eval T p) (TestClass.eval T q) ≤
      |T p.val.1 (fun i => p.val.2 i) - T q.val.1 (fun i => p.val.2 i)| +
      |T q.val.1 (fun i => p.val.2 i) - T q.val.1 (fun i => q.val.2 i)| :=
        dist_triangle _ (T q.val.1 (fun i => p.val.2 i)) _
    _ ≤ _ := add_le_add hfirst' hcoord'
    _ = _ := by dsimp [ε]; push_cast; ring

omit [MeasurableSpace X] [BorelSpace X] in

lemma admissible_mem_testClass {d : ℕ} {b : X → ℝ} {π : Fin d → X → ℝ}
    (h : Admissible b π) :
    ∃ (K : ℕ) (p : TestClass (X := X) d K),
      (p.val.1 : X → ℝ) = b ∧ (fun i => (p.val.2 i : X → ℝ)) = π := by
  obtain ⟨⟨Kb, hb⟩, B, hB⟩ := h.1
  choose Ks hKs using h.2
  let Bn : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  let L : ℝ≥0 := max Kb (max Bn (Finset.univ.sup Ks))
  obtain ⟨K, hK⟩ := exists_nat_gt L
  have hbK : Kb ≤ (K : ℝ≥0) := (le_max_left _ _).trans hK.le
  have hBK : Bn ≤ (K : ℝ≥0) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hK.le
  have hπK (i : Fin d) : Ks i ≤ (K : ℝ≥0) :=
    ((Finset.le_sup (Finset.mem_univ i)).trans
      ((le_max_right _ _).trans (le_max_right _ _))).trans hK.le
  let p : C(X, ℝ) × (Fin d → C(X, ℝ)) :=
    (⟨b, hb.continuous⟩, fun i => ⟨π i, (hKs i).continuous⟩)
  refine ⟨K, ⟨p, ⟨hb.weaken hbK, ?_, fun i => (hKs i).weaken (hπK i)⟩⟩, rfl, rfl⟩
  apply (p.1.norm_le (by positivity)).mpr
  intro x
  exact (hB x).trans ((le_max_left B 0).trans hBK)

end Foundations

end CAT0Fillings
end

end OAI
