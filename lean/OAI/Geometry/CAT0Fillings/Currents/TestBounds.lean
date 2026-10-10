import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.ProductRule

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
omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedLip_of_lipschitz {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    BoundedLip f := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuous.continuousOn
  exact ⟨⟨K, hf⟩, M, fun x => by simpa [Real.norm_eq_abs] using hM x (mem_univ x)⟩

lemma IntegerRectifiable.coord_bound {k : ℕ} {T : Functional X (k + 1)}
    (hT : IntegerRectifiable T) (hcur : IsMetricCurrent T)
    (hbd : IsMetricCurrent (boundarySucc T))
    {b : X → ℝ} {Kb : ℝ≥0} (hb : LipschitzWith Kb b)
    (π : Fin (k + 1) → X → ℝ) (K : ℝ≥0)
    (hπ : ∀ i, LipschitzWith K (π i)) (i : Fin (k + 1))
    (B F : ℝ≥0) (hB : ∀ x, |b x| ≤ B) (hF : ∀ x, |π i x| ≤ F) :
    |T b π| ≤ (K : ℝ) ^ k *
      ((B : ℝ) * mass (boundarySucc T) + (Kb : ℝ) * mass T) * F := by
  let σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap 0 i
  let ρ : Fin k → X → ℝ := fun j => π (σ j.succ)
  have hadm : Admissible b π := ⟨⟨⟨Kb, hb⟩, B, hB⟩, fun j => ⟨K, hπ j⟩⟩
  have heq : π ∘ σ = Matrix.vecCons (π i) ρ := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [σ]
    · rfl
  rw [← IntegerRectifiable.abs_apply_permute hT hadm σ, heq]
  have h := IntegerRectifiable.head_bound hT hcur hbd hb
    (boundedLip_of_lipschitz (hπ i)) ρ (fun _ => K) (fun j => hπ (σ j.succ)) B F hB hF
  simpa using h

lemma IntegerRectifiable.test_difference_bound {k : ℕ} {T : Functional X (k + 1)}
    (hT : IntegerRectifiable T) (hcur : IsMetricCurrent T)
    (hbd : IsMetricCurrent (boundarySucc T))
    {b : X → ℝ} {Kb : ℝ≥0} (hb : LipschitzWith Kb b)
    (π σ : Fin (k + 1) → X → ℝ) (K : ℝ≥0)
    (hπ : ∀ i, LipschitzWith K (π i)) (hσ : ∀ i, LipschitzWith K (σ i))
    (B ε : ℝ≥0) (hB : ∀ x, |b x| ≤ B) (hε : ∀ i x, |π i x - σ i x| ≤ ε) :
    |T b π - T b σ| ≤ (k + 1 : ℝ) * ((K + K : ℝ≥0) : ℝ) ^ k *
      ((B : ℝ) * mass (boundarySucc T) + (Kb : ℝ) * mass T) * ε := by
  let a : Fin (k + 1) → lipSubmodule (X := X) := fun i => ⟨π i, K, hπ i⟩
  let c : Fin (k + 1) → lipSubmodule (X := X) := fun i => ⟨σ i, K, hσ i⟩
  let ρ : Fin (k + 1) → Fin (k + 1) → X → ℝ := fun i j =>
    if j < i then π j else if i = j then fun x => π j x - σ j x else σ j
  have heq : T b π - T b σ = ∑ i, T b (ρ i) := by
    have h := (hcur.multilinear b ⟨⟨Kb, hb⟩, B, hB⟩).map_sub_map_piecewise a c Finset.univ
    simp only [Finset.mem_univ, forall_const, Finset.piecewise_univ] at h
    change T b π - T b σ = _ at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    change T b _ = T b _
    congr 1
    funext j
    dsimp [ρ]
    split_ifs <;> rfl
  have hρ (i j : Fin (k + 1)) : LipschitzWith (K + K) (ρ i j) := by
    dsimp [ρ]
    split_ifs
    · exact (hπ j).weaken (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ K from bot_le))
    · exact (hπ j).sub (hσ j)
    · exact (hσ j).weaken (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ K from bot_le))
  have hρi (i : Fin (k + 1)) (x : X) : |ρ i i x| ≤ ε := by
    simpa [ρ] using hε i x
  rw [heq]
  calc |∑ i, T b (ρ i)| ≤ ∑ i, |T b (ρ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (k + 1), ((K + K : ℝ≥0) : ℝ) ^ k *
        ((B : ℝ) * mass (boundarySucc T) + (Kb : ℝ) * mass T) * ε :=
      Finset.sum_le_sum fun i _ => IntegerRectifiable.coord_bound hT hcur hbd hb
        (ρ i) (K + K) (hρ i) i B ε hB (hρi i)
    _ = _ := by simp; ring

omit [MeasurableSpace X] [BorelSpace X] in
lemma lipschitz_pointwise_uniform {ι : Type*} {l : Filter ι}
    {f : ι → X → ℝ} {g : X → ℝ} {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hg : ∀ x, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    TendstoUniformly f g l := by
  have heq : Equicontinuous f := Metric.equicontinuous_of_continuity_modulus
    (fun r : ℝ => (K : ℝ) * r) (by simpa using (tendsto_const_nhds (x := (K : ℝ))).mul (show Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0) from tendsto_id)) f
    (fun x y i => (hf i).dist_le_mul x y)
  have ht := (heq.tendsto_uniformFun_iff_pi l g).mpr (tendsto_pi_nhds.mpr hg)
  exact UniformFun.tendsto_iff_tendstoUniformly.mp ht

lemma weak_limit_test_difference_bound
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X (k + 1)} {T : Functional X (k + 1)}
    (hTs : ∀ j, IntegerRectifiable (Ts j))
    (hcur : ∀ j, IsMetricCurrent (Ts j))
    (hbd : ∀ j, IsMetricCurrent (boundarySucc (Ts j)))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Admissible b π → Tendsto (fun j => Ts j b π) l (𝓝 (T b π)))
    {b : X → ℝ} {Kb : ℝ≥0} (hb : LipschitzWith Kb b)
    (π σ : Fin (k + 1) → X → ℝ) (K : ℝ≥0)
    (hπ : ∀ i, LipschitzWith K (π i)) (hσ : ∀ i, LipschitzWith K (σ i))
    (B ε : ℝ≥0) (hB : ∀ x, |b x| ≤ B) (hε : ∀ i x, |π i x - σ i x| ≤ ε) :
    |T b π - T b σ| ≤ (k + 1 : ℝ) * ((K + K : ℝ≥0) : ℝ) ^ k *
      ((B : ℝ) * N + (Kb : ℝ) * M) * ε := by
  have hb' : BoundedLip b := ⟨⟨Kb, hb⟩, B, hB⟩
  apply le_of_tendsto ((hlim b π ⟨hb', fun i => ⟨K, hπ i⟩⟩).sub
    (hlim b σ ⟨hb', fun i => ⟨K, hσ i⟩⟩)).abs
  apply Eventually.of_forall
  intro j
  refine (IntegerRectifiable.test_difference_bound (hTs j) (hcur j) (hbd j) hb
    π σ K hπ hσ B ε hB hε).trans ?_
  apply mul_le_mul_of_nonneg_right _ ε.coe_nonneg
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left (hN j) B.coe_nonneg)
    (mul_le_mul_of_nonneg_left (hM j) Kb.coe_nonneg)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma lipschitz_of_pointwise_limit {ι : Type*} {l : Filter ι} [NeBot l]
    {f : ι → X → ℝ} {g : X → ℝ} {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hg : ∀ x, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    LipschitzWith K g := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  exact le_of_tendsto ((hg x).dist (hg y))
    (Eventually.of_forall fun i => (hf i).dist_le_mul x y)

end Foundations
end CAT0Fillings
end

end OAI
