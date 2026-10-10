import Mathlib
import OAI.Geometry.IntegralFillings.Currents.TestBounds

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

namespace SharpIntegralFillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
omit [MeasurableSpace X] [BorelSpace X] in
lemma eval_tendsto_of_uniform_modulus {d : ℕ}
    (F : (Fin d → X → ℝ) → ℝ) (π : Fin d → X → ℝ)
    (πs : ℕ → Fin d → X → ℝ)
    (hLip : ∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i))
    (hpt : ∀ i x, Tendsto (fun j => πs j i x) atTop (𝓝 (π i x)))
    (hmod : ∀ K : ℝ≥0, ∃ C : ℝ≥0, ∀ (ρ σ : Fin d → X → ℝ),
      (∀ i, LipschitzWith K (ρ i)) → (∀ i, LipschitzWith K (σ i)) →
      ∀ ε : ℝ≥0, (∀ i x, |ρ i x - σ i x| ≤ ε) → |F ρ - F σ| ≤ C * ε) :
    Tendsto (fun j => F (πs j)) atTop (𝓝 (F π)) := by
  choose Ks hKs using hLip
  let K : ℝ≥0 := ∑ i, Ks i
  have hK (i : Fin d) : Ks i ≤ K :=
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
  have hseq (j : ℕ) (i : Fin d) : LipschitzWith K (πs j i) := (hKs i j).weaken (hK i)
  have hlimit (i : Fin d) : LipschitzWith K (π i) :=
    lipschitz_of_pointwise_limit (fun j => hseq j i) (hpt i)
  obtain ⟨C, hC⟩ := hmod K
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / ((C : ℝ) + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hev (i : Fin d) : ∀ᶠ j in atTop, ∀ x, |πs j i x - π i x| ≤ δ := by
    have hu := lipschitz_pointwise_uniform (fun j => hseq j i) (hpt i)
    filter_upwards [Metric.tendstoUniformly_iff.mp hu δ hδ] with j hj x
    exact le_of_lt (by simpa [Real.dist_eq, abs_sub_comm] using hj x)
  filter_upwards [Filter.eventually_all.mpr hev] with j hj
  rw [Real.dist_eq]
  have h := hC (πs j) π (hseq j) hlimit ⟨δ, hδ.le⟩ hj
  refine h.trans_lt ?_
  change (C : ℝ) * δ < ε
  calc (C : ℝ) * δ < ((C : ℝ) + 1) * δ := by nlinarith
    _ = ε := by dsimp [δ]; exact mul_div_cancel₀ ε (by positivity : (C : ℝ) + 1 ≠ 0)

lemma metricCurrent_of_bounded_weak_limit
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X (k + 1)} {T : Functional X (k + 1)}
    (hTs : ∀ j, IntegerRectifiable (Ts j))
    (hcur : ∀ j, IsMetricCurrent (Ts j))
    (hbd : ∀ j, IsMetricCurrent (boundarySucc (Ts j)))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) :
    IsMetricCurrent T := by
  obtain ⟨μ, hμ, hctrl, _⟩ := exists_controls_of_bounded_weak_limit M hcur hM
    (fun b π _ => hlim b π)
  refine {
    offDomain := ?_
    linearFirst := ?_
    linearCoord := ?_
    sequentialContinuity := ?_
    locality := ?_
    finiteMass := ⟨μ, hμ, hctrl⟩ }
  · intro b π h
    apply tendsto_nhds_unique (hlim b π)
    have heq : (fun j => Ts j b π) = fun _ => 0 :=
      funext fun j => (hcur j).offDomain b π h
    rw [heq]
    exact tendsto_const_nhds
  · intro b₁ b₂ π a c hb₁ hb₂ hπ
    apply tendsto_nhds_unique (hlim (fun x => a * b₁ x + c * b₂ x) π)
    convert ((hlim b₁ π).const_mul a).add ((hlim b₂ π).const_mul c) using 1
    funext j
    exact (hcur j).linearFirst b₁ b₂ π a c hb₁ hb₂ hπ
  · intro b π i f a c hadm hf
    apply tendsto_nhds_unique (hlim b (Function.update π i (fun x => a * π i x + c * f x)))
    convert ((hlim b π).const_mul a).add
      ((hlim b (Function.update π i f)).const_mul c) using 1
    funext j
    exact (hcur j).linearCoord b π i f a c hadm hf
  · intro b π πs hb hLip hpt
    obtain ⟨Kb, hKb⟩ := hb.1
    obtain ⟨B₀, hB₀⟩ := hb.2
    let B : ℝ≥0 := ⟨max B₀ 0, le_max_right _ _⟩
    have hB (x : X) : |b x| ≤ B := (hB₀ x).trans (le_max_left _ _)
    apply eval_tendsto_of_uniform_modulus (T b) π πs hLip hpt
    intro K
    let C : ℝ≥0 := (k + 1) * (K + K) ^ k * (B * N + Kb * M)
    refine ⟨C, ?_⟩
    intro ρ σ hρ hσ ε hε
    have h := weak_limit_test_difference_bound hTs hcur hbd M N hM hN
      (fun b π _ => hlim b π) hKb ρ σ K hρ hσ B ε hB hε
    simpa [C] using h
  · intro b π hadm hloc
    apply tendsto_nhds_unique (hlim b π)
    have heq : (fun j => Ts j b π) = fun _ => 0 :=
      funext fun j => (hcur j).locality b π hadm hloc
    rw [heq]
    exact tendsto_const_nhds

omit [BorelSpace X] [CompactSpace X] in
lemma boundarySucc_boundarySucc {k : ℕ} {T : Functional X (k + 1 + 1)}
    (hT : IsMetricCurrent T) : boundarySucc (boundarySucc T) = fun _ _ => 0 := by
  funext b π
  by_cases h : Admissible b π
  · rw [boundarySucc, ite_eq_left h]
    have hadm : Admissible (fun _ : X => (1 : ℝ)) (Matrix.vecCons b π) :=
      admissible_vecCons (BoundedLip.const 1) h.1.1 h.2
    rw [boundarySucc, ite_eq_left hadm]
    apply hT.eq_zero_of_const_coord (admissible_vecCons (BoundedLip.const 1)
      ⟨0, LipschitzWith.const 1⟩ hadm.2) 0 1
    intro x
    rfl
  · rw [boundarySucc, ite_eq_right h]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma boundarySucc_weak_limit {ι : Type*} {l : Filter ι} {k : ℕ}
    {Ts : ι → Functional X (k + 1)} {T : Functional X (k + 1)}
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) :
    ∀ b π, Tendsto (fun j => boundarySucc (Ts j) b π) l (𝓝 (boundarySucc T b π)) := by
  intro b π
  by_cases h : Admissible b π
  · simpa only [boundarySucc, ite_eq_left h] using hlim (fun _ => 1) (Matrix.vecCons b π)
  · simp only [boundarySucc, ite_eq_right h]
    exact tendsto_const_nhds

lemma normal_of_bounded_integral_weak_limit
    {ι : Type*} {l : Filter ι} [NeBot l] {k : ℕ}
    {Ts : ι → Functional X (k + 1 + 1)} {T : Functional X (k + 1 + 1)}
    (hTs : ∀ j, IsIntegral (k + 1 + 1) (Ts j))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) l (𝓝 (T b π))) :
    IsMetricCurrent T ∧ IsMetricCurrent (boundarySucc T) := by
  have hcur (j : ι) := (hTs j).1
  have hint (j : ι) := (hTs j).2.1
  have hbd (j : ι) := (hTs j).2.2.1
  have hbdi (j : ι) := (hTs j).2.2.2
  refine ⟨metricCurrent_of_bounded_weak_limit hint hcur hbd M N hM hN hlim, ?_⟩
  apply metricCurrent_of_bounded_weak_limit hbdi hbd (fun j => ?_) N 0 hN
    (fun j => ?_) (boundarySucc_weak_limit hlim)
  · rw [boundarySucc_boundarySucc (hcur j)]
    exact isMetricCurrent_zero k
  · rw [boundarySucc_boundarySucc (hcur j), mass_zero]
    rfl

end Foundations
end SharpIntegralFillings
end

end OAI
