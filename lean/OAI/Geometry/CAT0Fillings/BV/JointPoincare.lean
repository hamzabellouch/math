import Mathlib
import OAI.Geometry.CAT0Fillings.Calculus.Smoothing
import OAI.Geometry.CAT0Fillings.BV.WeakCalculus
import OAI.Geometry.CAT0Fillings.BV.Oscillation

namespace OAI

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution

namespace CAT0Fillings.JointBV

lemma scalar_convolution_comm {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddLeftInvariant]
    [μ.IsNegInvariant] (f g : E → ℝ) :
    (f ⋆[lsmul ℝ ℝ, μ] g) = (g ⋆[lsmul ℝ ℝ, μ] f) := by
  have he : (lsmul ℝ ℝ).flip = lsmul ℝ ℝ := by ext; simp
  simpa only [he] using (convolution_flip (L := lsmul ℝ ℝ) (f := g) (g := f) (μ := μ))

noncomputable def shrinkingBump {E : Type*} [NormedAddCommGroup E] (j : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / ((j:ℝ)+1)
  rOut := 2 * (1 / ((j:ℝ)+1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < 1/((j:ℝ)+1) := by positivity
    linarith

lemma shrinkingBump_tendsto {E : Type*} [NormedAddCommGroup E] :
    Tendsto (fun j => (shrinkingBump (E := E) j).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump,mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

theorem ball_poincare_of_directional_variation {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin k))} [μ.IsAddHaarMeasure]
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ν]
    (hf : LocallyIntegrable f μ)
    (hv : ∀ i, DirectionalVariation f (EuclideanSpace.basisFun (Fin k) ℝ i) μ ν)
    (a : EuclideanSpace ℝ (Fin k)) {r : ℝ} (hr : 0 < r) :
    (∫ z in closedBall a r, |f z - (⨍ w in closedBall a r, f w ∂μ)| ∂μ) ≤
      (4*(2:ℝ)^k*k) * r * ν.real (closedBall a (2*r)) := by
  let η (j : ℕ) := shrinkingBump (E := EuclideanSpace ℝ (Fin k)) j
  let F (j : ℕ) := f ⋆[lsmul ℝ ℝ, μ] (η j).normed μ
  let F' (j : ℕ) := f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), μ]
    fderiv ℝ ((η j).normed μ)
  have hF (j : ℕ) (x : EuclideanSpace ℝ (Fin k)) : HasFDerivAt (F j) (F' j x) x :=
    (η j).hasCompactSupport_normed.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf
      (η j).contDiff_normed x
  have hF' (j : ℕ) : Continuous (F' j) :=
    ((η j).hasCompactSupport_normed.fderiv ℝ).continuous_convolution_right
      ((lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k))) hf
      (((η j).contDiff_normed (n := (⊤ : ℕ∞))).continuous_fderiv (by simp))
  have hl : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x)) := by
    have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := η) shrinkingBump_tendsto (K := 2) (Eventually.of_forall (fun j => le_rfl)) hf
    filter_upwards [hh] with x hx
    simpa only [F,scalar_convolution_comm f] using hx
  have hg : ∀ᶠ j in atTop, (∫ z in closedBall a r, ‖F' j z‖ ∂μ) ≤
      k * ν.real (closedBall a (2*r)) := by
    have hh : ∀ᶠ j in atTop, (η j).rOut < r := (shrinkingBump_tendsto.eventually (gt_mem_nhds hr))
    filter_upwards [hh] with j hj
    exact (mollified_gradient_integral_bound hf hv (η j) a r).trans
      (mul_le_mul_of_nonneg_left
        (measureReal_mono (closedBall_subset_closedBall (by linarith : r+(η j).rOut ≤ 2*r)))
        (Nat.cast_nonneg k))
  have hp := ball_poincare_of_smooth_approx hf F F' hF hF' hl a hr (by positivity) hg
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hp
  exact hp.trans_eq (by ring)

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients JointBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

noncomputable def parameterEquiv (k : ℕ) : (Fin k → ℝ) ≃L[ℝ] Euc k :=
  (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.toContinuousLinearEquiv

lemma parameterEquiv_apply (k : ℕ) (z : Fin k → ℝ) :
    parameterEquiv k z = WithLp.toLp 2 z := rfl

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma coordinateMap_lipschitz {k : ℕ} (π : Fin k → X → ℝ) {K : ℝ≥0}
    (hπ : ∀ i, LipschitzWith K (π i)) : ∃ L, LipschitzWith L (coordinateMap π) := by
  have hp : LipschitzWith K (fun x i => π i x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).mpr (fun i => (hπ i).dist_le_mul x y)
  exact ⟨_,(parameterEquiv k).toContinuousLinearMap.lipschitzWith.comp hp⟩

noncomputable def fullSliceControl {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (π : Fin (k+1) → X → ℝ) (K : ℝ≥0) : Measure (Euc (k+1)) :=
  (K^k) • Measure.map (coordinateMap π)
    (currentMassMeasure h.normal.1 + currentMassMeasure h.normal.2)

instance fullSliceControl_finite {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (π : Fin (k+1) → X → ℝ) (K : ℝ≥0) :
    IsFiniteMeasure (fullSliceControl h π K) := by unfold fullSliceControl; infer_instance

lemma fullSlice_directional_variation {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1) (i : Fin (k+1)) :
    DirectionalVariation (fun z => fullSlice h π z b (fun j => Fin.elim0 j))
      (EuclideanSpace.basisFun (Fin (k+1)) ℝ i) volume (fullSliceControl h π K) := by
  intro φ hφ hc
  let A := parameterEquiv (k+1)
  let v := EuclideanSpace.basisFun (Fin (k+1)) ℝ i
  let ψ : (Fin (k+1) → ℝ) → ℝ := fun z => φ (A z)
  let dψ (z : Fin (k+1) → ℝ) := (fderiv ℝ φ (A z)).comp A.toContinuousLinearMap
  have hψ (z) : HasFDerivAt ψ (dψ z) z :=
    ((hφ.differentiable (by simp)) (A z)).hasFDerivAt.comp z A.hasFDerivAt
  have he (z : Fin (k+1) → ℝ) : dψ z (Pi.single i 1) = fderiv ℝ φ (A z) v := by
    simp only [dψ,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
    congr 1
    simp only [v,EuclideanSpace.basisFun_apply]
    rfl
  obtain ⟨L,hL⟩ := coordinateMap_lipschitz π hπ
  obtain ⟨M,hM⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hφ (by simp)
  have hbφ : BoundedLip (fun x => φ (coordinateMap π x)) := boundedLip_of_lipschitz (hM.comp hL)
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ φ z v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc : HasCompactSupport (fun z => fderiv ℝ φ z v) := by
    exact (hc.fderiv ℝ).comp_left (g := fun L => L v) rfl
  obtain ⟨N,hN⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hdc hd (by simp)
  have hbd : BoundedLip (fun x => dψ (fun j => π j x) (Pi.single i 1)) := by
    simp only [he]
    exact boundedLip_of_lipschitz (hN.comp hL)
  have hh := fullSlice_distributional_bound h hX π hπ hb hb1 hψ i hbφ hbd
  have hA (z : Euc (k+1)) : A (WithLp.ofLp z) = z := rfl
  simp only [he,hA] at hh
  change |∫ z, (fderiv ℝ φ z) v * fullSlice h π z b (fun j => Fin.elim0 j)| ≤ _
  rw [fullSliceControl,integral_smul_nnreal_measure]
  rw [integral_map hL.continuous.measurable.aemeasurable hφ.continuous.abs.aestronglyMeasurable]
  rw [integral_add_measure (integrable_boundedLip _ hbφ).abs (integrable_boundedLip _ hbφ).abs]
  simpa only [NNReal.smul_def,smul_eq_mul,NNReal.coe_pow,ψ,A,parameterEquiv_apply,coordinateMap] using hh

theorem fullSlice_ball_poincare {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1)
    (a : Euc (k+1)) {r : ℝ} (hr : 0 < r) :
    (∫ z in closedBall a r, |fullSlice h π z b (fun j => Fin.elim0 j) -
      (⨍ w in closedBall a r, fullSlice h π w b (fun j => Fin.elim0 j))|) ≤
      (4*(2:ℝ)^(k+1)*(k+1)) * r * (fullSliceControl h π K).real (closedBall a (2*r)) := by
  simpa only [Nat.cast_add,Nat.cast_one] using ball_poincare_of_directional_variation
    (fullSlice_eval_integrable h hX π (fun i => boundedLip_of_lipschitz (hπ i))
      (b := b) ⟨⟨1,hb⟩,1,hb1⟩ (fun j => Fin.elim0 j)).locallyIntegrable
    (fun i => fullSlice_directional_variation h hX π hπ hb hb1 i) a hr

end CAT0Fillings.Slicing
end

end OAI
