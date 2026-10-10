import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSlowFamily

namespace OAI

/-! The finite slow iteration solves the actual restored polynomial mean
metric to any prescribed finite unweighted order. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PrimitiveRealization WeightedEstimates
local instance meanApproxFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance meanApproxFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance meanApproxDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance meanApproxDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance meanApproxSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance meanApproxSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma tensorWeightedBound_unscaled {H : ∀ x : M, CovariantTwoTensor x}
    {s C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hH : A.TensorWeightedBound s m C H) : A.TensorWeightedBound 1 m (C/s^m) H := by
  intro i j hj x hx
  simp only [one_pow,one_mul]
  exact ((hH i).deriv_le hs hj hx).trans (div_le_div_of_nonneg_left hC (pow_pos hs _)
    (pow_le_pow_of_le_one hs.le hs1 hj))

lemma polynomial_metric_error_of_defect {n : A.centers → ℕ}
    {Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {G : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G)
    {ε δ s C D : ℝ} {m : ℕ} (hs : 0 ≤ s) (hδ : δ ≠ 0)
    (hbase : A.TensorWeightedBound s m C γ)
    (hdefect : A.TensorWeightedBound s m D (A.normalizedPolynomialDefect Pol ε δ γ G)) :
    A.TensorWeightedBound s m (δ^2*(C+D)) (A.atlasPolynomialMetric Pol ε G-γ) := by
  have hd := A.normalizedPolynomialDefect_smooth (ε := ε) (δ := δ) hPol hγ hG
  have hh := A.tensorWeightedBound_const_smul (hγ.add_section hd)
    (A.tensorWeightedBound_add hγ hd hs hbase hdefect) (-(δ^2))
  have heq : A.atlasPolynomialMetric Pol ε G-γ =
      (-(δ^2)) • (γ+A.normalizedPolynomialDefect Pol ε δ γ G) := by
    funext x
    ext v w
    change A.atlasPolynomialMetric Pol ε G x v w-γ x v w =
      -(δ^2)*(γ x v w+((δ^2)⁻¹*(γ x v w-A.atlasPolynomialMetric Pol ε G x v w)-γ x v w))
    field_simp
    ring
  rw [heq]
  simpa only [abs_neg,abs_of_nonneg (sq_nonneg δ)] using hh

end SmoothingAtlas
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

/-- Finite-order approximation of the actual polynomial mean, with all
slow-map derivative profiles and a vanishing C3 displacement. -/
theorem polynomial_mean_approximation (data : MetricGoodPhaseData g F)
    {n : data.A.centers → ℕ}
    (Pol : ∀ i : data.A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (R N : ℕ) (σmax : ℝ) (hσmax : 0 < σmax) :
    ∃ (b u η L C : ℝ) (P : ℕ → ℝ), 0 ≤ b ∧ b < 1/16 ∧ b < σmax ∧ 0 < u ∧
      0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ C ∧ (∀ m, 0 ≤ P m) ∧
    ∀ z : ℝ, 0 < z → z < η → ∃ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G ∧
      data.A.WeightedBound 1 3 (L*z^u) (G-F) ∧
      (∀ m, data.A.ShiftedBound 2 m (z^b) (P m) G) ∧
      data.A.TensorWeightedBound 1 R (C*z^N) (data.A.atlasPolynomialMetric Pol z G-g.inner) := by
  obtain ⟨steps,hsteps,horder⟩ := exists_amplitude_steps R N
  obtain ⟨σ,hσ,hσ16,hσσmax,hfamily⟩ :=
    data.polynomial_finite_slow_family Pol hPol hF hmetric steps hsteps σmax hσmax
  obtain ⟨a,u,η,L,P,D,ha,hu,hη,hη1,hL,hP,hD,_,hfamily⟩ := hfamily steps le_rfl
  obtain ⟨K,hK,hbase⟩ := data.A.exists_bundle_bound data.A.tensorTriv data.A.tensorTriv_domain R g.contMDiff
  let b := scaleExponent σ steps steps
  have hb := (scaleExponent_bounds hσ hsteps (le_refl steps)).1
  have hbσ := (scaleExponent_bounds hσ hsteps (le_refl steps)).2
  have hpow : (N : ℝ) ≤ 2*amplitudeExponent steps-b*(R : ℝ) := by
    have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
    have hb1 : b ≤ 1 := by dsimp [b]; linarith
    have hh : b*(R : ℝ) ≤ R := by nlinarith
    linarith
  refine ⟨b,u,η,L,K+D R,P,hb,hbσ.trans_lt hσ16,hbσ.trans_lt hσσmax,hu,hη,hη1,hL,add_nonneg hK (hD R),hP,?_⟩
  intro z hz hzη
  have hz1 := hzη.le.trans hη1
  have hs : 0 < z^b := Real.rpow_pos_of_pos hz _
  have hs1 : z^b ≤ 1 := Real.rpow_le_one hz.le hz1 hb
  obtain ⟨G,hG,hclose,hmap,hdefect⟩ := hfamily z hz hzη
  have hδ : 0 < z^amplitudeExponent steps := Real.rpow_pos_of_pos hz _
  have hDb : data.A.TensorWeightedBound (z^b) R (D R)
      (data.A.normalizedPolynomialDefect Pol z (z^amplitudeExponent steps) g.inner G) := by
    intro i
    apply (hdefect R i).mono_const
    exact mul_le_of_le_one_right (hD R) (Real.rpow_le_one hz.le hz1 ha.le)
  have herror := data.A.polynomial_metric_error_of_defect hPol g.contMDiff hG hs.le hδ.ne'
    (fun i => (hbase i).shrink_scale hs.le hs1) hDb
  have he := data.A.tensorWeightedBound_unscaled hs hs1
    (mul_nonneg (sq_nonneg _) (add_nonneg hK (hD R))) herror
  refine ⟨G,hG,hclose,hmap,fun i => (he i).mono_const ?_⟩
  have heq : (z^amplitudeExponent steps)^2*(K+D R)/(z^b)^R =
      (K+D R)*z^(2*amplitudeExponent steps-b*R) := by
    rw [← Real.rpow_mul_natCast hz.le,← Real.rpow_mul_natCast hz.le]
    rw [mul_comm (z^_) _,mul_div_assoc,← Real.rpow_sub hz]
    congr 2
    ring
  rw [heq]
  simpa only [Real.rpow_natCast] using mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hz hz1 hpow) (add_nonneg hK (hD R))

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
