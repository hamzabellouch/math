import OAI.Geometry.SurfaceImmersion.Correction.MetricPolynomialSlowStep
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveSeedBounds
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveInitialFamily

namespace OAI

/-! The finite family solving the perturbed mean equation to successively
higher amplitude orders. Every member is an actual smooth map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PrimitiveRealization
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Uniform profiles for the nearby smooth maps at one finite stage. -/
def HasPolynomialSlowFamily {n : A.centers → ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (γ : ∀ x : M, CovariantTwoTensor x) (F : M → Space) (d b : ℝ) : Prop :=
  ∃ (a u η L : ℝ) (P D : ℕ → ℝ), 0 < a ∧ 0 < u ∧ 0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧
    (∀ m, 0 ≤ P m) ∧ (∀ m, 0 ≤ D m) ∧
    (∀ m, A.ShiftedBound 2 m 1 (P m) F) ∧
    ∀ z : ℝ, 0 < z → z < η → ∃ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G ∧
      A.WeightedBound 1 3 (L*z^u) (G-F) ∧
      (∀ m, A.ShiftedBound 2 m (z^b) (P m) G) ∧
      (∀ m, A.TensorWeightedBound (z^b) m (D m*z^a)
        (A.normalizedPolynomialDefect Pol z (z^d) γ G))

lemma polynomial_slow_seed {n : A.centers → ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) :
    A.HasPolynomialSlowFamily Pol (inducedTensor F) F (1/4) 0 := by
  classical
  obtain ⟨U,K,hU,hUK,_,houter⟩ := A.exists_outer_domains
  obtain ⟨L,D,hL,hD,hseed⟩ := A.atlas_primitive_seed_defect_bounds Pol hPol F hF U hU K hUK houter
  choose P hP hPF using fun m => A.exists_shifted_bound 2 m hF
  refine ⟨1/2,1/2,1,L 3,P,D,by norm_num,by norm_num,zero_lt_one,le_rfl,
    hL 3,hP,hD,hPF,?_⟩
  intro z hz hz1
  have hδ : 0 < z^(1/4 : ℝ) := Real.rpow_pos_of_pos hz _
  have hδ1 : (z^(1/4 : ℝ))^2 ≤ 1 := by
    rw [initial_amplitude_square hz]
    exact Real.rpow_le_one hz.le hz1.le (by norm_num)
  obtain ⟨hclose,hdefect⟩ := hseed (z^(1/4 : ℝ)) z hδ.ne' hδ1 hz.le hz1.le
  have hsqrt : |Real.sqrt (1-(z^(1/4 : ℝ))^2)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (sub_nonneg.mpr hδ1),Real.sqrt_nonneg (1-(z^(1/4 : ℝ))^2)]
  refine ⟨Real.sqrt (1-(z^(1/4 : ℝ))^2) • F,space_smul_contMDiff hF _,?_,?_,?_⟩
  · simpa only [initial_amplitude_square hz] using hclose 3
  · intro m
    simpa only [Real.rpow_zero] using
      A.shiftedBound_smul_of_abs_le_one hF zero_le_one (hP m) hsqrt (hPF m)
  · intro m
    have he : D m*z/(z^(1/4 : ℝ))^2 = D m*z^(1/2 : ℝ) := by
      rw [mul_div_assoc,initial_error_quotient hz]
    simpa only [Real.rpow_zero,he] using hdefect m

end SmoothingAtlas

namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

/-- The number of stages and the loss determine the slow scales before any
accuracy order. This finite induction uses only constructed increments. -/
theorem polynomial_finite_slow_family (data : MetricGoodPhaseData g F)
    {n : data.A.centers → ℕ}
    (Pol : ∀ i : data.A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (steps : ℕ) (hsteps : 1 ≤ steps) (σmax : ℝ) (hσmax : 0 < σmax) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1/16 ∧ σ < σmax ∧ ∀ j : ℕ, j ≤ steps →
      data.A.HasPolynomialSlowFamily Pol g.inner F (amplitudeExponent j) (scaleExponent σ steps j) := by
  obtain ⟨loss,hstep⟩ := data.polynomial_slow_step Pol hPol hF
  obtain ⟨σ₀,hσ₀,_,_,hσ₀loss,hσ₀16,_⟩ := exists_slow_exponent 0 0 1 (by norm_num) (loss : ℝ) 0
  let σ := min σ₀ (σmax/2)
  have hσ : 0 < σ := lt_min hσ₀ (half_pos hσmax)
  have hσ16 : σ < 1/16 := (min_le_left _ _).trans_lt hσ₀16
  have hσσmax : σ < σmax := (min_le_right _ _).trans_lt (half_lt_self hσmax)
  have hσloss : σ*(loss : ℝ) < 1/2 := (mul_le_mul_of_nonneg_right
    (min_le_left σ₀ (σmax/2)) (Nat.cast_nonneg loss : (0 : ℝ) ≤ loss)).trans_lt hσ₀loss
  refine ⟨σ,hσ,hσ16,hσσmax,?_⟩
  intro j hj
  induction j with
  | zero =>
      simpa only [amplitudeExponent_zero,scaleExponent,Nat.cast_zero,zero_mul,zero_div,hmetric] using
        data.A.polynomial_slow_seed Pol hPol F hF
  | succ j ih =>
      have hjlt : j < steps := by omega
      obtain ⟨a,u,η,L,P,D,ha,hu,hη,hη1,hL,hP,hD,hPF,hfamily⟩ := ih (by omega)
      have hb := (scaleExponent_bounds hσ hsteps (by omega : j ≤ steps)).1
      have hb' := (scaleExponent_bounds hσ hsteps (by omega : j+1 ≤ steps)).2
      have hscale : scaleExponent σ steps j < scaleExponent σ steps (j+1) := by
        have hdiff := scaleExponent_step (σ := σ) (steps := steps) (j := j)
        have hd : 0 < σ/(steps : ℝ) := div_pos hσ (by exact_mod_cast (by omega : 0 < steps))
        linarith
      have hloss : scaleExponent σ steps (j+1)*(loss : ℝ) < 1 := by
        have hh := mul_le_mul_of_nonneg_right hb' (Nat.cast_nonneg loss : (0 : ℝ) ≤ loss)
        linarith
      have hpositives := slow_step_positive_powers hσ hσ16 hsteps hjlt
      have hbd : 2*scaleExponent σ steps (j+1) < amplitudeExponent j := by
        have hd := amplitudeExponent_lower j
        linarith
      have hdd : amplitudeExponent j < amplitudeExponent (j+1) := by
        rw [amplitudeExponent_succ]
        linarith [amplitudeExponent_pos j]
      obtain ⟨a',η',L',P',D',ha',hη',hη'1,hL',hP',hD',hnext⟩ :=
        hstep (scaleExponent σ steps j) (scaleExponent σ steps (j+1))
          (amplitudeExponent j) (amplitudeExponent (j+1)) a u hb hscale hloss hbd hdd
          (by linarith [hpositives.1]) ha hu P D L hP hD hL hPF
      let R : ℕ → ℝ := fun m => max (P' m) (P m)
      refine ⟨a',min u (amplitudeExponent j-2*scaleExponent σ steps (j+1)),min η η',L',R,D',
        ha',lt_min hu (sub_pos.mpr hbd),lt_min hη hη',
        (min_le_left _ _).trans hη1,hL',?_,hD',?_,?_⟩
      · intro m
        exact (hP' m).trans (le_max_left _ _)
      · intro m i k hk x
        exact (hPF m i k hk x).trans (le_max_right _ _)
      · intro z hz hzmin
        obtain ⟨G,hG,hclose,hmap,hdefect⟩ := hfamily z hz (hzmin.trans_le (min_le_left _ _))
        obtain ⟨G',hG',hclose',hmap',hdefect'⟩ := hnext z hz
          (hzmin.trans_le (min_le_right _ _)) G hG hclose hmap hdefect
        refine ⟨G',hG',hclose',?_,hdefect'⟩
        intro m i k hk x
        exact (hmap' m i k hk x).trans (le_max_left _ _)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
