import OAI.Geometry.RCD.Harmonic.DyadicRootDirectionConvergence
import OAI.Geometry.RCD.Coordinates.UnitCoordinateDirections
import OAI.Geometry.RCD.Harmonic.MixedGramL1

namespace OAI

/-! # Finite Gram convergence in the original root frame -/

open Set Metric Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem dyadic_root_gram_convergence {K : ℝ} (m : ℕ) (hm : 2 ≤ m+1)
    (hX : NoncollapsedRCD K (m+1) X) [(hausdorff (m+1) X).Regular]
    {a κ : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m+1) X) (comparisonModelVolume m a))
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hsmall : ((m+1 : ℕ) : ℝ)^2*(normalizationVolumeRatio m*κ) ≤ 1/2)
    (p : ℕ → X) (r ε : ℕ → ℝ) (d : ℕ → ℕ)
    (hr : ∀ k, 0 < r k) (hd : Tendsto d atTop atTop)
    (hcurv : ∀ k, -1 ≤ K*(r k)^2)
    (hcurv5 : ∀ k, -1 ≤ K*(5*r k)^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (V : ℕ → X → Euclidean (m+1))
    (hV : ∀ j : ℕ, ∀ᶠ k in atTop, IsMeasuredEuclideanApproximation (hausdorff (m+1) X)
      (m+1) (p k) (r k) ((j : ℝ)+1) (ε k) (V k))
    (u : ℕ → Fin (m+1) → SobolevSpace (hausdorff (m+1) X) hX.quadratic)
    (v : ℕ → X → Euclidean (m+1)) (A : ℕ → Euclidean (m+1) ≃L[ℝ] Euclidean (m+1))
    (hA : ∀ k, IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k))
      (ball (p k) (r k)) measurableSet_ball (A k))
    (hscale : ∀ k j, j ≤ d k → a*(3*((2 : ℝ)^j*r k)) ≤ 1)
    (hframes : ∀ k j, j ≤ d k → ∃ (S : Euclidean (m+1) ≃L[ℝ] Euclidean (m+1))
      (w : X → Euclidean (m+1)),
      FirstOrderSplittingOn (hausdorff (m+1) X) hX.quadratic (p k) ((2 : ℝ)^j*r k) κ
        (transformedColumn (hausdorff (m+1) X) hX.quadratic (u k) S) w ∧
      IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k))
        (ball (p k) ((2 : ℝ)^j*r k)) measurableSet_ball S)
    (hv : ∀ k, ContinuousOn (v k) (ball (p k) ((2 : ℝ)^(d k)*r k)))
    (hrep : ∀ k i, SobolevSpace.toLp (hausdorff (m+1) X) hX.quadratic (u k i) =ᵐ[
      (hausdorff (m+1) X).restrict (ball (p k) ((2 : ℝ)^(d k)*r k))] fun x => v k x i)
    (hu : ∀ k i, IsSobolevHarmonicOn (hausdorff (m+1) X) hX.quadratic
      (ball (p k) ((2 : ℝ)^(d k)*r k)) (u k i)) :
    (∀ i : Fin (m+1), ∀ β : ℝ, 0 < β → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff (m+1) X).restrict (ball (p k) (3*r k)),
        localGamma (hausdorff (m+1) X) hX.quadratic
          (transformedColumn (hausdorff (m+1) X) hX.quadratic (u k) (A k) i)
          (transformedColumn (hausdorff (m+1) X) hX.quadratic (u k) (A k) i) x ≤ 1+β) ∧
    (∀ i j : Fin (m+1), Tendsto (fun k => ((hausdorff (m+1) X).real (ball (p k) (2*r k)))⁻¹*
      ∫ x in ball (p k) (2*r k),
        |localGamma (hausdorff (m+1) X) hX.quadratic
          (transformedColumn (hausdorff (m+1) X) hX.quadratic (u k) (A k) i)
          (transformedColumn (hausdorff (m+1) X) hX.quadratic (u k) (A k) j) x-
            (if i=j then 1 else 0)| ∂hausdorff (m+1) X) atTop (𝓝 0)) := by
  let μ := hausdorff (m+1) X
  let e : Fin (m+1) → Euclidean (m+1) := fun i => EuclideanSpace.single i 1
  let G := fun (i : Fin (m+1)) k => transformedColumn μ hX.quadratic (u k) (A k) i
  have hdir (z : Euclidean (m+1)) (hz : ‖z‖=1) :=
    dyadic_root_unit_direction_convergence m hm hX ha hBG hκ hκ1 hsmall p r ε d hr hd
      hcurv hcurv5 hε hε1 hεlim V hV u v A hA hscale hframes hv hrep hu z hz
  have he (i : Fin (m+1)) : ‖e i‖=1 := by simp [e]
  have hdiag (i : Fin (m+1)) : Tendsto (fun k => (μ.real (ball (p k) (2*r k)))⁻¹*
      ∫ x in ball (p k) (2*r k), |localGamma μ hX.quadratic (G i k) (G i k) x-1| ∂μ)
      atTop (𝓝 0) := (hdir (e i) (he i)).2
  refine ⟨fun i => (hdir (e i) (he i)).1,?_⟩
  intro i j
  by_cases hij : i=j
  · subst j
    simpa using hdiag i
  · let z := (Real.sqrt 2)⁻¹ • (e i+e j)
    have hsum : ‖e i+e j‖^2=2 := by
      rw [norm_add_sq_real,he i,he j]
      norm_num [e,EuclideanSpace.inner_single_left,hij]
    have hsum' : ‖e i+e j‖=Real.sqrt 2 := by
      nlinarith [norm_nonneg (e i+e j),Real.sqrt_nonneg 2,
        Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    have hz : ‖z‖=1 := by
      change ‖(Real.sqrt 2)⁻¹ • (e i+e j)‖=1
      rw [norm_smul,Real.norm_of_nonneg (by positivity),hsum']
      exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
    have hpair := (hdir z hz).2
    have hG (k : ℕ) : sobolevColumnMap μ hX.quadratic (u k) (A k z) =
        (Real.sqrt 2)⁻¹ • (G i k+G j k) := by
      simp only [z,map_smul,map_add]
      rfl
    change Tendsto (fun k => (μ.real (ball (p k) (2*r k)))⁻¹*
      ∫ x in ball (p k) (2*r k), |localGamma μ hX.quadratic
        (sobolevColumnMap μ hX.quadratic (u k) (A k z))
        (sobolevColumnMap μ hX.quadratic (u k) (A k z)) x-1| ∂μ) atTop (𝓝 0) at hpair
    simp_rw [hG] at hpair
    have hmix := mixed_gram_l1_tendsto μ hX.quadratic
      (fun k => ball (p k) (2*r k)) (fun k => (hX.finiteOnBounded _ isBounded_ball).ne)
      (fun _ => 1) (fun k => (μ.real (ball (p k) (2*r k)))⁻¹) (fun _ => by positivity)
      (G i) (G j)
      (by simpa only [one_pow,one_mul] using hdiag i)
      (by simpa only [one_pow,one_mul] using hdiag j)
      (by simpa only [one_pow,one_mul] using hpair)
    simpa only [one_pow,one_mul,ite_eq_right hij,sub_zero] using hmix

end RegularPointCoordinates

end

end OAI
