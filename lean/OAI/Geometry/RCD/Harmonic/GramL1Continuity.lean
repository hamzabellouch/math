import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Strong Sobolev convergence gives L1 convergence of Gram densities -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem integral_abs_localGamma_le (f g : SobolevSpace μ Q) :
    (∫ x, |localGamma μ Q f g x| ∂μ) ≤ ‖f‖*‖g‖ := by
  let F := SobolevSpace.minimalSlope μ Q f
  let G := SobolevSpace.minimalSlope μ Q g
  have hi : Integrable (fun x => F x*G x) μ := (Lp.memLp F).integrable_mul (Lp.memLp G)
  have he : (∫ x, F x*G x ∂μ)=inner ℝ F G := by
    simp only [L2.inner_def,Real.inner_apply]
  calc
    _ ≤ ∫ x, F x*G x ∂μ := integral_mono_ae (localGamma_memL1 μ Q f g).abs hi
      (localGamma_abs_le μ Q f g)
    _ ≤ ‖F‖*‖G‖ := by
      rw [he]
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) F G)
    _ ≤ ‖f‖*‖g‖ := mul_le_mul (SobolevSpace.minimalSlope_norm_le μ Q f)
      (SobolevSpace.minimalSlope_norm_le μ Q g) (norm_nonneg _) (norm_nonneg _)

theorem integral_abs_gram_difference_le (u v : SobolevSpace μ Q) :
    (∫ x, |localGamma μ Q u u x-localGamma μ Q v v x| ∂μ) ≤
      (‖u‖+‖v‖)*‖u-v‖ := by
  have he : (fun x => localGamma μ Q u u x-localGamma μ Q v v x) =ᵐ[μ]
      fun x => localGamma μ Q (u-v) u x+localGamma μ Q (u-v) v x := by
    filter_upwards [localGamma_sub_left μ Q u v u,localGamma_sub_left μ Q u v v,
      localGamma_comm μ Q u v] with x h1 h2 h3
    rw [h1,h2,h3]
    ring
  have heabs : (fun x => |localGamma μ Q u u x-localGamma μ Q v v x|) =ᵐ[μ]
      fun x => |localGamma μ Q (u-v) u x+localGamma μ Q (u-v) v x| :=
    he.mono fun _ hx => congrArg abs hx
  rw [integral_congr_ae heabs]
  calc
    _ ≤ ∫ x, |localGamma μ Q (u-v) u x|+|localGamma μ Q (u-v) v x| ∂μ :=
      integral_mono_ae ((localGamma_memL1 μ Q (u-v) u).add (localGamma_memL1 μ Q (u-v) v)).abs
        ((localGamma_memL1 μ Q (u-v) u).abs.add (localGamma_memL1 μ Q (u-v) v).abs)
        (Eventually.of_forall fun x => abs_add_le _ _)
    _ = (∫ x, |localGamma μ Q (u-v) u x| ∂μ)+(∫ x, |localGamma μ Q (u-v) v x| ∂μ) :=
      integral_add (localGamma_memL1 μ Q (u-v) u).abs (localGamma_memL1 μ Q (u-v) v).abs
    _ ≤ ‖u-v‖*‖u‖+‖u-v‖*‖v‖ := add_le_add
      (integral_abs_localGamma_le μ Q (u-v) u) (integral_abs_localGamma_le μ Q (u-v) v)
    _ = _ := by ring

theorem weighted_gram_L1_tendsto {Ω : Set X}
    (u : ℕ → SobolevSpace μ Q) (v : SobolevSpace μ Q)
    (hu : Tendsto u atTop (𝓝 v)) (φ : X → ℝ) (hφ : AEStronglyMeasurable φ μ)
    (B : ℝ≥0) (hB : ∀ᵐ x ∂μ, |φ x|≤B) :
    Tendsto (fun k => ∫ x in Ω,
      |φ x*(localGamma μ Q (u k) (u k) x-localGamma μ Q v v x)| ∂μ) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun k => ‖u k-v‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hu.sub (tendsto_const_nhds (x := v))).norm
  have hb : Tendsto (fun k => (B:ℝ)*(‖u k‖+‖v‖)*‖u k-v‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((hu.norm.add tendsto_const_nhds).const_mul (B:ℝ)).mul hnorm
  apply squeeze_zero (fun k => integral_nonneg fun x => abs_nonneg _) (fun k => ?_) hb
  have hi := (localGamma_memL1 μ Q (u k) (u k)).sub (localGamma_memL1 μ Q v v)
  calc
    _ ≤ ∫ x in Ω, (B:ℝ)*|localGamma μ Q (u k) (u k) x-localGamma μ Q v v x| ∂μ := by
      apply integral_mono_ae (hi.bdd_mul hφ (hB.mono fun _ hx => by simpa only [Real.norm_eq_abs] using hx)).abs.integrableOn
        (hi.abs.const_mul (B:ℝ)).integrableOn
      filter_upwards [ae_restrict_of_ae hB] with x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ ≤ ∫ x, (B:ℝ)*|localGamma μ Q (u k) (u k) x-localGamma μ Q v v x| ∂μ :=
      setIntegral_le_integral (hi.abs.const_mul (B:ℝ))
        (Eventually.of_forall fun x => mul_nonneg B.coe_nonneg (abs_nonneg _))
    _ ≤ _ := by
      rw [integral_const_mul,mul_assoc]
      exact mul_le_mul_of_nonneg_left (integral_abs_gram_difference_le μ Q (u k) v) B.coe_nonneg

end RegularPointCoordinates

end

end OAI
