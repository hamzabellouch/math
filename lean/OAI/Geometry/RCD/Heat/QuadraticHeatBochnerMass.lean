import OAI.Geometry.RCD.Sobolev.QuadraticBochnerCutoffLimit
import OAI.Geometry.RCD.Heat.HeatLocalSourceConvergence
import OAI.Geometry.RCD.Coordinates.BoundedRegularBochnerMass
import OAI.Geometry.RCD.Heat.BoundedHeatSobolevData

namespace OAI

/-! # Vanishing shifted Bochner mass for the actual quadratic heat approximations -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem GoodLaplacianCutoff.source_integral_tendsto_constant
    {p : X} {r C b : ℝ} (χ : GoodLaplacianCutoff μ Q p r C) (hb : 2*r < b)
    (n : ℝ) {d : Lp ℝ 2 μ} (hd : d =ᵐ[μ.restrict (ball p b)] fun _ => n)
    {ds : ℕ → Lp ℝ 2 μ} (hds : Tendsto ds atTop (𝓝 d)) :
    Tendsto (fun k => ∫ x, χ.weight x*ds k x ∂μ) atTop
      (𝓝 (n*(∫ x, χ.weight x ∂μ))) := by
  have hp (z : Lp ℝ 2 μ) : inner ℝ z (SobolevSpace.toLp μ Q χ.sobolev)=
      ∫ x, χ.weight x*z x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [χ.representative] with x hx
    simp only [Real.inner_apply,hx]
    ring
  have he : (∫ x, χ.weight x*d x ∂μ)=n*(∫ x, χ.weight x ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hd] with x hx
    by_cases hm : x∈ball p b
    · rw [hx hm,mul_comm]
    · have hdist : 2*r < dist p x := hb.trans_le (by
        simpa only [mem_ball,dist_comm,not_lt] using hm)
      rw [χ.zero x hdist]
      ring
  have h := hds.inner (𝕜 := ℝ) (tendsto_const_nhds (x := SobolevSpace.toLp μ Q χ.sobolev))
  simpa only [hp,he] using h

theorem NoncollapsedRCD.quadratic_heat_bochner_mass {n : ℕ}
    (hX : NoncollapsedRCD 0 n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (p : X)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (U : X → ℝ) (L A : ℝ≥0) (hU : LipschitzWith L U) (hUc : HasCompactSupport U)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] U)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x| ≤ A)
    {R b : ℝ} (hR : 0 < R) (hb : 4*R < b)
    (hdn : d =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => (n:ℝ))
    (he : localGamma (hausdorff n X) hX.quadratic u u
      =ᵐ[(hausdorff n X).restrict (ball p b)]
        fun x => 2*SobolevSpace.toLp (hausdorff n X) hX.quadratic u x)
    (t : ℕ → ℝ) (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let f := SobolevSpace.toLp m q u
    let w k := heatSobolev m q (t k) (ht k) f
    let D k := heatSobolevMap m q (t k/2) (half_pos (ht k))
      (-heatGeneratorAt m q (t k-t k/2) f)
    ∃ (G : ℕ → SobolevSpace m q) (σ : ℕ → Measure X),
      (∀ k, IsFiniteMeasure (σ k)) ∧
      (∀ k, SobolevSpace.toLp m q (G k) =ᵐ[m] localGamma m q (w k) (w k)) ∧
      (∀ k, ∀ (ψ : SobolevSpace m q) (v : X → ℝ),
        Continuous v → HasCompactSupport v → tsupport v ⊆ ball p (6*R) →
        SobolevSpace.toLp m q ψ =ᵐ[m] v →
        (∫ x, v x ∂σ k)=-(1/2:ℝ)*energyForm m q (G k) ψ-
          weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (D k)) ∧
      ∀ (C : ℝ) (χ : GoodLaplacianCutoff m q p R C), 0 ≤ C →
        Tendsto (fun k => (∫ x, χ.weight x ∂σ k)-
          2*(∫ x, χ.weight x*SobolevSpace.toLp m q (D k) x ∂m)+
          (n:ℝ)*(∫ x, χ.weight x ∂m)) atTop (𝓝 0) := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  intro m q f w D
  have hw (k : ℕ) := heatTail_weak_laplacian m q (t k) (ht k) f
  have hgrad (k : ℕ) : ∀ᵐ x ∂m, SobolevSpace.minimalSlope m q (w k) x ≤ L := by
    simpa only [neg_zero,zero_mul,Real.exp_zero,mul_one] using
      hX.heat_compact_slope_bdd 0 n hn hU hUc p f hu.symm (t k) (ht k)
  choose G hG using fun k => hX.bounded_heat_gram hn p f A hA (ht k)
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  have hmeasure (k : ℕ) : ∃ σ : Measure X, IsFiniteMeasure σ ∧
      (∀ (ψ : SobolevSpace m q) (v : X → ℝ), Continuous v → HasCompactSupport v →
        tsupport v ⊆ ball p (6*R) → SobolevSpace.toLp m q ψ =ᵐ[m] v →
        (∫ x, v x ∂σ)=-(1/2:ℝ)*energyForm m q (G k) ψ-
          weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (D k)) := by
    obtain ⟨hLip,-⟩ := hX.kernelHeat_bounded_regularity hn p hk f A hA (t k) (ht k)
    have hwr : SobolevSpace.toLp m q (w k) =ᵐ[m] kernelHeat m q hk (t k) f := by
      simpa only [w,heatSobolev_toLp] using (kernelHeat_represents_L2 m q hk (ht k) f).symm
    obtain ⟨M,-,hM⟩ := hX.bounded_regular_bochner_mass hn le_rfl p (w k) (D k) (G k)
      (hw k) (kernelHeat m q hk (t k) f) hLip hwr A
      (hX.bounded_heat_sobolev_data hn p f A hA (ht k)).1 (hG k)
    obtain ⟨σ,hσ,hrep,-⟩ := hM (2*R) (by positivity)
    refine ⟨σ,hσ,?_⟩
    intro ψ v hv hvc hvs hψ
    simpa only [zero_mul,sub_zero] using hrep ψ v hv hvc
      (by simpa only [show 3*(2*R)=6*R by ring] using hvs) hψ
  choose σ hσ hrep using hmeasure
  refine ⟨G,σ,hσ,hG,hrep,?_⟩
  intro C χ hC
  obtain ⟨hconv,hdconv⟩ := heat_regularization_value_source_converges m q u d hd t ht ht0
  have hlim := χ.quadratic_bochner_source_tendsto m q hC (by linarith : 2*R<b)
    u d hd n hdn he w D G hw hG L hgrad
    (SobolevSpace.minimalSlope_le_lipschitz m q u hU hu) hconv hdconv
  have hσlim : Tendsto (fun k => ∫ x, χ.weight x ∂σ k) atTop
      (𝓝 ((n:ℝ)*(∫ x, χ.weight x ∂m))) := by
    apply hlim.congr'
    filter_upwards [] with k
    exact (hrep k χ.sobolev χ.weight χ.weight.continuous (χ.hasCompactSupport m q)
      ((χ.tsupport_subset m q).trans (closedBall_subset_ball (by linarith))) χ.representative).symm
  have hdlim := χ.source_integral_tendsto_constant m q (by linarith : 2*R<b) n hdn hdconv
  have hh := (hσlim.sub (hdlim.const_mul 2)).add
    (tendsto_const_nhds (x := (n:ℝ)*(∫ x, χ.weight x ∂m)))
  simpa only [show (n:ℝ)*(∫ x, χ.weight x ∂m)-2*((n:ℝ)*(∫ x, χ.weight x ∂m))+
    (n:ℝ)*(∫ x, χ.weight x ∂m)=0 by ring] using hh

end RegularPointCoordinates

end

end OAI
