import OAI.Geometry.RCD.Sobolev.HarmonicBochnerCutoffLimit
import OAI.Geometry.RCD.Heat.HeatLocalSourceConvergence
import OAI.Geometry.RCD.Coordinates.BoundedRegularBochnerMass
import OAI.Geometry.RCD.Heat.BoundedHeatSobolevData

namespace OAI

/-! # Actual heat Bochner measures have vanishing local mass near a flat harmonic function

Both the regularizations and their sources are the original heat semigroup.
The measures satisfy the full continuous compact Sobolev test identity;
their singular parts are retained in the mass limit.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {n : ℕ} (hX : NoncollapsedRCD 0 n X) (hn : 2 ≤ n) (p : X)
  [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem heat_local_bochner_mass
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (U : X → ℝ) (L A : ℝ≥0) (hU : LipschitzWith L U) (hUc : HasCompactSupport U)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] U)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x| ≤ A)
    {R b : ℝ} (hR : 0 < R) (hb : 4*R < b)
    (hd0 : d =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => 0) (c : ℝ)
    (hc : localGamma (hausdorff n X) hX.quadratic u u
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c)
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
      Tendsto (fun k => (σ k).real (closedBall p R)) atTop (𝓝 0) := by
  intro m q f w D
  have hw (k : ℕ) := heatTail_weak_laplacian m q (t k) (ht k) f
  have hgrad (k : ℕ) : ∀ᵐ x ∂m, SobolevSpace.minimalSlope m q (w k) x ≤ L := by
    simpa only [neg_zero,zero_mul,Real.exp_zero,mul_one] using
      hX.heat_compact_slope_bdd 0 n hn hU hUc p f hu.symm (t k) (ht k)
  choose G hG using fun k => hX.bounded_heat_gram hn p f A hA (ht k)
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  have hmeasure (k : ℕ) : ∃ σ : Measure X, IsFiniteMeasure σ ∧
      (∀ (ψ : SobolevSpace m q) (v : X → ℝ),
        Continuous v → HasCompactSupport v → tsupport v ⊆ ball p (6*R) →
        SobolevSpace.toLp m q ψ =ᵐ[m] v →
        (∫ x, v x ∂σ)=-(1/2:ℝ)*energyForm m q (G k) ψ-
          weightedGamma m q (SobolevSpace.toLp m q ψ) (w k) (D k)) := by
    obtain ⟨hLip,-⟩ := hX.kernelHeat_bounded_regularity hn p hk f A hA (t k) (ht k)
    have hwr : SobolevSpace.toLp m q (w k) =ᵐ[m] kernelHeat m q hk (t k) f := by
      simpa only [w,heatSobolev_toLp] using (kernelHeat_represents_L2 m q hk (ht k) f).symm
    obtain ⟨M,_hM,hM⟩ := hX.bounded_regular_bochner_mass hn le_rfl p (w k) (D k) (G k)
      (hw k) (kernelHeat m q hk (t k) f) hLip hwr A
      (hX.bounded_heat_sobolev_data hn p f A hA (ht k)).1 (hG k)
    obtain ⟨σ,hσ,hrep,_hmass⟩ := hM (2*R) (by positivity)
    refine ⟨σ,hσ,?_⟩
    intro ψ v hv hvc hvs hψ
    simpa only [zero_mul,sub_zero] using hrep ψ v hv hvc (by convert hvs using 1; ring_nf) hψ
  choose σ hσ hrep using hmeasure
  let (k : ℕ) : IsFiniteMeasure (σ k) := hσ k
  obtain ⟨C,hC,⟨χ⟩⟩ := hX.goodCutoff_exists hn p (show 0 < 2*R by positivity)
  obtain ⟨hconv,hdconv⟩ := heat_regularization_value_source_converges m q u d hd t ht ht0
  have hlim := χ.bochner_source_tendsto_zero m q (show 0 < 2*R by positivity)
    (by linarith : 0 ≤ C) (show 2*(2*R)<b by linarith) u d hd0 c hc w D G hw hG L hgrad
    (SobolevSpace.minimalSlope_le_lipschitz m q u hU hu) hconv hdconv
  have hlimχ : Tendsto (fun k => ∫ x, χ.weight x ∂σ k) atTop (𝓝 0) := by
    apply hlim.congr'
    filter_upwards [] with k
    exact (hrep k χ.sobolev χ.weight χ.weight.continuous (χ.hasCompactSupport m q)
      ((χ.tsupport_subset m q).trans (closedBall_subset_ball (by linarith))) χ.representative).symm
  refine ⟨G,σ,hσ,hG,hrep,?_⟩
  apply χ.measure_mass_tendsto_zero m q σ hlimχ measurableSet_closedBall
  intro x hx
  exact χ.one x (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith)))

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
