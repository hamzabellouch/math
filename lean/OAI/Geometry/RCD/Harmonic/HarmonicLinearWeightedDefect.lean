import OAI.Geometry.RCD.Harmonic.HarmonicLinearSharp
import OAI.Geometry.RCD.Harmonic.WeightedUnitDefect
import OAI.Geometry.RCD.Sobolev.WeightedBallEnergyLiminf
import OAI.Geometry.RCD.Sobolev.PhysicalBallMeasuredTests

namespace OAI

/-! # Weighted L1 gradient convergence for unit linear harmonic limits -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_linear_weighted_defect {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1≤K*r k^2) (hcurv5 : ∀ k, -1≤K*(5*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w k))
    {M : ℝ} (hM : 0<M) (hnorm : ∀ k, harmonicTargetNorm hX (p k) (5*r k) (w k)≤M)
    (L : Euclidean n →L[ℝ] ℝ) (hL : ‖L‖=1)
    (hconv : ∀ W, 0<W → W<5 → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-L (V k x)|≤δ)
    (φ : Euclidean n →ᵇ ℝ) (hφ : ∀ z, 0≤φ z) (hφ1 : ∀ z, φ z≤1)
    (hs : Function.support φ⊆ball 0 (11/4)) :
    Tendsto (fun k => ((hausdorff n X).real (ball (p k) (5*r k)))⁻¹*
      ∫ x in ball (p k) (5*r k), φ (V k x)*
        |r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x-1|
        ∂hausdorff n X) atTop (𝓝 0) := by
  let μ := hausdorff n X
  let Ω := fun k => ball (p k) (5*r k)
  let mass := fun k => μ.real (Ω k)
  let f := fun k x => φ (V k x)
  let g := fun k x => r k^2*localGamma μ hX.quadratic (w k) (w k) x
  have hfinite (k : ℕ) : μ (Ω k)≠⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
  have : ∀ k, IsFiniteMeasure (μ.restrict (Ω k)) := fun k =>
    ⟨by simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded _ isBounded_ball⟩
  have hm (k : ℕ) : 0 < mass k := ENNReal.toReal_pos
    (hX.fullSupport _ _ (mul_pos (by norm_num) (hr k))).ne' (hfinite k)
  have hfm (k : ℕ) : AEStronglyMeasurable (f k) μ :=
    (φ.continuous.measurable.comp (hV k).measurable).aestronglyMeasurable
  have hfi (k : ℕ) : IntegrableOn (f k) (Ω k) μ := by
    apply (MemLp.of_bound (hfm k).restrict 1 _ : MemLp (f k) 1 (μ.restrict (Ω k))).integrable le_rfl
    exact Eventually.of_forall (fun x => by
      change ‖φ (V k x)‖≤1
      rw [Real.norm_eq_abs,abs_of_nonneg (hφ _)]
      exact hφ1 _)
  have hfgi (k : ℕ) : IntegrableOn (fun x => f k x*g k x) (Ω k) μ :=
    (((localGamma_memL1 μ hX.quadratic (w k) (w k)).const_mul (r k^2)).bdd_mul
      (hfm k) (Eventually.of_forall (fun x => φ.norm_coe_le_norm (V k x)))).integrableOn
  have hmass (k : ℕ) : (mass k)⁻¹*(∫ x in Ω k, f k x ∂μ)≤1 := by
    have hi : (∫ x in Ω k, f k x ∂μ)≤μ.real (Ω k) := by
      simpa only [setIntegral_const,smul_eq_mul,mul_one] using
        integral_mono_ae (hfi k) (integrableOn_const (hfinite k))
          (Eventually.of_forall (fun x => hφ1 (V k x)))
    exact (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (hm k).le)).trans_eq (inv_mul_cancel₀ (hm k).ne')
  have hmasslim := physical_ball_measured_test_tendsto (by norm_num : (0:ℝ)<5)
    (by norm_num : (0:ℝ)<5) le_rfl hr hV hfinite hm hεlim φ
  obtain ⟨B,hB,hbound⟩ := hX.bounded_harmonic_scaled_energy_bound hn
    (S:=5) (R:=4) (by norm_num) (by norm_num) (by norm_num) hM p r hr hcurv w hw hnorm
  have hlower := hX.weighted_energy_eventual_lower_on_ball hn
    (S:=5) (ρ:=11/4) (τ:=3) (R:=4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    p r ε V hr hcurv hε hε1 hεlim hV w L
    (fun _ _ => ⟨_,L.lipschitzWith.lipschitzOnWith⟩) hconv φ hφ hs hB (Eventually.of_forall hbound)
  have hderiv (z : Euclidean n) : ‖fderiv ℝ L z‖^2=1 := by rw [L.hasFDerivAt.fderiv,hL]; norm_num
  simp_rw [hderiv,mul_one] at hlower
  have hfull : (∫ z, φ z)=∫ z in ball (0:Euclidean n) 5, φ z := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact Function.notMem_support.mp (fun hh => hz ((ball_subset_ball (by norm_num : (11/4:ℝ)≤5)) (hs hh)))
  rw [hfull] at hlower
  have hlow : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      (volume.real (ball (0:Euclidean n) 5))⁻¹*(∫ z in ball 0 5, φ z)-δ≤
        (mass k)⁻¹*∫ x in Ω k, f k x*g k x ∂μ := by
    intro δ hδ
    filter_upwards [hlower δ hδ] with k hk
    convert hk using 1
    dsimp only [mass,Ω,f,g,μ]
    simp_rw [mul_left_comm (φ _) (r k^2)]
    rw [integral_const_mul]
    ring
  have hsharp := hX.harmonic_linear_sharp hn p r ε V hr hcurv hcurv5 hε hε1 hεlim hV
    w hw hM hnorm L hL.le hconv
  have hup : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k),
      f k x*g k x≤(1+δ)*f k x := by
    intro δ hδ
    filter_upwards [hsharp δ hδ,hεlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/8))]
      with k hk he
    have hglobal := (ae_restrict_iff' measurableSet_ball).mp hk
    filter_upwards [ae_restrict_of_ae hglobal,self_mem_ae_restrict measurableSet_ball] with x hx hxb
    by_cases hxin : x∈ball (p k) (3*r k)
    · exact (mul_le_mul_of_nonneg_left (hx hxin) (hφ _)).trans_eq (mul_comm _ _)
    · have hd : 3≤dist x (p k)/r k := (le_div_iff₀ (hr k)).mpr (by
        have hh : 3*r k≤dist x (p k) := le_of_not_gt hxin
        linarith)
      have hrad := (abs_le.mp (pointed_radial_distance (hr k) (by norm_num : (0:ℝ)≤5)
        (hV k).metric hxb.le)).1
      have hz : φ (V k x)=0 := Function.notMem_support.mp (by
        intro hz
        have ht := hs hz
        simp only [mem_ball,dist_zero_right] at ht
        linarith)
      simp [f,hz]
  exact weighted_unit_defect_tendsto μ Ω (fun k => (mass k)⁻¹)
    (fun k => inv_nonneg.mpr (hm k).le) f g hfi hfgi
    (fun _ => Eventually.of_forall (fun _ => hφ _)) hmass hmasslim hlow hup

end RegularPointCoordinates

end

end OAI
