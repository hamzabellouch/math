import OAI.Geometry.RCD.Harmonic.SupportedCoefficientL2Error
import OAI.Geometry.RCD.Metric.ContainingMassUniformL2
import OAI.Geometry.RCD.Harmonic.PointedRadialDistance

namespace OAI

/-! # Uniform compact-test recovery preserves the original mixed pairing -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem compact_recovery_coefficient (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} {S c d T : ℝ} (hS : 0<S) (hcT : c<T) (hdT : d<T) (hTS : T<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (V k))
    [∀ k, IsFiniteMeasure (μ.restrict (ball (p k) (S*r k)))]
    (hmass : ∀ k, 0<μ.real (ball (p k) (S*r k)))
    (u f w : ℕ → SobolevSpace μ hQ)
    (ψ : Euclidean n → ℝ) (hψ : Continuous ψ) {B : ℝ} (hψB : ∀ x, |ψ x|≤B)
    (hψs : tsupport ψ⊆ball 0 d)
    (huz : ∀ k, ∀ᵐ x ∂μ, x∉ball (p k) (c*r k) → SobolevSpace.toLp μ hQ (u k) x=0)
    (hconv : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (S*r k)),
        |SobolevSpace.toLp μ hQ (u k) x-ψ (V k x)|≤δ)
    {M L : ℝ} (hM : 0≤M) (hL : 0≤L)
    (hf : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (ball (p k) (T*r k)),
      r k^2*localGamma μ hQ (f k) (f k) x≤M^2)
    (hw : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (ball (p k) (T*r k)),
      r k^2*localGamma μ hQ (w k) (w k) x≤L^2) :
    Tendsto (fun k => r k^2*(μ.real (ball (p k) (S*r k)))⁻¹*
      (∫ x in ball (p k) (S*r k), ψ (V k x)*localGamma μ hQ (f k) (w k) x ∂μ)-
      r k^2*(μ.real (ball (p k) (S*r k)))⁻¹*
      (∫ x in ball (p k) (S*r k), SobolevSpace.toLp μ hQ (u k) x*
        localGamma μ hQ (f k) (w k) x ∂μ)) atTop (𝓝 0) := by
  let U := fun k => ball (p k) (S*r k)
  let Ω := fun k => ball (p k) (T*r k)
  let z := fun k x => ψ (V k x)-SobolevSpace.toLp μ hQ (u k) x
  have hψL (k : ℕ) : MemLp (fun x => ψ (V k x)) 2 (μ.restrict (U k)) :=
    MemLp.of_bound (hψ.measurable.comp (hV k).measurable).aestronglyMeasurable B
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hψB (V k x))
  have hzL (k : ℕ) : MemLp (z k) 2 (μ.restrict (U k)) :=
    (hψL k).sub ((Lp.memLp (SobolevSpace.toLp μ hQ (u k))).restrict (U k))
  have hzl : Tendsto (fun k => (μ.real (U k))⁻¹*∫ x in U k, (z k x)^2 ∂μ) atTop (𝓝 0) := by
    apply containing_mass_uniform_l2 (fun k => μ.restrict (U k)) (fun k => μ.real (U k)) hmass
      (fun k => by simp only [Measure.real,Measure.restrict_apply_univ]; exact le_rfl) z
      (fun k => (hzL k).aestronglyMeasurable)
    intro δ hδ
    exact (hconv δ hδ).mono fun k hk => hk.mono fun x hx => by
      simpa only [z,abs_sub_comm] using hx
  have hzero : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (U k), x∉Ω k → z k x=0 := by
    filter_upwards [hε.eventually (gt_mem_nhds (show 0<(T-d)/2 by linarith))] with k hk
    filter_upwards [ae_restrict_of_ae (huz k),ae_restrict_mem measurableSet_ball] with x hz hx hn
    have hu : SobolevSpace.toLp μ hQ (u k) x=0 := hz (fun hy => hn
      ((ball_subset_ball (mul_le_mul_of_nonneg_right hcT.le (hr k).le)) hy))
    have hdist : T≤dist x (p k)/r k := (le_div_iff₀ (hr k)).mpr (le_of_not_gt hn)
    have hd := (abs_le.mp (pointed_radial_distance (hr k) hS.le (hV k).metric hx.le)).1
    have hnorm : d<‖V k x‖ := by linarith
    have hψ0 : ψ (V k x)=0 := image_eq_zero_of_notMem_tsupport
      (fun hs => (lt_irrefl d) (lt_trans hnorm (by simpa only [mem_ball,dist_zero_right] using hψs hs)))
    change ψ (V k x)-SobolevSpace.toLp μ hQ (u k) x=0
    rw [hψ0,hu,sub_self]
  have he := supported_coefficient_l2_gamma_error μ hQ Ω U (fun _ => measurableSet_ball)
    (fun k => ball_subset_ball (mul_le_mul_of_nonneg_right hTS.le (hr k).le)) hmass
    r (fun k => (hr k).le) f w z hM hL hf hw hzero hzL hzl
  apply he.congr'
  filter_upwards [hconv 1 zero_lt_one] with k hk
  have hm : AEStronglyMeasurable (fun x => ψ (V k x)) (μ.restrict (U k)) :=
    (hψ.measurable.comp (hV k).measurable).aestronglyMeasurable
  have hi : IntegrableOn (fun x => ψ (V k x)*localGamma μ hQ (f k) (w k) x) (U k) μ :=
    (localGamma_memL1 μ hQ (f k) (w k)).restrict.bdd_mul hm
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hψB (V k x))
  have huB : ∀ᵐ x ∂μ.restrict (U k), ‖SobolevSpace.toLp μ hQ (u k) x‖≤B+1 := by
    filter_upwards [hk] with x hx
    rw [Real.norm_eq_abs]
    calc |SobolevSpace.toLp μ hQ (u k) x|
        = |(SobolevSpace.toLp μ hQ (u k) x-ψ (V k x))+ψ (V k x)| := by congr 1; ring
      _ ≤ |SobolevSpace.toLp μ hQ (u k) x-ψ (V k x)|+|ψ (V k x)| := abs_add_le _ _
      _ ≤ B+1 := by linarith [hψB (V k x)]
  have hj : IntegrableOn (fun x => SobolevSpace.toLp μ hQ (u k) x*localGamma μ hQ (f k) (w k) x) (U k) μ :=
    (localGamma_memL1 μ hQ (f k) (w k)).restrict.bdd_mul
      ((Lp.memLp (SobolevSpace.toLp μ hQ (u k))).restrict (U k)).aestronglyMeasurable huB
  change r k^2*(μ.real (U k))⁻¹*(∫ x in U k, z k x*localGamma μ hQ (f k) (w k) x ∂μ)=_
  simp only [z,sub_mul]
  rw [integral_sub hi hj]
  ring

end RegularPointCoordinates

end

end OAI
