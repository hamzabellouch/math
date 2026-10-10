import OAI.Analysis.CircleDomains.Sobolev.PositiveSobolevApproximation
import OAI.Analysis.CircleDomains.Sobolev.SphericalGradientEnergyNorm

namespace OAI

/-! Strong mollification converges in Dirichlet energy on every measurable
source region. The limiting energy is that of the original weak field. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem integral_sq_tendsto_of_L2
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {v : ℕ → X → ℝ} {g : X → ℝ}
    (hv : ∀ n, MemLp (v n) 2 μ) (hg : MemLp g 2 μ)
    (hl : Tendsto (fun n => eLpNorm (fun x => v n x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, v n x ^ 2 ∂μ) atTop (𝓝 (∫ x, g x ^ 2 ∂μ)) := by
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv g hg).mpr hl
  have hn := ht.norm.pow 2
  have he (f : X → ℝ) (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [Lp.norm_toLp, integral_sq_eq_eLpNorm_toReal_sq hf]
  simpa only [he] using hn

 theorem planarMollification_partial_memLp
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u univ)
    (hs : HasCompactSupport u) (n : ℕ) (i : Fin 2) :
    MemLp (fun x => fderiv ℝ (planarMollification u n) x (EuclideanSpace.single i 1))
      2 volume := by
  have hL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp
  exact ((planarMollification_smooth (hL.locallyIntegrable (by norm_num)) n).continuous_fderiv
    (by simp)).clm_apply continuous_const |>.memLp_of_hasCompactSupport
      ((planarMollification_hasCompactSupport hs n).fderiv_apply (𝕜 := ℝ) _)

 theorem planarMollification_energy_tendsto
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u univ)
    (hs : HasCompactSupport u) (U : Set EuclideanPlane) :
    Tendsto (fun n => ∫ x in U,
      (fderiv ℝ (planarMollification u n) x (EuclideanSpace.single 0 1)) ^ 2 +
      (fderiv ℝ (planarMollification u n) x (EuclideanSpace.single 1 1)) ^ 2)
      atTop (𝓝 (∫ x in U, hu.weakGrad x 0 ^ 2 + hu.weakGrad x 1 ^ 2)) := by
  have hg (i : Fin 2) : MemLp (fun x => hu.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hu.weakGrad_component_memLp i
  have hl (i : Fin 2) : Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (planarMollification u n) x (EuclideanSpace.single i 1) - hu.weakGrad x i)
      2 (volume.restrict U)) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (planarMollification_tendsto_gradient_L2 hu i)
      (fun _ => bot_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have ht (i : Fin 2) := integral_sq_tendsto_of_L2
    (fun n => (planarMollification_partial_memLp hu hs n i).restrict U)
    ((hg i).restrict U) (hl i)
  have hh := (ht 0).add (ht 1)
  simpa only [← integral_add ((hg 0).restrict U).integrable_sq ((hg 1).restrict U).integrable_sq,
    ← integral_add ((planarMollification_partial_memLp hu hs _ 0).restrict U).integrable_sq
      ((planarMollification_partial_memLp hu hs _ 1).restrict U).integrable_sq] using hh

end CircleDomainRigidity

end

end OAI
