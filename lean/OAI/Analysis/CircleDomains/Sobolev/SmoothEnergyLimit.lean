import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneSobolev
import OAI.Analysis.CircleDomains.Sobolev.WeakPairEnergy
import Mathlib.Topology.Order.LiminfLimsup

namespace OAI

/-! A locally bounded pointwise limit of smooth functions with convergent
Dirichlet energies has a Sobolev witness with no greater energy. This is
used for the actual mollifications transported by the conformal inverse. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_energy_limit
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : EuclideanPlane → ℝ} (hu : MemLp u 2 (volume.restrict U))
    (v : ℕ → EuclideanPlane → ℝ)
    (hv : ∀ n, ContDiffOn ℝ 1 (v n) U)
    (hgrad : ∀ n i, MemLp (fun x => fderiv ℝ (v n) x (EuclideanSpace.single i 1))
      2 (volume.restrict U))
    {C : ℝ} (hb : ∀ n x, x ∈ U → ‖v n x‖ ≤ C)
    (hp : ∀ x ∈ U, Tendsto (fun n => v n x) atTop (𝓝 (u x)))
    {B : ℝ} (henergy : Tendsto (fun n => ∫ x in U,
      (fderiv ℝ (v n) x (EuclideanSpace.single 0 1)) ^ 2 +
      (fderiv ℝ (v n) x (EuclideanSpace.single 1 1)) ^ 2) atTop (𝓝 B)) :
    ∃ H : DeGiorgi.MemW1pWitness 2 u U,
      (∫ x in U, H.weakGrad x 0 ^ 2 + H.weakGrad x 1 ^ 2) ≤ B := by
  let μ := volume.restrict U
  let g (i : Fin 2) (n : ℕ) (x : EuclideanPlane) :=
    fderiv ℝ (v n) x (EuclideanSpace.single i 1)
  let e (n : ℕ) := ∫ x, g 0 n x ^ 2 + g 1 n x ^ 2 ∂μ
  change Tendsto e atTop (𝓝 B) at henergy
  obtain ⟨M, hM⟩ := henergy.bddAbove_range
  have hMe (n : ℕ) : e n ≤ M := hM (mem_range_self n)
  have hnorm (n : ℕ) (i : Fin 2) : ‖(hgrad n i).toLp (g i n)‖ ≤ M + 1 := by
    have he (j : Fin 2) : (∫ x, g j n x ^ 2 ∂μ) = ‖(hgrad n j).toLp (g j n)‖ ^ 2 := by
      rw [Lp.norm_toLp, integral_sq_eq_eLpNorm_toReal_sq (hgrad n j)]
    have hm := hMe n
    dsimp only [e] at hm
    rw [integral_add (hgrad n 0).integrable_sq (hgrad n 1).integrable_sq, he, he] at hm
    fin_cases i
    · change ‖(hgrad n 0).toLp (g 0 n)‖ ≤ M + 1
      nlinarith [sq_nonneg (‖(hgrad n 0).toLp (g 0 n)‖ - 1),
        sq_nonneg ‖(hgrad n 1).toLp (g 1 n)‖]
    · change ‖(hgrad n 1).toLp (g 1 n)‖ ≤ M + 1
      nlinarith [sq_nonneg (‖(hgrad n 1).toLp (g 1 n)‖ - 1),
        sq_nonneg ‖(hgrad n 0).toLp (g 0 n)‖]
  obtain ⟨G₀, _, s₀, hs₀, hl₀⟩ := exists_L2_weak_subsequence μ (g 0)
    (fun n => hgrad n 0) (M + 1) (fun n => hnorm n 0)
  obtain ⟨G₁, _, s₁, hs₁, hl₁⟩ := exists_L2_weak_subsequence μ (g 1 ∘ s₀)
    (fun n => hgrad (s₀ n) 1) (M + 1) (fun n => hnorm (s₀ n) 1)
  let σ := s₀ ∘ s₁
  have hσ : Tendsto σ atTop atTop := hs₀.tendsto_atTop.comp hs₁.tendsto_atTop
  have hpair₀ (w : Lp ℝ 2 μ) :
      Tendsto (fun n => ∫ x, g 0 (σ n) x * w x ∂μ) atTop (𝓝 (∫ x, G₀ x * w x ∂μ)) :=
    (hl₀ w).comp hs₁.tendsto_atTop
  have hweak (i : Fin 2) (G : Lp ℝ 2 μ)
      (hl : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, g i (σ n) x * w x ∂μ)
        atTop (𝓝 (∫ x, G x * w x ∂μ))) :
      DeGiorgi.HasWeakPartialDeriv i G u U := by
    intro φ hφ hs hsub
    let ψ (x : EuclideanPlane) := fderiv ℝ φ x (EuclideanSpace.single i 1)
    have hψ : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsψ : HasCompactSupport ψ := hs.fderiv_apply (𝕜 := ℝ) _
    have hleft : Tendsto (fun n => ∫ x, v (σ n) x * ψ x ∂μ) atTop
        (𝓝 (∫ x, u x * ψ x ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (bound := fun x => C * ‖ψ x‖)
      · intro n
        exact ((hv (σ n)).continuousOn.aestronglyMeasurable hU.measurableSet).mul
          hψ.aestronglyMeasurable
      · exact ((hψ.integrable_of_hasCompactSupport hsψ).restrict (s := U)).norm.const_mul C
      · intro n
        filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb (σ n) x hx) (norm_nonneg _)
      · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        exact ((hp x hx).comp hσ).mul_const (ψ x)
    have hφL : MemLp φ 2 μ := (hφ.continuous.memLp_of_hasCompactSupport hs).restrict U
    have he (f : EuclideanPlane → ℝ) :
        (∫ x, f x * hφL.toLp φ x ∂μ) = ∫ x, f x * φ x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hφL.coeFn_toLp] with x hx
      rw [hx]
    have hright := hl (hφL.toLp φ)
    simp only [he] at hright
    have hboth : ∀ n, (∫ x, v (σ n) x * ψ x ∂μ) = -(∫ x, g i (σ n) x * φ x ∂μ) :=
      fun n => weakPartial_of_smooth_on hU (hv (σ n)) i φ hφ hs hsub
    rw [show (fun n => ∫ x, v (σ n) x * ψ x ∂μ) =
      (fun n => -(∫ x, g i (σ n) x * φ x ∂μ)) from funext hboth] at hleft
    exact tendsto_nhds_unique hleft hright.neg
  let H : DeGiorgi.MemW1pWitness 2 u U := {
    memLp := hu
    weakGrad := fun x => WithLp.toLp 2 (fun i => if i = 0 then G₀ x else G₁ x)
    weakGrad_component_memLp := by
      intro i
      fin_cases i
      · exact Lp.memLp G₀
      · exact Lp.memLp G₁
    isWeakGrad := by
      intro i
      fin_cases i
      · exact hweak 0 G₀ hpair₀
      · exact hweak 1 G₁ hl₁ }
  refine ⟨H, ?_⟩
  change (∫ x, G₀ x ^ 2 + G₁ x ^ 2 ∂μ) ≤ B
  apply paired_L2_energy_le (fun n => hgrad (σ n) 0) (fun n => hgrad (σ n) 1)
    G₀ G₁ (ε := fun n => e (σ n) - B)
  · simpa only [Function.comp_def, sub_self] using (henergy.comp hσ).sub_const B
  · exact Eventually.of_forall fun n => le_of_eq (by dsimp [e]; ring)
  · exact hpair₀ G₀
  · exact hl₁ G₁

end CircleDomainRigidity

end

end OAI
