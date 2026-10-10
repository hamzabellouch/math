import OAI.Analysis.CircleDomains.Uniformization.HeightTestLimit
import OAI.Analysis.CircleDomains.Sobolev.WeakPairEnergy
import OAI.Analysis.CircleDomains.Modulus.WeightedScalarTests
import OAI.Analysis.CircleDomains.Sobolev.CutoffEnergyAlgebra
import OAI.Analysis.CircleDomains.Topology.PlanarPairCalculus

namespace OAI

/-! Almost everywhere convergence of bounded continuous scalars and a
uniform global Dirichlet budget produce a global weak gradient. Compact
support is needed only for the test functions, not for a common support
of the approximating scalars. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakPartial_of_bounded_ae_pointwise_weak_limit
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (hu : ∀ n, Continuous (u n)) {C : ℝ}
    (hb : ∀ n x, ‖u n x‖ ≤ C)
    (hp : ∀ᵐ x ∂volume, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {i : Fin 2} {g : ℕ → EuclideanPlane → ℝ}
    (hw : ∀ n, DeGiorgi.HasWeakPartialDeriv i (g n) (u n) univ)
    (G : Lp ℝ 2 (volume : Measure EuclideanPlane))
    (hG : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ x, g n x*w x) atTop (𝓝 (∫ x, G x*w x))) :
    DeGiorgi.HasWeakPartialDeriv i G v univ := by
  intro φ hφ hs _
  simp only [Measure.restrict_univ]
  let ψ := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hψ : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsψ : HasCompactSupport ψ := hs.fderiv_apply (𝕜 := ℝ) _
  have hl : Tendsto (fun n => ∫ x, u n x*ψ x) atTop (𝓝 (∫ x, v x*ψ x)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun x => C*‖ψ x‖)
    · exact fun n => (hu n).aestronglyMeasurable.mul hψ.aestronglyMeasurable
    · exact (hψ.integrable_of_hasCompactSupport hsψ).norm.const_mul C
    · exact fun n => Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _)
    · exact hp.mono (fun x hx => hx.mul_const _)
  have hr := tendsto_pairings_with_memLp_test hG (hφ.continuous.memLp_of_hasCompactSupport hs)
  have he : (fun n => ∫ x, u n x*ψ x) = (fun n => -(∫ x, g n x*φ x)) := by
    funext n
    simpa only [Measure.restrict_univ] using hw n φ hφ hs (subset_univ _)
  rw [he] at hl
  exact tendsto_nhds_unique hl hr.neg

 theorem exists_bounded_energy_weak_gradient
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (W : ℕ → EuclideanPlane → EuclideanPlane)
    (hWL : ∀ n, MemLp (W n) 2 volume)
    (hW : ∀ n, DeGiorgi.HasWeakGrad (W n) (u n) univ)
    (hu : ∀ n, Continuous (u n)) {C : ℝ} (hb : ∀ n x, ‖u n x‖ ≤ C)
    (hp : ∀ᵐ x ∂volume, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {B : ℝ} (hB : ∀ n, (∫ x, ‖W n x‖^2) ≤ B) :
    ∃ g : EuclideanPlane → EuclideanPlane,
      MemLp g 2 volume ∧ DeGiorgi.HasWeakGrad g v univ ∧ (∫ x, ‖g x‖^2) ≤ B := by
  let u₀ := fun n x => W n x (0 : Fin 2)
  let u₁ := fun n x => W n x (1 : Fin 2)
  have hm₀ (n : ℕ) : MemLp (u₀ n) 2 volume := by
    exact memLp_piLp_iff.mp (hWL n) 0
  have hm₁ (n : ℕ) : MemLp (u₁ n) 2 volume := by
    exact memLp_piLp_iff.mp (hWL n) 1
  have he (n : ℕ) : (∫ x, u₀ n x^2+u₁ n x^2) ≤ B := by
    simpa only [plane_norm_sq] using hB n
  have hn (n : ℕ) : ‖(hm₀ n).toLp (u₀ n)‖ ≤ B+1 ∧ ‖(hm₁ n).toLp (u₁ n)‖ ≤ B+1 := by
    have h0 : ‖(hm₀ n).toLp (u₀ n)‖^2 = ∫ x, u₀ n x^2 := by
      rw [Lp.norm_toLp,integral_sq_eq_eLpNorm_toReal_sq (hm₀ n)]
    have h1 : ‖(hm₁ n).toLp (u₁ n)‖^2 = ∫ x, u₁ n x^2 := by
      rw [Lp.norm_toLp,integral_sq_eq_eLpNorm_toReal_sq (hm₁ n)]
    have hh := he n
    rw [integral_add (hm₀ n).integrable_sq (hm₁ n).integrable_sq,← h0,← h1] at hh
    constructor <;> nlinarith [sq_nonneg (‖(hm₀ n).toLp (u₀ n)‖-1),
      sq_nonneg (‖(hm₁ n).toLp (u₁ n)‖-1),sq_nonneg ‖(hm₀ n).toLp (u₀ n)‖,
      sq_nonneg ‖(hm₁ n).toLp (u₁ n)‖]
  obtain ⟨G₀,_,s,hs,h0⟩ := exists_L2_weak_subsequence volume u₀ hm₀ (B+1) (fun n => (hn n).1)
  obtain ⟨G₁,_,t,ht,h1⟩ := exists_L2_weak_subsequence volume (u₁ ∘ s)
    (fun n => hm₁ (s n)) (B+1) (fun n => (hn (s n)).2)
  let σ := s ∘ t
  have hσ : StrictMono σ := hs.comp ht
  have h0' (w : Lp ℝ 2 (volume : Measure EuclideanPlane)) := (h0 w).comp ht.tendsto_atTop
  let g : EuclideanPlane → EuclideanPlane := fun x => planePair (G₀ x) (G₁ x)
  refine ⟨g,?_,?_,?_⟩
  · apply memLp_piLp_iff.mpr
    intro i
    fin_cases i
    · change MemLp (fun x => planePair (G₀ x) (G₁ x) 0) 2 volume
      simpa only [planePair_zero] using Lp.memLp G₀
    · change MemLp (fun x => planePair (G₀ x) (G₁ x) 1) 2 volume
      simpa only [planePair_one] using Lp.memLp G₁
  · intro i
    fin_cases i
    · change DeGiorgi.HasWeakPartialDeriv 0 (fun x => planePair (G₀ x) (G₁ x) 0) v univ
      simpa only [planePair_zero] using weakPartial_of_bounded_ae_pointwise_weak_limit (fun n => hu (σ n))
        (fun n => hb (σ n)) (hp.mono (fun _ hx => hx.comp hσ.tendsto_atTop))
        (fun n => hW (σ n) 0) G₀ h0'
    · change DeGiorgi.HasWeakPartialDeriv 1 (fun x => planePair (G₀ x) (G₁ x) 1) v univ
      simpa only [planePair_one] using weakPartial_of_bounded_ae_pointwise_weak_limit (fun n => hu (σ n))
        (fun n => hb (σ n)) (hp.mono (fun _ hx => hx.comp hσ.tendsto_atTop))
        (fun n => hW (σ n) 1) G₁ h1
  · have hh := paired_L2_energy_le (fun n => hm₀ (σ n)) (fun n => hm₁ (σ n)) G₀ G₁
      (ε := fun _ => 0) tendsto_const_nhds
      (Eventually.of_forall (fun n => by simpa only [add_zero] using he (σ n)))
      (h0' G₀) (h1 G₁)
    simpa only [g,plane_norm_sq,planePair_zero,planePair_one] using hh

 theorem exists_bounded_energy_weak_closure
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (W : ∀ n, DeGiorgi.MemW1pWitness 2 (u n) univ)
    (hu : ∀ n, Continuous (u n)) {C : ℝ} (hb : ∀ n x, ‖u n x‖ ≤ C)
    (hp : ∀ᵐ x ∂volume, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {B : ℝ} (hB : ∀ n, (∫ x, ‖(W n).weakGrad x‖^2) ≤ B) :
    ∃ g : EuclideanPlane → EuclideanPlane,
      MemLp g 2 volume ∧ DeGiorgi.HasWeakGrad g v univ ∧ (∫ x, ‖g x‖^2) ≤ B := by
  exact exists_bounded_energy_weak_gradient (fun n => (W n).weakGrad)
    (fun n => by simpa only [Measure.restrict_univ] using (W n).weakGrad_memLp)
    (fun n => (W n).isWeakGrad) hu hb hp hB

end CircleDomainRigidity

end

end OAI
