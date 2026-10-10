import OAI.Analysis.CircleDomains.Uniformization.HeightTestLimit
import OAI.Analysis.CircleDomains.Modulus.WeightedScalarTests
import OAI.Analysis.CircleDomains.Sobolev.WeakPairEnergy

namespace OAI

/-! Weak L2 pairings identify derivatives of bounded pointwise limits.
The same pairings retain localized energy estimates on measurable sets. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma weakPartial_of_bounded_pointwise_weak_limit
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (hu : ∀ n, Continuous (u n))
    {C : ℝ} (hb : ∀ n x, ‖u n x‖ ≤ C)
    (hp : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {g : ℕ → EuclideanPlane → ℝ} {G : EuclideanPlane → ℝ} {i : Fin 2}
    (hw : ∀ n, DeGiorgi.HasWeakPartialDeriv i (g n) (u n) univ)
    (hl : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ x, g n x*w x) atTop (𝓝 (∫ x, G x*w x))) :
    DeGiorgi.HasWeakPartialDeriv i G v univ := by
  intro φ hφ hs _
  simp only [Measure.restrict_univ]
  let ψ (x : EuclideanPlane) := fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hψ : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsψ : HasCompactSupport ψ := hs.fderiv_apply (𝕜 := ℝ) _
  have ht := height_test_integral_tendsto u hu hp
    (fun _ _ => ⟨C, fun n x _ => hb n x⟩) hψ hsψ
  have hg := tendsto_pairings_with_memLp_test hl
    (hφ.continuous.memLp_of_hasCompactSupport hs (p := 2) (μ := volume))
  have he (n : ℕ) : (∫ x, u n x*ψ x) = -(∫ x, g n x*φ x) := by
    simpa only [Measure.restrict_univ] using hw n φ hφ hs (subset_univ _)
  exact tendsto_nhds_unique (ht.congr' (.of_forall he)) hg.neg

lemma weak_pairings_restrict
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : ℕ → X → ℝ} {G : X → ℝ}
    (hl : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, u n x*w x ∂μ)
      atTop (𝓝 (∫ x, G x*w x ∂μ)))
    {A : Set X} (hA : MeasurableSet A) {w : X → ℝ} (hw : MemLp w 2 μ) :
    Tendsto (fun n => ∫ x in A, u n x*w x ∂μ) atTop
      (𝓝 (∫ x in A, G x*w x ∂μ)) := by
  have ht := tendsto_pairings_with_memLp_test hl (hw.indicator hA)
  have he (f : X → ℝ) : (∫ x, f x*A.indicator w x ∂μ) = ∫ x in A, f x*w x ∂μ := by
    rw [← integral_indicator hA]
    congr 1
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  simpa only [he] using ht

lemma weak_pair_energy_restrict_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u₀ u₁ : ℕ → X → ℝ} (hu₀ : ∀ n, MemLp (u₀ n) 2 μ)
    (hu₁ : ∀ n, MemLp (u₁ n) 2 μ) (G₀ G₁ : X → ℝ)
    (hm₀ : MemLp G₀ 2 μ) (hm₁ : MemLp G₁ 2 μ)
    (hl₀ : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, u₀ n x*w x ∂μ)
      atTop (𝓝 (∫ x, G₀ x*w x ∂μ)))
    (hl₁ : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, u₁ n x*w x ∂μ)
      atTop (𝓝 (∫ x, G₁ x*w x ∂μ)))
    {A : Set X} (hA : MeasurableSet A) {B : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, (∫ x in A, (u₀ n x)^2+(u₁ n x)^2 ∂μ) ≤ B+ε n) :
    (∫ x in A, (G₀ x)^2+(G₁ x)^2 ∂μ) ≤ B := by
  let hG₀ := hm₀.restrict A
  let hG₁ := hm₁.restrict A
  have he₀ := hG₀.coeFn_toLp
  have he₁ := hG₁.coeFn_toLp
  have hp₀ := weak_pairings_restrict hl₀ hA hm₀
  have hp₁ := weak_pairings_restrict hl₁ hA hm₁
  have ht₀ : Tendsto (fun n => ∫ x in A, u₀ n x*hG₀.toLp G₀ x ∂μ) atTop
      (𝓝 (∫ x in A, hG₀.toLp G₀ x*hG₀.toLp G₀ x ∂μ)) := by
    convert hp₀ using 1
    · funext n
      exact integral_congr_ae (he₀.mono fun x hx => by dsimp only; rw [hx])
    · exact congrArg (𝓝 : ℝ → Filter ℝ) (integral_congr_ae (he₀.mono fun x hx => by dsimp only; rw [hx]))
  have ht₁ : Tendsto (fun n => ∫ x in A, u₁ n x*hG₁.toLp G₁ x ∂μ) atTop
      (𝓝 (∫ x in A, hG₁.toLp G₁ x*hG₁.toLp G₁ x ∂μ)) := by
    convert hp₁ using 1
    · funext n
      exact integral_congr_ae (he₁.mono fun x hx => by dsimp only; rw [hx])
    · exact congrArg (𝓝 : ℝ → Filter ℝ) (integral_congr_ae (he₁.mono fun x hx => by dsimp only; rw [hx]))
  have h := paired_L2_energy_le (fun n => (hu₀ n).restrict A)
    (fun n => (hu₁ n).restrict A) (hG₀.toLp G₀) (hG₁.toLp G₁) hε hb ht₀ ht₁
  convert h using 1
  apply integral_congr_ae
  filter_upwards [he₀, he₁] with x hx hy
  rw [hx, hy]

end CircleDomainRigidity

end

end OAI
