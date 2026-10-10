import Mathlib
import OAI.Analysis.Conductivity.Sobolev.LocalPiolaFluxSub
import OAI.Analysis.Conductivity.Geometry.InverseChartPiolaOperator
import OAI.Analysis.Conductivity.Sobolev.LocalPullback

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

theorem exists_chart_two_flux_localized
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (D : E →L[ℝ] (Fin 2 → ℝ)) (hD : Function.Surjective D)
    (u : E → Fin 2 → ℝ) (hu : ∀ y ∈ X.source, D (X y) = u y)
    (χ : SmoothScalar E) (hχ : HasCompactSupport χ.val) (hχs : tsupport χ.val ⊆ X.target)
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (h : SmoothScalar ℝ) (hp : Function.Periodic h.val 1)
    (hm : ∫ t in (0 : ℝ)..1, h.val t = 0)
    (R : Fin 2 → E) (hRs : D (R 0) 1 = D (R 1) 0) (hRn : ∀ j, L (R j) = 0) :
    ∃ F : ℝ → Fin 2 → E → E,
      (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
      (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ X.source ∧
        tsupport (F k j) ⊆ X.symm '' tsupport χ.val) ∧
      (∀ k y, fderiv ℝ u y (F k 0 y) 1 = fderiv ℝ u y (F k 1 y) 0) ∧
      (∀ k j (ψ : E → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
        (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
      ∀ j, TendstoUniformly
        (fun k y => F k j y - localPiolaFlux X.symm
          (fun x => (χ.val x * h.val (k * L x)) • R j) y) (fun _ => 0) atTop := by
  classical
  obtain ⟨G, hg, hs, hsym, hdiv, he⟩ := exists_physical_two_flux hdim μ D hD
    χ hχ L hL h hp hm R hRs hRn
  have hc (k : ℝ) (j : Fin 2) : HasCompactSupport (G k j) :=
    hχ.of_isClosed_subset (isClosed_tsupport _) (hs k j)
  have hgs (k : ℝ) (j : Fin 2) : tsupport (G k j) ⊆ X.target := (hs k j).trans hχs
  refine ⟨fun k j => localPiolaFlux X.symm (G k j), ?_, ?_, ?_, ?_, ?_⟩
  · intro k j
    exact localPiolaFlux_smooth X.symm hXi hX (G k j) (hg k j) (hc k j) (hgs k j)
  · intro k j
    refine ⟨localPiolaFlux_hasCompactSupport X.symm _ (hc k j) (hgs k j),
      localPiolaFlux_tsupport X.symm _ (hc k j) (hgs k j), ?_⟩
    apply closure_minimal
      ((localPiolaFlux_support X.symm (G k j)).trans
        (image_mono (fun _ hx => hs k j (subset_closure hx.1))))
      ((hχ.image_of_continuousOn (X.symm.continuousOn.mono hχs)).isClosed)
  · intro k y
    by_cases hy : y ∈ X.source
    · rw [localPiolaFlux_potential_pairing X (hX.differentiableOn (by simp))
        (hXi.differentiableOn (by simp)) D u hu (G k 0) hy,
        localPiolaFlux_potential_pairing X (hX.differentiableOn (by simp))
        (hXi.differentiableOn (by simp)) D u hu (G k 1) hy]
      simp only [Pi.smul_apply, smul_eq_mul, hsym]
    · simp [localPiolaFlux, hy]
  · intro k j ψ hψ
    exact localPiolaFlux_zero_pairing μ X.symm hXi hX _ (hc k j) (hgs k j) (hdiv k j) ψ hψ
  · intro j
    apply localPiolaFlux_uniform_error X.symm hXi hX hχ hχs
      (fun k => G k j) (fun k x => (χ.val x * h.val (k * L x)) • R j) _ (he j)
    intro k x hx
    by_contra hn
    have hz : χ.val x = 0 := image_eq_zero_of_notMem_tsupport hn
    have hgz : G k j x = 0 := image_eq_zero_of_notMem_tsupport (fun hx => hn (hs k j hx))
    apply hx
    simp [hz, hgz]

theorem exists_frozen_chart_two_flux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (D : E →L[ℝ] (Fin 2 → ℝ)) (hD : Function.Surjective D)
    (u : E → Fin 2 → ℝ) (hu : ∀ y ∈ X.source, D (X y) = u y)
    {a : E} (ha : a ∈ X.source) (hDa : fderiv ℝ X a = ContinuousLinearMap.id ℝ E)
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (R : Fin 2 → E) (hRs : D (R 0) 1 = D (R 1) 0) (hRn : ∀ j, L (R j) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ X.source ∧
      ∀ h : SmoothScalar ℝ, Function.Periodic h.val 1 →
        (∫ t in (0 : ℝ)..1, h.val t = 0) → (∀ t, |h.val t| ≤ 1) →
      ∀ χ : SmoothScalar E, HasCompactSupport χ.val → tsupport χ.val ⊆ X '' V →
        (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) →
        ∃ F : ℝ → Fin 2 → E → E,
          (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
          (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ V ∧
            tsupport (F k j) ⊆ X.symm '' tsupport χ.val) ∧
          (∀ k y, fderiv ℝ u y (F k 0 y) 1 = fderiv ℝ u y (F k 1 y) 0) ∧
          (∀ k j (ψ : E → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
            (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
          ∀ᶠ k : ℝ in atTop, ∀ j y,
            ‖F k j y - (localPullback X χ.val y * h.val (k * L (X y))) • R j‖ < ε := by
  let B := ‖R 0‖ + ‖R 1‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hR : ∀ j, ‖R j‖ ≤ B := by
    intro j
    fin_cases j <;> dsimp [B] <;> linarith only [norm_nonneg (R 0), norm_nonneg (R 1)]
  obtain ⟨V, hV, haV, hVs, hfreeze⟩ := inverseChartPiola_freezing X hX hXi ha hDa
    (div_pos (half_pos hε) hB)
  refine ⟨V, hV, haV, hVs, ?_⟩
  intro h hp hm hb χ hχ hχV hχb
  have hχs : tsupport χ.val ⊆ X.target := by
    rintro z hz
    obtain ⟨y, hy, rfl⟩ := hχV hz
    exact X.map_source (hVs hy)
  obtain ⟨F, hF, hFs, hsym, hdiv, he⟩ := exists_chart_two_flux_localized hdim μ X hX hXi
    D hD u hu χ hχ hχs L hL h hp hm R hRs hRn
  have hFi : ∀ k j, tsupport (F k j) ⊆ V := by
    intro k j y hy
    obtain ⟨z, hz, rfl⟩ := (hFs k j).2.2 hy
    obtain ⟨w, hw, rfl⟩ := hχV hz
    simpa only [X.left_inv (hVs hw)] using hw
  have hχi : tsupport (localPullback X χ.val) ⊆ V := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (localPullback_tsupport X χ.val hχ hχs).2.1 hy
    obtain ⟨w, hw, rfl⟩ := hχV hz
    simpa only [X.left_inv (hVs hw)] using hw
  refine ⟨F, hF, fun k j => ⟨(hFs k j).1, hFi k j, (hFs k j).2.2⟩, hsym, hdiv, ?_⟩
  have herr : ∀ᶠ k : ℝ in atTop, ∀ j y,
      ‖F k j y - localPiolaFlux X.symm
        (fun z => (χ.val z * h.val (k * L z)) • R j) y‖ < ε / 2 := by
    apply Filter.eventually_all.mpr
    intro j
    simpa only [dist_zero_left] using (Metric.tendstoUniformly_iff.mp (he j)) _ (half_pos hε)
  filter_upwards [herr] with k hk j y
  by_cases hy : y ∈ V
  · have hfr := hfreeze (localPullback X χ.val) (fun z => h.val (k * L z)) (R j) y hy
    have hpre : localPiolaFlux X.symm
        (fun z => (localPullback X χ.val (X.symm z) * h.val (k * L z)) • R j) y =
        localPiolaFlux X.symm (fun z => (χ.val z * h.val (k * L z)) • R j) y := by
      rw [localPiolaFlux_inverse_eq X _ (hVs hy), localPiolaFlux_inverse_eq X _ (hVs hy),
        localPullback_comp X _ (X.map_source (hVs hy))]
    rw [hpre] at hfr
    have hcb := localPullback_bounds X χ.val hχb y
    have habs : |localPullback X χ.val y * h.val (k * L (X y))| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hcb.1]
      exact (mul_le_mul_of_nonneg_left (hb _) hcb.1).trans (by simpa using hcb.2)
    have hnorm : |localPullback X χ.val y * h.val (k * L (X y))| * ‖R j‖ ≤ B :=
      (mul_le_mul_of_nonneg_right habs (norm_nonneg _)).trans (by simpa using hR j)
    have hsmall : ‖localPiolaFlux X.symm
        (fun z => (χ.val z * h.val (k * L z)) • R j) y -
          (localPullback X χ.val y * h.val (k * L (X y))) • R j‖ ≤ ε / 2 :=
      hfr.trans ((mul_le_mul_of_nonneg_left hnorm (div_pos (half_pos hε) hB).le).trans
        (le_of_eq (div_mul_cancel₀ _ hB.ne')))
    exact (norm_sub_le_norm_sub_add_norm_sub (F k j y) _ _).trans_lt (by linarith only [hk j y, hsmall])
  · have hFz : F k j y = 0 := image_eq_zero_of_notMem_tsupport (fun hz => hy (hFi k j hz))
    have hχz : localPullback X χ.val y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hz => hy (hχi hz))
    simpa only [hFz, hχz, zero_mul, zero_smul, sub_zero, norm_zero] using hε

end ScalarConductivity

end

end OAI
