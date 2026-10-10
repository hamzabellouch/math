import Mathlib
import OAI.Analysis.Conductivity.Variational.ContDiffClmDet
import OAI.Analysis.Conductivity.Sobolev.LocalPiolaFluxPotentialPairing
import OAI.Analysis.Conductivity.Variational.AdaptedSpatialBasis

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

lemma localPiolaFlux_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (F G : E → E) :
    localPiolaFlux X (fun x => F x - G x) =
      fun x => localPiolaFlux X F x - localPiolaFlux X G x := by
  classical
  funext x
  by_cases hx : x ∈ X.target <;> simp [localPiolaFlux, hx, map_sub, smul_sub]

lemma localPiolaFlux_linear_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ X.source) :
    ∃ B : ℝ, 0 < B ∧ ∀ (F : E → E), Function.support F ⊆ K → ∀ y,
      ‖localPiolaFlux X F y‖ ≤ B * ‖F (X.symm y)‖ := by
  classical
  let T : E → E →L[ℝ] E := fun x => |(fderiv ℝ X x).det|⁻¹ • fderiv ℝ X x
  have hT : ContinuousOn T X.source := by
    intro x hx
    have hd : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fderiv ℝ X) x :=
      (hX.contDiffAt (X.open_source.mem_nhds hx)).fderiv_right (by simp)
    have hdet0 := local_fderiv_det_ne_zero X (hX.differentiableOn (by simp))
      (hXi.differentiableOn (by simp)) hx
    have hdet := ((contDiff_clm_det (E := E) (↑(⊤ : ℕ∞))).contDiffAt.comp x hd).abs hdet0
    exact ((hdet.inv (abs_ne_zero.mpr hdet0)).smul hd).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn (hT.mono hKs)).isBounded.exists_norm_le
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro F hF y
  by_cases hy : y ∈ X.target
  · by_cases hxy : X.symm y ∈ K
    · change ‖(if y ∈ X.target then _ else 0)‖ ≤ _
      simp only [ite_eq_left hy]
      change ‖T (X.symm y) (F (X.symm y))‖ ≤ _
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right ((hC _ (mem_image_of_mem _ hxy)).trans (le_max_left _ _))
          (norm_nonneg _))
    · have hz : F (X.symm y) = 0 := by
        by_contra hn
        exact hxy (hF hn)
      simp [localPiolaFlux, hy, hz]
  · simp [localPiolaFlux, hy, mul_nonneg (le_trans zero_le_one (le_max_right C 1))
      (norm_nonneg (F (X.symm y)))]

lemma localPiolaFlux_uniform_error
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {l : Filter I}
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ X.source)
    (F G : I → E → E) (hs : ∀ i, Function.support (fun x => F i x - G i x) ⊆ K)
    (he : TendstoUniformly (fun i x => F i x - G i x) (fun _ => 0) l) :
    TendstoUniformly (fun i x => localPiolaFlux X (F i) x - localPiolaFlux X (G i) x)
      (fun _ => 0) l := by
  obtain ⟨B, hB, hb⟩ := localPiolaFlux_linear_bound X hX hXi hK hKs
  rw [Metric.tendstoUniformly_iff] at he ⊢
  intro ε hε
  filter_upwards [he (ε / B) (div_pos hε hB)] with i hi x
  have hix : ‖F i (X.symm x) - G i (X.symm x)‖ < ε / B := by
    simpa only [dist_zero_left] using hi (X.symm x)
  have hii := hb (fun y => F i y - G i y) (hs i) x
  rw [localPiolaFlux_sub] at hii
  simpa only [dist_zero_left] using hii.trans_lt ((lt_div_iff₀' hB).mp hix)

theorem exists_chart_two_flux
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
      (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ X.source) ∧
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
    exact ⟨localPiolaFlux_hasCompactSupport X.symm _ (hc k j) (hgs k j),
      localPiolaFlux_tsupport X.symm _ (hc k j) (hgs k j)⟩
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

end ScalarConductivity

end

end OAI
