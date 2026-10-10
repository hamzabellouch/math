import Mathlib
import OAI.Analysis.Conductivity.Variational.DerivativeEquiv
import OAI.Analysis.Conductivity.Variational.ContDiffClmDet

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
open Set MeasureTheory Filter Topology

lemma piolaFlux_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Y : E ≃ E)
    (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y) (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    (F : E → E) (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (piolaFlux Y F) := by
  rw [contDiff_iff_contDiffAt]; intro x
  have hd := (hY.contDiffAt.fderiv_right (by simp)).comp x hi.contDiffAt
  have hn := fderiv_equiv_det_ne_zero Y (hY.differentiable (by simp))
    (hi.differentiable (by simp)) (Y.symm x)
  have hdet := ((contDiff_clm_det (E := E) (↑(⊤ : ℕ∞))).contDiffAt.comp x hd).abs hn
  exact (hdet.inv (abs_ne_zero.mpr hn)).smul (hd.clm_apply (hF.contDiffAt.comp x hi.contDiffAt))

lemma equiv_symm_eq_off {E : Type*} (Y : E ≃ E) {K : Set E}
    (hY : ∀ x ∉ K, Y x = x) : ∀ x ∉ K, Y.symm x = x := by
  intro x hx
  exact Y.symm_apply_eq.mpr (hY x hx).symm

lemma fderiv_equiv_eq_id_off {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : E ≃ E) {K : Set E} (hK : IsClosed K) (hY : ∀ x ∉ K, Y x = x)
    {x : E} (hx : x ∉ K) : fderiv ℝ Y x = ContinuousLinearMap.id ℝ E := by
  have he : Y =ᶠ[𝓝 x] id := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact hY y hy
  rw [he.fderiv_eq]
  exact fderiv_id

lemma tsupport_comp_equiv_sub {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddGroup V] [TopologicalSpace V] (Y : E ≃ E) {K : Set E} (hK : IsClosed K)
    (hY : ∀ x ∉ K, Y x = x) (f : E → V) : tsupport (fun x => f (Y x)-f x) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  exact hx (by change f (Y x)-f x=0; rw [hY x hn, sub_self])

lemma piolaFlux_eq_off {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Y : E ≃ E) {K : Set E} (hK : IsClosed K)
    (hY : ∀ x ∉ K, Y x = x) (F : E → E) {x : E} (hx : x ∉ K) :
    piolaFlux Y F x = F x := by
  rw [piolaFlux, equiv_symm_eq_off Y hY x hx, fderiv_equiv_eq_id_off Y hK hY hx]
  change |(LinearMap.id : E →ₗ[ℝ] E).det|⁻¹ • F x = F x
  simp

lemma smooth_flux_integrable_pairing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] (F : E → E)
    (hF : Continuous F) (hc : HasCompactSupport F) (ψ : E → ℝ)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) :
    Integrable (fun x => fderiv ℝ ψ x (F x)) μ := by
  apply (hψ.continuous_fderiv (by simp) |>.clm_apply hF).integrable_of_hasCompactSupport
  apply hc.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  rw [hx, map_zero]

theorem compact_piola_Cauchy_difference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (Y : E ≃ E)
    (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y) (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    {K U : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (hoff : ∀ x ∉ K, Y x = x)
    (F : E → E) (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (hc : HasCompactSupport F)
    (hdiv : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => piolaFlux Y F x - F x) ∧
    HasCompactSupport (fun x => piolaFlux Y F x - F x) ∧
    tsupport (fun x => piolaFlux Y F x - F x) ⊆ K ∧
    ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (piolaFlux Y F x - F x) ∂μ) = 0 := by
  have hG := piolaFlux_contDiff Y hY hi F hF
  have hGc := piolaFlux_hasCompactSupport Y (hY.differentiable (by simp))
    (hi.differentiable (by simp)) F hc
  have hs : tsupport (fun x => piolaFlux Y F x - F x) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (by change piolaFlux Y F x - F x = 0
                 rw [piolaFlux_eq_off Y hK.isClosed hoff F hn, sub_self])
  refine ⟨hG.sub hF, hK.of_isClosed_subset isClosed_closure hs, hs, ?_⟩
  intro ψ hψ
  have hψY := hψ.comp hY
  have htest := tsupport_comp_equiv_sub Y hK.isClosed hoff ψ
  have hz := hdiv (fun x => ψ (Y x)-ψ x) (hψY.sub hψ)
    (hK.of_isClosed_subset isClosed_closure htest) (htest.trans hKU)
  have h1 := smooth_flux_integrable_pairing μ F hF.continuous hc ψ hψ
  have h2 := smooth_flux_integrable_pairing μ F hF.continuous hc (ψ ∘ Y) hψY
  have h3 := smooth_flux_integrable_pairing μ (piolaFlux Y F) hG.continuous hGc ψ hψ
  simp only [map_sub]
  rw [integral_sub h3 h1, piolaFlux_pairing μ Y (hY.differentiable (by simp))
    (fderiv_equiv_det_ne_zero Y (hY.differentiable (by simp)) (hi.differentiable (by simp)))
      F ψ (hψ.differentiable (by simp))]
  simp_rw [show (fun x => ψ (Y x) - ψ x) = (ψ ∘ Y) - ψ from rfl] at hz
  simp_rw [fderiv_sub (hψY.differentiable (by simp) _) (hψ.differentiable (by simp) _),
    _root_.sub_apply] at hz
  rw [integral_sub h2 h1] at hz
  exact hz

end ScalarConductivity

end

end OAI
