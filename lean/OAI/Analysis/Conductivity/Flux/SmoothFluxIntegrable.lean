import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactGlobalUpdate

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
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

lemma smooth_matrix_column {F : Coord3 → Matrix (Fin 3) (Fin 2) ℝ}
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (j : Fin 2) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (F x).col j) := by
  exact contDiff_pi.mpr (fun i => (contDiff_pi.mp (contDiff_pi.mp hF i) j))

lemma compact_matrix_column {F : Coord3 → Matrix (Fin 3) (Fin 2) ℝ}
    (hF : HasCompactSupport F) (j : Fin 2) : HasCompactSupport (fun x => (F x).col j) := by
  apply hF.mono
  intro x hx hzero
  apply hx
  change (F x).col j = 0
  rw [hzero]
  rfl

def SmoothFluxIntegrable (μ : Measure Coord3) (U : Set Coord3)
    (F : Coord3 → Matrix (Fin 3) (Fin 2) ℝ) : Prop :=
  ∀ (j : Fin 2) (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
    HasCompactSupport ψ → tsupport ψ ⊆ U →
    Integrable (fun x => fderiv ℝ ψ x ((F x).col j)) μ

lemma CompactGlobalUpdate.preserves_harmonic
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0) :
    SmoothFluxIntegrable μ U (conductivityFlux (fun x => u x+R.du x) R.tensor) ∧
    ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux (fun x => u x+R.du x) R.tensor x).col j) ∂μ) = 0 := by
  have he : ∀ j (ψ : Coord3 → ℝ),
      (fun x => fderiv ℝ ψ x ((conductivityFlux (fun x => u x+R.du x) R.tensor x).col j)) =
      (fun x => fderiv ℝ ψ x ((conductivityFlux u A x).col j) + fderiv ℝ ψ x ((R.dF x).col j)) := by
    intro j ψ
    funext x
    rw [R.constitutive x]
    change fderiv ℝ ψ x (((conductivityFlux u A x).col j) + (R.dF x).col j) = _
    exact map_add _ _ _
  constructor
  · intro j ψ hψ hc hs
    rw [he]
    exact (hint j ψ hψ hc hs).add (smooth_flux_integrable_pairing μ
      (fun x => (R.dF x).col j) (smooth_matrix_column R.smooth_dF j).continuous (compact_matrix_column R.compact_dF j) ψ hψ)
  · intro j ψ hψ hc hs
    rw [he,integral_add (hint j ψ hψ hc hs) (smooth_flux_integrable_pairing μ
      (fun x => (R.dF x).col j) (smooth_matrix_column R.smooth_dF j).continuous (compact_matrix_column R.compact_dF j) ψ hψ),
      hdiv j ψ hψ hc hs,R.cauchy_dF j ψ hψ,add_zero]

def CompactGlobalUpdate.trans
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    (S : CompactGlobalUpdate μ U (fun x => u x+R.du x) R.tensor) :
    CompactGlobalUpdate μ U u A where
  du := R.du+S.du
  dF := R.dF+S.dF
  tensor := S.tensor
  smooth_du := R.smooth_du.add S.smooth_du
  compact_du := R.compact_du.add S.compact_du
  support_du := (tsupport_add _ _).trans (union_subset R.support_du S.support_du)
  smooth_dF := R.smooth_dF.add S.smooth_dF
  compact_dF := R.compact_dF.add S.compact_dF
  support_dF := (tsupport_add _ _).trans (union_subset R.support_dF S.support_dF)
  cauchy_dF := by
    intro j ψ hψ
    change (∫ x, fderiv ℝ ψ x ((R.dF x).col j+(S.dF x).col j) ∂μ) = 0
    simp_rw [map_add]
    rw [integral_add (smooth_flux_integrable_pairing μ
      (fun x => (R.dF x).col j) (smooth_matrix_column R.smooth_dF j).continuous (compact_matrix_column R.compact_dF j) ψ hψ)
      (smooth_flux_integrable_pairing μ
      (fun x => (S.dF x).col j) (smooth_matrix_column S.smooth_dF j).continuous (compact_matrix_column S.compact_dF j) ψ hψ),
      R.cauchy_dF j ψ hψ,S.cauchy_dF j ψ hψ,add_zero]
  measurable_tensor := S.measurable_tensor
  constitutive := by
    intro x
    have he : (fun y => u y+(R.du+S.du) y) = (fun y => (u y+R.du y)+S.du y) := by
      funext y; exact (add_assoc _ _ _).symm
    rw [he,S.constitutive x,R.constitutive x]
    exact add_assoc _ _ _

end ScalarConductivity

end

end OAI
