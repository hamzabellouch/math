import Mathlib
import OAI.Analysis.Conductivity.Sources.LocalPiola
import OAI.Analysis.Conductivity.Variational.CompactSymmetricMoments
import OAI.Analysis.Conductivity.Flux.CompactFluxDivergence

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def symmetricSource (H : Coord3 → Mat3) (u : Coord3 → Fin 2 → ℝ) (j : Fin 2) : Coord3 → ℝ :=
  coordinateDivergence (fun x => (H x*gradientColumns (fderiv ℝ u x)).col j)

lemma symmetricFlux_smooth {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤ : ℕ∞)) H) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (j : Fin 2) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (H x*gradientColumns (fderiv ℝ u x)).col j) := by
  have hm : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => H x*gradientColumns (fderiv ℝ u x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact contDiffAt_matrix_mul hH.contDiffAt (contDiff_gradientColumns u hu).contDiffAt
  apply contDiff_pi.mpr
  intro i
  exact contDiff_pi.mp (contDiff_pi.mp hm i) j

lemma symmetricFlux_compact {H : Coord3 → Mat3} (hH : HasCompactSupport H)
    (u : Coord3 → Fin 2 → ℝ) (j : Fin 2) :
    HasCompactSupport (fun x => (H x*gradientColumns (fderiv ℝ u x)).col j) :=
  hH.of_isClosed_subset isClosed_closure (tensorColumn_tsupport H _ j)

theorem symmetric_cutoff_sources
    (H : Coord3 → Mat3) (hH : ContDiff ℝ (↑(⊤ : ℕ∞)) H) (hs : HasCompactSupport H)
    (hsy : ∀ x,(H x).IsSymm)
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) :
    (∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (symmetricSource H u j)) ∧
    (∀ j,HasCompactSupport (symmetricSource H u j)) ∧
    (∀ j (ψ : Coord3 → ℝ),ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x,fderiv ℝ ψ x ((H x*gradientColumns (fderiv ℝ u x)).col j))=
        -(∫ x,ψ x*symmetricSource H u j x)) ∧
    (∫ x,symmetricSource H u 0 x)=0 ∧ (∫ x,symmetricSource H u 1 x)=0 ∧
    (∫ x,u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x)=0 := by
  have hr (j : Fin 2) : ContDiff ℝ (↑(⊤ : ℕ∞)) (symmetricSource H u j) :=
    coordinateDivergence_smooth (symmetricFlux_smooth hH hu j)
  have hsr (j : Fin 2) : HasCompactSupport (symmetricSource H u j) :=
    coordinateDivergence_compact (symmetricFlux_compact hs u j)
  have hw (j : Fin 2) (ψ : Coord3 → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) :
      (∫ x,fderiv ℝ ψ x ((H x*gradientColumns (fderiv ℝ u x)).col j))=
        -(∫ x,ψ x*symmetricSource H u j x) :=
    coordinateDivergence_weak (symmetricFlux_smooth hH hu j) (symmetricFlux_compact hs u j) ψ hψ
  exact ⟨hr,hsr,hw,compact_symmetric_source_moments u hu H hsy _ hr hsr hw⟩

end ScalarConductivity

end

end OAI
