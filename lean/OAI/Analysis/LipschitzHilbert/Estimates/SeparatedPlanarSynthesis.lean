import OAI.Analysis.LipschitzHilbert.Estimates.PlanarFixedScaleEnergy
import OAI.Analysis.LipschitzHilbert.Estimates.PlanarSeparatedEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticePolarizationSpectrum

namespace OAI

/-! Combining the box-lattice synthesis bound with separated annuli.
This is the nonmaximal, unweighted separated synthesis estimate of §3,
including the dimension-independent sum over frequency bins. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem planarFourier_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (frequency : ℝ×ℝ) :
    planarFourier (∑ i ∈ s, f i : SchwartzMap (ℝ×ℝ) ℂ) frequency =
      ∑ i ∈ s, planarFourier (f i) frequency := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [planarFourier]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi,planarFourier_add,ih,Finset.sum_insert hi]

theorem separated_planar_synthesis_energy {N : ℕ} {κ : Type*} [Fintype κ]
    {ι : Fin N → Type*} [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (site : ∀ j, ι j → ℤ×ℤ) (hinj : ∀ j, Function.Injective (site j))
    (a b : Fin N → ℝ) (len latticeSlope : Fin N → ℝ) (W slope C : ℝ)
    (hlen : ∀ j, 0 < len j) (hW : 0 < W) (lo hi : Fin N → ℝ)
    (hgap : ∀ i j, i < j → hi i < lo j)
    (hspectrum : ∀ j i k ξ η, planarFourier (f j i k) (ξ,η) ≠ 0 →
      lo j ≤ |ξ+slope*η| ∧ |ξ+slope*η| ≤ hi j)
    (henv : ∀ j i k z, ‖f j i k z‖ ≤ C*
      (lineEnvelope (a j+len j*(site j i).1) (len j) 1 z.1*
        lineEnvelope (b j+W*(site j i).2) W 1 (z.2-latticeSlope j*z.1))) :
    (∫ z, ‖∑ j, planarFixedSynthesis (c j) (f j) z‖^2 ∂volume.prod volume) ≤
      ((4*Real.pi)^2*C^2*Real.pi^2)*∑ j, ∑ i, ‖c j i‖^2*len j*W := by
  let G := fun j k => (∑ i, c j i k • f j i k : SchwartzMap (ℝ×ℝ) ℂ)
  have hG (j : Fin N) (z : ℝ×ℝ) :
      (WithLp.toLp 2 (fun k => G j k z) : EuclideanSpace ℂ κ) =
        planarFixedSynthesis (c j) (f j) z := by
    ext k
    simp only [G,planarFixedSynthesis,WithLp.ofLp_toLp,sum_apply,smul_apply,smul_eq_mul]
  have hspec (j : Fin N) (k : κ) (ξ η : ℝ)
      (hne : planarFourier (G j k) (ξ,η) ≠ 0) :
      lo j ≤ |ξ+slope*η| ∧ |ξ+slope*η| ≤ hi j := by
    by_contra hout
    have hz (i : ι j) : planarFourier (f j i k) (ξ,η) = 0 := by
      by_contra hnonzero
      exact hout (hspectrum j i k ξ η hnonzero)
    apply hne
    dsimp only [G]
    rw [planarFourier_finsetSum]
    simp only [planarFourier_smul,hz,mul_zero,Finset.sum_const_zero]
  have horthog := planar_separated_strip_vector_energy G slope lo hi hgap hspec
  simp only [hG] at horthog
  rw [horthog]
  calc
    _ ≤ ∑ j, ((4*Real.pi)^2*C^2*Real.pi^2)*∑ i, ‖c j i‖^2*len j*W :=
      Finset.sum_le_sum (fun j _ => planar_fixed_scale_energy (c j) (f j) (site j)
        (hinj j) (a j) (b j) (len j) W (latticeSlope j) C (hlen j) hW (henv j))
    _ = _ := (Finset.mul_sum _ _ _).symm

end LipschitzHilbert

end

end OAI
