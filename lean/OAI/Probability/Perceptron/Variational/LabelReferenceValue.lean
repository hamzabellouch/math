import Mathlib
import OAI.Probability.Perceptron.Cavity.CountableFreshMoment
import OAI.Probability.Perceptron.Cavity.FreshReference

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def labelProfileTerminal (g : Jet3) (s : ℝ≥0) (v : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  heatLog s 1 g.f (inner ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))) v)

lemma labelProfileTerminal_lipschitz (g : Jet3) (s : ℝ≥0) :
    LipschitzWith (‖(g.heatLog s 1).d1‖₊*
      ‖innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))‖₊)
      (labelProfileTerminal g s) := by
  have he : labelProfileTerminal g s =
      fun v : EuclideanSpace ℝ (Fin 1) => (g.heatLog s 1).f
        ((innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))) v) := by
    funext v
    rw [Jet3.heatLog_f]
    rfl
  rw [he]
  have heatLipschitz : LipschitzWith ‖(g.heatLog s 1).d1‖₊ (g.heatLog s 1).f := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun point => ((g.heatLog s 1).has1 point).differentiableAt)
    intro point
    rw [(g.heatLog s 1).deriv_eq]
    exact_mod_cast (g.heatLog s 1).d1.norm_coe_le_norm point
  exact heatLipschitz.comp
    (innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))).lipschitzWith

lemma labelProfileTerminal_bound (g : Jet3) (s : ℝ≥0) (v : EuclideanSpace ℝ (Fin 1)) :
    |labelProfileTerminal g s v|≤‖g.f‖ := heatLog_abs_le s 1 g.f _

lemma labelProfileTerminal_exp (g : Jet3) (s : ℝ≥0) (v : EuclideanSpace ℝ (Fin 1)) :
    Real.exp (labelProfileTerminal g s v)=
      gaussianAverageBCF s (expBCF 1 g.f)
        (inner ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))) v) := by
  simpa only [NNReal.coe_one,one_mul,labelProfileTerminal,gaussianAverageBCF_coe] using
    exp_heatLog s 1 (by norm_num) g.f
      (inner ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))) v)

theorem source_countable_label_reference_value (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1) (g : Jet3) :
    let s : ℝ≥0 := ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩
    let A := fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => q l) j)
    let R := diagonalMark (profileGaussianRoot (fun l (_ : Fin 1) => q l))
    (∫ t : IndexedCascadeBase k×((ℕ→ℝ)×(ℕ→ℝ)),
      Real.log (tiltMean (indexedLeafProbability k t.1)
        (fun l => enrichedTerminal n M f a p u (h (Fin.last k))
          (indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
            ((fun _ => enrichedRootMap p d h
              (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) t.2.2).1),
              (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) t.2.2).2) l 0))
        (fun l => gaussianAverageBCF s (expBCF 1 g.f)
          (labelProfileField q t.2.1 ((),l))) 1)
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        (countableGaussianLaw.prod countableGaussianLaw)) =
      ∫ x, gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ (Fin 1)))
        (linearCascadeWord A k z) (labelProfileTerminal g s) (R x)
        ∂stdGaussian (EuclideanSpace ℝ (Fin 1)) := by
  dsimp only
  have hv := source_countable_fresh_reference_value n M k f a p d h u z hz hz0 hz1
    (fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => q l) j))
    (diagonalMark (profileGaussianRoot (fun l (_ : Fin 1) => q l)))
    (labelProfileTerminal_lipschitz g ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩)
    (norm_nonneg g.f) (labelProfileTerminal_bound g _)
  refine (integral_congr_ae (ae_of_all _ fun t => ?_)).trans hv
  unfold sourceFreshReferenceLog
  congr 2
  funext l
  dsimp only
  rw [labelProfileField_marked_state]
  exact (labelProfileTerminal_exp _ _ _).symm

end SphericalPerceptronFreeEnergy
end

end OAI
