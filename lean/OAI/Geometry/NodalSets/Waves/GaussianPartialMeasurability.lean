import OAI.Geometry.NodalSets.Elliptic.CoordinatePartialJets
import OAI.Geometry.NodalSets.Waves.GaussianDerivativeMoments

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Analysis Yau.Probability MeasureTheory
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma seeded_partial_joint_continuous (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (ds : List (Fin 4)) :
    Continuous (fun z : (ι × Fin 2 → ℝ) × Coord ↦
      partialJet (fun x ↦ seed x+gaussianWaveField V z.1 x) ds z.2) := by
  have hF (a : ι × Fin 2 → ℝ) := hs.add (gaussianWaveField_contDiff V a hV)
  simp_rw [partialJet_eq_iterated _ (hF _),seeded_gaussian_iterated_apply V seed hV hs]
  have horder : (ds.length : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (show (ds.length:ℕ∞) ≤ ⊤ from le_top)
  have hc {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : Coord → F) (hf : ContDiff ℝ ∞ f) :
      Continuous (fun z : (ι × Fin 2 → ℝ) × Coord ↦
        iteratedFDeriv ℝ ds.length f z.2 (partialDirs ds)) :=
    ((hf.continuous_iteratedFDeriv horder).comp continuous_snd).eval continuous_const
  apply (hc seed hs).add
  unfold pairLinearSum
  apply continuous_finsetSum
  intro p _
  apply Continuous.mul
  · split_ifs
    · exact Complex.continuous_re.comp (hc (V p.1) (hV p.1))
    · exact (Complex.continuous_im.comp (hc (V p.1) (hV p.1))).neg
  · exact (continuous_apply p).comp continuous_fst

end
end Yau.Geometry

end OAI
