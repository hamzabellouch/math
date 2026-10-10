import OAI.Geometry.NodalSets.Coefficients.GaussianCoefficientTail
import OAI.Geometry.NodalSets.Elliptic.CompactSignEvents

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Analysis Yau.Probability Set MeasureTheory
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma seeded_firstJetSize_continuous (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed) (N : ℝ) (x : Coord) :
    Continuous (fun a : ι × Fin 2 → ℝ ↦
      sourceFirstJetSize (fun y ↦ seed y+gaussianWaveField V a y) N x) := by
  have hc (ds : List (Fin 4)) :=
    (seeded_partial_joint_continuous V seed hV hs ds).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ι × Fin 2 → ℝ ↦ x)))
  have hd (i : Fin 4) : Continuous (fun a : ι × Fin 2 → ℝ ↦
      fderiv ℝ (fun y ↦ seed y+gaussianWaveField V a y) x (Pi.single i 1)) := by
    simpa only [Function.comp_def,partialJet,id_eq] using hc [i]
  unfold sourceFirstJetSize sourceEuclideanNorm
  apply (show Continuous (fun a : ι × Fin 2 → ℝ ↦ seed x+gaussianWaveField V a x) from
    by simpa only [Function.comp_def,partialJet,id_eq] using hc []).abs.add
  exact continuous_const.mul (continuous_finsetSum _ (fun i _ ↦ (hd i).pow 2)).sqrt

def firstJetGoodEvent (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (N : ℝ) (Ω : Set Coord) (b : Coord → ℝ) : Set (ι × Fin 2 → ℝ) :=
  {a | ∀ x ∈ Ω, b x ≤ sourceFirstJetSize (fun y ↦ seed y+gaussianWaveField V a y) N x}

lemma firstJetGoodEvent_isClosed (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (N : ℝ) (Ω : Set Coord) (b : Coord → ℝ) : IsClosed (firstJetGoodEvent V seed N Ω b) := by
  simp only [firstJetGoodEvent,ofPred_forall]
  exact isClosed_iInter (fun x ↦ isClosed_iInter (fun _ ↦
    isClosed_le continuous_const (seeded_firstJetSize_continuous V seed hV hs N x)))

omit [Fintype ι] in
lemma coefficientEvent_isClosed (r : ℝ) : IsClosed (coefficientEvent (ι := ι) r) := by
  simp only [coefficientEvent,ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_le _ continuous_const
  fun_prop

def coefficientJetGoodEvent (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (N : ℝ) (Ω : Set Coord) (b : Coord → ℝ) : Set (ι × Fin 2 → ℝ) :=
  coefficientEvent N ∩ firstJetGoodEvent V seed N Ω b

lemma coefficientJetGoodEvent_measurable (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (N : ℝ) (Ω : Set Coord) (b : Coord → ℝ) :
    MeasurableSet (coefficientJetGoodEvent V seed N Ω b) :=
  ((coefficientEvent_isClosed N).inter (firstJetGoodEvent_isClosed V seed hV hs N Ω b)).measurableSet

lemma coefficientJetGoodEvent_failure_le (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (N : ℝ) (Ω : Set Coord) (b : Coord → ℝ) :
    gaussianPairs (coefficientJetGoodEvent V seed N Ω b)ᶜ ≤
      gaussianPairs (coefficientEvent (ι := ι) N)ᶜ +
      gaussianPairs {a | ∃ x ∈ Ω, sourceFirstJetSize
        (fun y ↦ seed y+gaussianWaveField V a y) N x < b x} := by
  have he : (firstJetGoodEvent V seed N Ω b)ᶜ =
      {a | ∃ x ∈ Ω, sourceFirstJetSize (fun y ↦ seed y+gaussianWaveField V a y) N x < b x} := by
    ext a
    simp [firstJetGoodEvent,not_forall,not_le]
  rw [coefficientJetGoodEvent,compl_inter,he]
  exact measure_union_le _ _

end
end Yau.Geometry

end OAI
