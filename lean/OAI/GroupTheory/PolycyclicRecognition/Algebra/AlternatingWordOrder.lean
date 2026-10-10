import OAI.GroupTheory.PolycyclicRecognition.Algebra.BundleParameterCharts
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupedGoodWords

namespace OAI

/-! # Chronological alternating words and the two polynomial input blocks -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

def alternatingWordIndex (h : ℕ) : Fin (h * 2) ≃ Fin (h + h) :=
  finProdFinEquiv.symm.trans ((bundleParameterIndex h 1).trans (finCongr (by omega)))

theorem alternatingWordIndex_left (h : ℕ) (i : Fin h) :
    alternatingWordIndex h (finProdFinEquiv (i, (0 : Fin 2))) = Fin.castAdd h i := by
  simp only [alternatingWordIndex, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
  rw [bundleParameterIndex_left]
  apply Fin.ext
  simp [finProdFinEquiv]

theorem alternatingWordIndex_right (h : ℕ) (i : Fin h) :
    alternatingWordIndex h (finProdFinEquiv (i, (1 : Fin 2))) = Fin.natAdd h i := by
  simp only [alternatingWordIndex, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
  rw [bundleParameterIndex_right]
  apply Fin.ext
  simp [finProdFinEquiv]

variable {G : Type*} [MeasurableSpace G]

def alternatingWordBlockEquiv (h : ℕ) :
    (Fin (h * 2) → G) ≃ᵐ (Fin (h + h) → G) :=
  MeasurableEquiv.piCongrLeft (fun _ => G) (alternatingWordIndex h)

theorem alternatingWordBlockEquiv_left (h : ℕ) (u : Fin (h * 2) → G) (i : Fin h) :
    alternatingWordBlockEquiv h u (Fin.castAdd h i) = u (finProdFinEquiv (i, (0 : Fin 2))) := by
  rw [← alternatingWordIndex_left h i]
  exact MeasurableEquiv.piCongrLeft_apply_apply _ _ _

theorem alternatingWordBlockEquiv_right (h : ℕ) (u : Fin (h * 2) → G) (i : Fin h) :
    alternatingWordBlockEquiv h u (Fin.natAdd h i) = u (finProdFinEquiv (i, (1 : Fin 2))) := by
  rw [← alternatingWordIndex_right h i]
  exact MeasurableEquiv.piCongrLeft_apply_apply _ _ _

theorem alternatingWordBlockEquiv_apply (h : ℕ) (u : Fin (h * 2) → G) (i : Fin (h + h)) :
    alternatingWordBlockEquiv h u i = u ((alternatingWordIndex h).symm i) := by
  simp [alternatingWordBlockEquiv, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem measurePreserving_alternatingWordBlockEquiv (h : ℕ)
    (μ : Measure G) [SigmaFinite μ] :
    MeasurePreserving (alternatingWordBlockEquiv (G := G) h)
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) :=
  measurePreserving_piCongrLeft (fun _ => μ) (alternatingWordIndex h)

theorem alternatingWordBlockEquiv_image_measure (h : ℕ)
    (μ : Measure G) [SigmaFinite μ] (S : Set (Fin (h * 2) → G)) :
    (Measure.pi fun _ : Fin (h + h) => μ) (alternatingWordBlockEquiv h '' S) =
      (Measure.pi fun _ : Fin (h * 2) => μ) S := by
  let e := alternatingWordBlockEquiv (G := G) h
  have hm := (measurePreserving_alternatingWordBlockEquiv h μ).map_eq
  have he := congrArg (fun ν : Measure (Fin (h + h) → G) => ν (e '' S)) hm
  rw [e.measurableEmbedding.map_apply, Set.preimage_image_eq _ e.injective] at he
  exact he.symm

theorem continuous_alternatingWordBlockEquiv [TopologicalSpace G] (h : ℕ) :
    Continuous (alternatingWordBlockEquiv (G := G) h) := by
  have he : (alternatingWordBlockEquiv (G := G) h : _ → _) =
      fun u i => u ((alternatingWordIndex h).symm i) :=
    funext (fun u => funext (alternatingWordBlockEquiv_apply h u))
  rw [he]
  exact continuous_pi (fun i => continuous_apply ((alternatingWordIndex h).symm i))

theorem alternatingWordBlockEquiv_prod [Group G] (h : ℕ) (u : Fin (h * 2) → G) :
    (List.ofFn (fun i : Fin h =>
      alternatingWordBlockEquiv h u (Fin.castAdd h i) *
        alternatingWordBlockEquiv h u (Fin.natAdd h i))).prod = (List.ofFn u).prod := by
  simp only [alternatingWordBlockEquiv_left, alternatingWordBlockEquiv_right]
  rw [ofFn_eq_flatten_bundles, List.prod_flatten, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simp [List.ofFn_succ]

end PolycyclicRecognition

end

end OAI
