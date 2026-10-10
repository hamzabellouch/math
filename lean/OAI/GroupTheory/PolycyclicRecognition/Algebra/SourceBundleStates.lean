import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarPrefixCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential

namespace OAI

/-! # Passing bundle products to conjugated successive source states -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

def sourceBundleStateEquiv (h : ℕ) (x : G) (φ : Fin h → G ≃ᵐ G) :
    (Fin h → G) ≃ᵐ (Fin h → G) :=
  (MeasurableEquiv.piCongrRight φ).trans
    ((prefixCoordinateEquiv h).trans (MeasurableEquiv.mulLeft (fun _ : Fin h => x)))

@[simp] theorem sourceBundleStateEquiv_apply (h : ℕ) (x : G) (φ : Fin h → G ≃ᵐ G)
    (u : Fin h → G) (i : Fin h) :
    sourceBundleStateEquiv h x φ u i = x * prefixCoordinateEquiv h (fun j => φ j (u j)) i := rfl

theorem measurePreserving_sourceBundleStateEquiv (μ : Measure G)
    [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (h : ℕ) (x : G) (φ : Fin h → G ≃ᵐ G)
    (hφ : ∀ i, MeasurePreserving (φ i) μ μ) :
    MeasurePreserving (sourceBundleStateEquiv h x φ)
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) :=
  (measurePreserving_mul_left (Measure.pi fun _ : Fin h => μ) (fun _ => x)).comp
    ((measurePreserving_prefixCoordinateEquiv μ h).comp
      (measurePreserving_pi (fun _ => μ) (fun _ => μ) hφ))

theorem sourceBundleStateEquiv_image_measure (μ : Measure G)
    [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (h : ℕ) (x : G) (φ : Fin h → G ≃ᵐ G)
    (hφ : ∀ i, MeasurePreserving (φ i) μ μ) (S : Set (Fin h → G)) :
    (Measure.pi fun _ : Fin h => μ) (sourceBundleStateEquiv h x φ '' S) =
      (Measure.pi fun _ : Fin h => μ) S := by
  let e := sourceBundleStateEquiv h x φ
  have he := (measurePreserving_sourceBundleStateEquiv μ h x φ hφ).map_eq
  have hv := congrArg (fun ν : Measure (Fin h → G) => ν (e '' S)) he
  rw [e.measurableEmbedding.map_apply, Set.preimage_image_eq _ e.injective] at hv
  exact hv.symm

theorem continuous_prefixCoordinateEquiv [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) : Continuous (prefixCoordinateEquiv (G := G) h) := by
  induction h with
  | zero => exact continuous_id
  | succ h ih =>
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [prefixCoordinateEquiv_zero] using (continuous_apply (0 : Fin (h + 1)))
    · have he : (fun u : Fin (h + 1) → G => prefixCoordinateEquiv (h + 1) u j.succ) =
          (fun u => u 0 * prefixCoordinateEquiv h (fun k => u k.succ) j) := by
        funext u
        exact prefixCoordinateEquiv_succ h u j
      rw [he]
      exact (continuous_apply 0).mul ((continuous_apply j).comp
        (ih.comp (continuous_pi (fun k => continuous_apply k.succ))))

theorem prefixCoordinateEquiv_last (n : ℕ) (u : Fin (n + 1) → G) :
    prefixCoordinateEquiv (n + 1) u (Fin.last n) = (List.ofFn u).prod := by
  induction n with
  | zero => simp [prefixCoordinateEquiv_zero]
  | succ n ih =>
    rw [show Fin.last (n + 1) = (Fin.last n).succ from rfl,
      prefixCoordinateEquiv_succ, ih]
    conv_rhs => rw [List.ofFn_succ, List.prod_cons]

theorem continuous_sourceBundleStateEquiv [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) (x : G) (φ : Fin h → G ≃ᵐ G) (hφ : ∀ i, Continuous (φ i)) :
    Continuous (sourceBundleStateEquiv h x φ) := by
  have hC : Continuous (fun u : Fin h → G => fun i => φ i (u i)) :=
    continuous_pi (fun i => (hφ i).comp (continuous_apply i))
  have hP := (continuous_prefixCoordinateEquiv h).comp hC
  exact continuous_pi (fun i => continuous_const.mul ((continuous_apply i).comp hP))

end PolycyclicRecognition

end

end OAI
