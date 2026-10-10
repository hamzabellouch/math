import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlternatingProductSubmersion
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NormalizedExponentialLaws
import Mathlib.Topology.Sequences

namespace OAI

/-! # Simultaneous limits of two box embeddings

The bounded embeddings and their bounded generator preimages are retained
alongside the normalized Lie law. Thus every limiting generator belongs to
one of the limiting images, and the full alternating product is submersive.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric Module Filter
open scoped Topology

abbrev TwoImageData (I : Type*) (n : ℕ) :=
  ((((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ)) ×
    (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))) ×
      ((I → Fin n → ℝ) × (I → Fin n → ℝ))

def TwoImageData.generatorsCovered {I : Type*} {n : ℕ} (q : TwoImageData I n) : Prop :=
  ∀ i, q.1.2.1 (q.2.1 i) = q.1.1.2 i ∨ q.1.2.2 (q.2.2 i) = q.1.1.2 i

def HasSubmersiveTwoImageSubsequence {I : Type*} [Fintype I] {n c : ℕ}
    (a : DynkinCoefficients c 2) (w : Fin n → FreeMagma I) (C : ℝ)
    (q : ℕ → TwoImageData I n) : Prop :=
  ∃ q₀ : TwoImageData I n,
    q₀.1.1 ∈ normalizedExponentialParameters a w (fun i => Pi.single i 1) C ∧
    q₀.generatorsCovered ∧
    ∃ u : ℕ → ℕ, StrictMono u ∧ Tendsto (q ∘ u) atTop (𝓝 q₀) ∧
    ∃ (h : ℕ) (z₀ : Fin h → (Fin n → ℝ) × (Fin n → ℝ)),
      alternatingCoordinateProduct a q₀.1.1.1 q₀.1.2.1 q₀.1.2.2 z₀ = 0 ∧
      Function.Surjective
        (fderiv ℝ (alternatingCoordinateProduct a q₀.1.1.1 q₀.1.2.1 q₀.1.2.2) z₀)

theorem isClosed_twoImageData_generatorsCovered {I : Type*} {n : ℕ} :
    IsClosed {q : TwoImageData I n | q.generatorsCovered} := by
  simp only [TwoImageData.generatorsCovered, ofPred_forall]
  apply isClosed_iInter
  intro i
  exact (isClosed_eq
    (continuous_fst.snd.fst.clm_apply ((continuous_apply i).comp continuous_snd.fst))
    ((continuous_apply i).comp continuous_fst.fst.snd)).union
    (isClosed_eq
      (continuous_fst.snd.snd.clm_apply ((continuous_apply i).comp continuous_snd.snd))
      ((continuous_apply i).comp continuous_fst.fst.snd))

theorem exists_submersive_twoImage_limit
    {I : Type*} [Fintype I] {n c : ℕ} (a : DynkinCoefficients c 2)
    (w : Fin n → FreeMagma I) (C D : ℝ) (q : ℕ → TwoImageData I n)
    (hq : ∀ k, (q k).1.1 ∈
      normalizedExponentialParameters a w (fun i => Pi.single i 1) C)
    (hL₁ : ∀ k, ‖(q k).1.2.1‖ ≤ D) (hL₂ : ∀ k, ‖(q k).1.2.2‖ ≤ D)
    (hv₁ : ∀ k, ‖(q k).2.1‖ ≤ D) (hv₂ : ∀ k, ‖(q k).2.2‖ ≤ D)
    (hcover : ∀ k, (q k).generatorsCovered) :
    HasSubmersiveTwoImageSubsequence a w C q := by
  let : FiniteDimensional ℝ ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
    ContinuousLinearMap.finiteDimensional
  let : ProperSpace ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := FiniteDimensional.proper ℝ _
  let : ProperSpace (I → Fin n → ℝ) := FiniteDimensional.proper ℝ _
  let K : Set (TwoImageData I n) :=
    (normalizedExponentialParameters a w (fun i => Pi.single i 1) C ×ˢ
    (closedBall (0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) D ×ˢ closedBall 0 D)) ×ˢ
      (closedBall (0 : I → Fin n → ℝ) D ×ˢ closedBall 0 D)
  have hK : IsCompact K :=
    ((isCompact_normalizedExponentialParameters a w (fun i => Pi.single i 1) C).prod
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod
        ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hmem (k : ℕ) : q k ∈ K := by
    exact ⟨⟨hq k, by simpa using hL₁ k, by simpa using hL₂ k⟩,
      by simpa using hv₁ k, by simpa using hv₂ k⟩
  obtain ⟨q₀, hq₀, u, hu, hlim⟩ := hK.tendsto_subseq hmem
  have hc₀ : q₀.generatorsCovered :=
    isClosed_twoImageData_generatorsCovered.mem_of_tendsto hlim
      (Eventually.of_forall (fun k => hcover (u k)))
  have hw (i : Fin n) :
      evalBilinearWord q₀.1.1.1 q₀.1.1.2 (w i) = Pi.basisFun ℝ (Fin n) i := by
    simpa only [Pi.basisFun_apply] using hq₀.1.1.1.1.2.2.2 i
  refine ⟨q₀, hq₀.1.1, hc₀, u, hu, hlim, ?_⟩
  apply exists_submersive_alternatingCoordinateProduct a q₀.1.1.1
    hq₀.1.1.1.1.2.2.1 hq₀.1.1.1.2 hq₀.1.1.2
    q₀.1.2.1 q₀.1.2.2 q₀.1.1.2 (Pi.basisFun ℝ (Fin n)) w hw
  intro i
  rcases hc₀ i with h | h
  · exact Or.inl ⟨q₀.2.1 i, h⟩
  · exact Or.inr ⟨q₀.2.2 i, h⟩

end PolycyclicRecognition

end

end OAI
