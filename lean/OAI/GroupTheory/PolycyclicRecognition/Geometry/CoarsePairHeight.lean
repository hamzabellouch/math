import OAI.GroupTheory.PolycyclicRecognition.Analysis.LipschitzPairReplacement
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NormalizedPairHeightTransfer

namespace OAI

/-! # Bounded height for uniform families of coarse inverse pairs

Representative existence is proved here from the controlled contraction.
The normalized height premise is discharged by the Cartan theorem in the
application; it is not declared as a published result.
-/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {G W P I B₀ : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [Fintype I] [Fintype B₀] [Nonempty B₀]

theorem uniform_affine_height_of_coarse_inverse_pairs
    (c : ControlledContraction G)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ s) ≤ dist 1 g * |t - s|)
    (D : SupportDatum W I B₀) (π : G →* Multiplicative W)
    {L : ℝ} (hL : 0 ≤ L)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ L * dist x y)
    (hheight : ∀ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) →
      ∃ label : NormalizedPair G Λ → templateSymmetryGroup D,
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ p x, ‖(π (p.val.1 x)).toAdd - (label p).val (π x).toAdd‖ ≤ B)
    {K C A : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (f g : P → G → G)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ K * dist x y + C)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ K * dist x y + C)
    (hgf : ∀ p x, dist (g p (f p x)) x ≤ A)
    (hfg : ∀ p x, dist (f p (g p x)) x ≤ A) :
    ∃ (label : P → templateSymmetryGroup D) (B : ℝ), 0 ≤ B ∧ ∀ p x,
      ‖(π (f p x)).toAdd - ((π (f p 1)).toAdd + (label p).val (π x).toAdd)‖ ≤ B := by
  obtain ⟨Λ, hΛ, E, hE, hreplace⟩ := exists_lipschitz_pair_replacement_constants c hpath hK hC
  have hex (p : P) : ∃ q : C(G, G) × C(G, G), LipschitzPairBounds G Λ q ∧
      (∀ x, dist (q.1 x) (f p x) ≤ E) ∧ (∀ x, dist (q.2 x) (g p x) ≤ E) :=
    hreplace (f p) (g p) (hf p) (hg p) (hgf p) (hfg p)
  choose rep hrep hclose _ using hex
  obtain ⟨label, B, hB, hbound⟩ := hheight Λ hΛ
  exact uniform_affine_height_of_bounded_pair_representatives D π hL hπ
    label hB hbound f rep hrep hE hclose

end PolycyclicRecognition

end

end OAI
