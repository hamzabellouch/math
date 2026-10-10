import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateSymmetries

namespace OAI

/-! # Passing bounded height from normalized representatives to coarse maps -/

noncomputable section
namespace PolycyclicRecognition

open scoped NNReal

variable {G W P I B₀ : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [Fintype I] [Fintype B₀] [Nonempty B₀]

omit [ProperSpace G] in
/-- Bounded perturbations of both evaluation points cost at most twice
the height-Lipschitz constant times the perturbation radius. No continuity
of the original coarse maps is used. -/
theorem uniform_affine_height_of_bounded_pair_representatives
    (D : SupportDatum W I B₀) (π : G →* Multiplicative W)
    {L : ℝ} (hL : 0 ≤ L)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ L * dist x y)
    {Λ : ℝ≥0} (label : NormalizedPair G Λ → templateSymmetryGroup D)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ p x, ‖(π (p.val.1 x)).toAdd - (label p).val (π x).toAdd‖ ≤ K)
    (f : P → G → G) (rep : P → C(G, G) × C(G, G))
    (hrep : ∀ p, LipschitzPairBounds G Λ (rep p))
    {E : ℝ} (hE : 0 ≤ E) (hclose : ∀ p x, dist ((rep p).1 x) (f p x) ≤ E) :
    ∃ (A : P → templateSymmetryGroup D) (B : ℝ), 0 ≤ B ∧ ∀ p x,
      ‖(π (f p x)).toAdd - ((π (f p 1)).toAdd + (A p).val (π x).toAdd)‖ ≤ B := by
  let q := fun p => normalizePair (rep p) (hrep p)
  let A := fun p => label (q p)
  have hb (p : P) (x : G) :
      ‖(π ((rep p).1 x)).toAdd - (π ((rep p).1 1)).toAdd -
        (A p).val (π x).toAdd‖ ≤ K := by
    have h := hbound (q p) x
    change ‖(π (((rep p).1 1)⁻¹ * (rep p).1 (1 * x))).toAdd -
      (A p).val (π x).toAdd‖ ≤ K at h
    simpa only [one_mul, map_mul, map_inv, toAdd_mul, toAdd_inv, neg_add_eq_sub] using h
  refine ⟨A, K + 2 * L * E, by positivity, ?_⟩
  intro p x
  have hx : ‖(π (f p x)).toAdd - (π ((rep p).1 x)).toAdd‖ ≤ L * E := by
    exact (hπ _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [dist_comm] using hclose p x) hL)
  have h1 : ‖(π ((rep p).1 1)).toAdd - (π (f p 1)).toAdd‖ ≤ L * E :=
    (hπ _ _).trans (mul_le_mul_of_nonneg_left (hclose p 1) hL)
  calc
    _ = ‖((π (f p x)).toAdd - (π ((rep p).1 x)).toAdd) +
        ((π ((rep p).1 x)).toAdd - (π ((rep p).1 1)).toAdd - (A p).val (π x).toAdd) +
        ((π ((rep p).1 1)).toAdd - (π (f p 1)).toAdd)‖ := by congr 1; abel
    _ ≤ (‖(π (f p x)).toAdd - (π ((rep p).1 x)).toAdd‖ +
        ‖(π ((rep p).1 x)).toAdd - (π ((rep p).1 1)).toAdd - (A p).val (π x).toAdd‖) +
        ‖(π ((rep p).1 1)).toAdd - (π (f p 1)).toAdd‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (L * E + K) + L * E := add_le_add (add_le_add hx (hb p x)) h1
    _ = K + 2 * L * E := by ring

end PolycyclicRecognition

end

end OAI
