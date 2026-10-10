import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedProbeChains

namespace OAI

/-! # Linked root chains with their prescribed group endpoints -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Retain the logarithmic chains together with the group equalities used
by the measured comparison. The sampling domain stays an abstract parameter
so that its coordinate construction is not repeated in every projection. -/
structure LinkedRootProbeFrames
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (γ : M.Bases) (width : Fin M.letterCount → ℝ)
    (scale : ℕ → ℝ) (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (base step : ℕ → F.N.carrier)
    (first anchor second : ∀ n, Y n → F.N.carrier) where
  origin : ℕ → cartanRootIdeal H
  finish : ℕ → cartanRootIdeal H
  error : ℕ → ℝ
  error_nonneg : ∀ n, 0 ≤ error n
  error_tendsto : Tendsto error atTop (𝓝 0)
  chains : ∀ k, M.BoxProbeChains T F hunimod eW bN (E k) γ width scale (probe k)
  linked : M.LinkedProbeChains T F hunimod eW bN E γ width scale probe chains
    (fun n _ => origin n) (fun n _ => finish n) error
  origin_eq : ∀ n, F.ExpN (F.N.equiv (origin n)) = base n
  finish_eq : ∀ n, F.ExpN (F.N.equiv (finish n)) = base n * step n
  first_endpoint : ∀ n y,
    F.ExpN (F.N.equiv (linked.vertex 0 n y (Fin.last (chains 0).length))) = first n y
  anchor_endpoint : ∀ n y,
    F.ExpN (F.N.equiv (linked.vertex 1 n y (Fin.last (chains 1).length))) = anchor n y
  second_endpoint : ∀ n y,
    F.ExpN (F.N.equiv (linked.vertex 2 n y (Fin.last (chains 2).length))) = second n y

variable {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
  {bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)}
  {E : Fin 3 → Set W} {γ : M.Bases} {width : Fin M.letterCount → ℝ}
  {scale : ℕ → ℝ} {probe : Fin 3 → ∀ n, Y n → F.N.carrier}
  {base step : ℕ → F.N.carrier} {first anchor second : ∀ n, Y n → F.N.carrier}

/-- Substitute the first endpoint before specializing the sampling domain.
This keeps the metric comparison independent of its coordinate expressions. -/
theorem LinkedRootProbeFrames.first_endpoint_distance_le
    (L : LinkedRootProbeFrames T M F hunimod eW bN E γ width scale probe base step
      first anchor second)
    (other : ∀ n, Y n → G) (tail : ℕ → G) (bound : ℕ → ℝ)
    (h : ∀ᶠ n in atTop, ∀ y, dist (other n y)
      (F.inclusionN (first n y) * tail n) ≤ bound n) :
    ∀ᶠ n in atTop, ∀ y, dist (other n y)
      (F.inclusionN (F.ExpN (F.N.equiv
        (L.linked.vertex 0 n y (Fin.last (L.chains 0).length)))) * tail n) ≤ bound n := by
  filter_upwards [h] with n hn y
  rw [L.first_endpoint n y]
  exact hn y

end PolycyclicRecognition.CartanWordModel

end

end OAI
