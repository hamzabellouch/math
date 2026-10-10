import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceTilePacking

namespace OAI

/-! # Packing tiles whose factor lifts use different anchors

Endpoint sets stay in the common ambient frame. Each tile may choose its
own left-translated factor coordinates without changing its cardinality
or the separation constant.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology

variable {N D G : Type*} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MeasurableSpace D] [MeasurableMul N] [MeasurableMul D]
  [MetricSpace G] [IsIsometricSMul G G]

theorem factor_anchored_card_le_product_volume (φ : D →* MulAut N)
    (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (μ : Measure N) (ν : Measure D) [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    [SFinite μ] [SFinite ν] (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (s : Finset G) (anchor : G) (p : G → N × D)
    (U : Set (N × D)) (E : Set N) (B : Set D)
    (hU : MeasurableSet U) (hU0 : (μ.prod ν) U ≠ 0) (hUtop : (μ.prod ν) U ≠ ⊤)
    (hE : μ E ≠ ⊤) (hB : ν B ≠ ⊤) {ρ : ℝ}
    (hp : ∀ x ∈ s, ι (p x).1 * κ (p x).2 = anchor⁻¹ * x)
    (hsmall : ∀ z ∈ U, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ x ∈ s, factorTranslate φ (p x) '' U ⊆ E ×ˢ B) :
    (s.card : ℝ) ≤ (μ E).toReal * (ν B).toReal / ((μ.prod ν) U).toReal := by
  let f : G ↪ G := ⟨fun x => anchor⁻¹ * x, fun _ _ h => mul_left_cancel h⟩
  let p' : G → N × D := fun x => p (anchor * x)
  have hp' : ∀ x ∈ s.map f, ι (p' x).1 * κ (p' x).2 = x := by
    intro x hx
    obtain ⟨x, hsx, rfl⟩ := Finset.mem_map.mp hx
    change ι (p (anchor * (anchor⁻¹ * x))).1 * κ (p (anchor * (anchor⁻¹ * x))).2 = anchor⁻¹ * x
    rw [mul_inv_cancel_left]
    exact hp x hsx
  have hsep' : ∀ x ∈ s.map f, ∀ y ∈ s.map f, x ≠ y → ρ ≤ dist x y := by
    intro x hx y hy hxy
    obtain ⟨x, hsx, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y, hsy, rfl⟩ := Finset.mem_map.mp hy
    have hne : x ≠ y := fun h => hxy (congrArg f h)
    change ρ ≤ dist (anchor⁻¹ * x) (anchor⁻¹ * y)
    rw [dist_mul_left]
    exact hsep x hsx y hsy hne
  have hthick' : ∀ x ∈ s.map f, factorTranslate φ (p' x) '' U ⊆ E ×ˢ B := by
    intro x hx
    obtain ⟨x, hsx, rfl⟩ := Finset.mem_map.mp hx
    change factorTranslate φ (p (anchor * (anchor⁻¹ * x))) '' U ⊆ E ×ˢ B
    rw [mul_inv_cancel_left]
    exact hthick x hsx
  simpa only [Finset.card_map] using factor_separated_card_le_product_volume
    φ ι κ hc μ ν hφ (s.map f) p' U E B hU hU0 hUtop hE hB hp' hsmall hsep' hthick'

/-- Common per-tile bounds in independently translated factor frames. -/
theorem sequence_anchored_tile_separated_count
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (μ : Measure N) (ν : Measure D) [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    [SFinite μ] [SFinite ν] (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (tiles : ℕ → ℕ) (s : ∀ n, Fin (tiles n) → Finset G)
    (anchor : ∀ n, Fin (tiles n) → G)
    (p : ∀ n, Fin (tiles n) → G → N × D)
    (E : ∀ n, Fin (tiles n) → Set N) (B : ℕ → Set D)
    (U : Set (N × D)) (hU : MeasurableSet U)
    (hU0 : (μ.prod ν) U ≠ 0) (hUtop : (μ.prod ν) U ≠ ⊤)
    (hE : ∀ n j, μ (E n j) ≠ ⊤) (hB : ∀ n, ν (B n) ≠ ⊤) {ρ : ℝ}
    (hp : ∀ n j, ∀ x ∈ s n j, ι (p n j x).1 * κ (p n j x).2 = (anchor n j)⁻¹ * x)
    (hsmall : ∀ z ∈ U, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hsep : ∀ n j, ∀ x ∈ s n j, ∀ y ∈ s n j, x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ᶠ n in atTop, ∀ j, ∀ x ∈ s n j, factorTranslate φ (p n j x) '' U ⊆ E n j ×ˢ B n)
    (A Bvol : ℕ → ℝ)
    (hA : HasSubexponentialUpperBoundSeq scale A)
    (hBvol : HasSubexponentialUpperBoundSeq scale Bvol)
    (hA0 : ∀ n, 0 ≤ A n) (hBvol0 : ∀ n, 0 ≤ Bvol n)
    (P ell : ℝ)
    (hNvol : ∀ n j, (μ (E n j)).toReal ≤ A n * Real.exp ((P - ell) * scale n))
    (hDvol : ∀ n, (ν (B n)).toReal ≤ Bvol n) :
    ∃ loss : ℕ → ℝ, HasSubexponentialUpperBoundSeq scale loss ∧
      (∀ n, 0 ≤ loss n) ∧ ∀ᶠ n in atTop, ∀ j,
        ((s n j).card : ℝ) ≤ loss n * Real.exp ((P - ell) * scale n) := by
  let c := ((μ.prod ν) U).toReal
  have hc0 : 0 < c := ENNReal.toReal_pos hU0 hUtop
  let loss := fun n => A n * Bvol n * c⁻¹
  have hloss : HasSubexponentialUpperBoundSeq scale loss :=
    (hA.mul hBvol (Eventually.of_forall hA0)).mul
      (sequence_subexponential_upper_const hscale c⁻¹)
      (Eventually.of_forall (fun n => mul_nonneg (hA0 n) (hBvol0 n)))
  refine ⟨loss, hloss,
    fun n => mul_nonneg (mul_nonneg (hA0 n) (hBvol0 n)) (inv_nonneg.mpr hc0.le), ?_⟩
  filter_upwards [hthick] with n hn
  intro j
  have hcount := factor_anchored_card_le_product_volume φ ι κ hc μ ν hφ
    (s n j) (anchor n j) (p n j) U (E n j) (B n) hU hU0 hUtop (hE n j) (hB n)
    (hp n j) hsmall (hsep n j) (hn j)
  calc
    _ ≤ (μ (E n j)).toReal * (ν (B n)).toReal / c := hcount
    _ ≤ (A n * Real.exp ((P - ell) * scale n)) * Bvol n / c := by
      apply div_le_div_of_nonneg_right _ hc0.le
      exact mul_le_mul (hNvol n j) (hDvol n) ENNReal.toReal_nonneg
        (mul_nonneg (hA0 n) (Real.exp_pos _).le)
    _ = loss n * Real.exp ((P - ell) * scale n) := by dsimp [loss]; ring

end PolycyclicRecognition

end

end OAI
