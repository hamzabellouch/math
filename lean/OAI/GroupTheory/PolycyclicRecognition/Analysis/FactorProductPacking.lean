import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasurePacking
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.GroupTheory.SemidirectProduct

namespace OAI

/-! # Packing through a possibly noninjective factor map

Left translations on a semidirect product act separately on its two factor
coordinates. Their product measure is preserved when the action preserves
the first factor's measure. Disjointness is tested after projection to the
ambient metric group, so no injectivity of that projection is required.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped ENNReal

variable {N D G : Type*} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MeasurableSpace D] [MeasurableMul N] [MeasurableMul D]

/-- Semidirect left translation, written on the product of the factors. -/
def factorTranslate (φ : D →* MulAut N) (p z : N × D) : N × D :=
  (p.1 * φ p.2 z.1, p.2 * z.2)

/-- Measurable automorphisms give measurable product-coordinate translations. -/
def factorTranslationEquiv (φ : D →* MulAut N)
    (hφ : ∀ d, Measurable (φ d)) (p : N × D) : (N × D) ≃ᵐ (N × D) :=
  let e : N ≃ᵐ N := {
    toEquiv := (φ p.2).toEquiv
    measurable_toFun := hφ p.2
    measurable_invFun := by
      change Measurable (fun x => (φ p.2).symm x)
      have he : (fun x => (φ p.2).symm x) = (fun x => φ p.2⁻¹ x) := by
        funext x
        rw [map_inv, MulAut.inv_apply]
      rw [he]
      exact hφ p.2⁻¹ }
  (e.trans (MeasurableEquiv.mulLeft p.1)).prodCongr (MeasurableEquiv.mulLeft p.2)

@[simp] theorem factorTranslationEquiv_apply (φ : D →* MulAut N)
    (hφ : ∀ d, Measurable (φ d)) (p z : N × D) :
    factorTranslationEquiv φ hφ p z = factorTranslate φ p z := rfl

/-- Product Haar mass is unchanged by these translations. -/
theorem factorTranslate_measure (φ : D →* MulAut N)
    (μ : Measure N) (ν : Measure D) [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    [SFinite μ] [SFinite ν] (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (p : N × D) (U : Set (N × D)) :
    (μ.prod ν) (factorTranslate φ p '' U) = (μ.prod ν) U := by
  let e := factorTranslationEquiv φ (fun d => (hφ d).measurable) p
  have hp : MeasurePreserving e (μ.prod ν) (μ.prod ν) :=
    ((measurePreserving_mul_left μ p.1).comp (hφ p.2)).prod
      (measurePreserving_mul_left ν p.2)
  have he : e ⁻¹' (e '' U) = U := e.preimage_image U
  have hv := hp.measure_preimage_equiv (e '' U)
  rw [he] at hv
  exact hv.symm

omit [MeasurableSpace N] [MeasurableSpace D] [MeasurableMul N] [MeasurableMul D] in
/-- The product-coordinate map intertwines translations and ambient multiplication. -/
theorem factorTranslate_projection (φ : D →* MulAut N)
    (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹) (p z : N × D) :
    ι (factorTranslate φ p z).1 * κ (factorTranslate φ p z).2 =
      (ι p.1 * κ p.2) * (ι z.1 * κ z.2) := by
  simp only [factorTranslate, map_mul, hc]
  group

variable [MetricSpace G] [IsIsometricSMul G G]

/-- Every finite separated family of ambient projections gives disjoint
translated cells in the product of the factors, even if the factor map has
nontrivial fibers. -/
theorem factor_separated_card_mul_le (φ : D →* MulAut N)
    (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (μ : Measure N) (ν : Measure D) [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    [SFinite μ] [SFinite ν] (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (s : Finset G) (p : G → N × D) (U region : Set (N × D))
    (hU : MeasurableSet U) {ρ : ℝ}
    (hp : ∀ x ∈ s, ι (p x).1 * κ (p x).2 = x)
    (hsmall : ∀ z ∈ U, dist (1 : G) (ι z.1 * κ z.2) < ρ / 2)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ρ ≤ dist x y)
    (hthick : ∀ x ∈ s, factorTranslate φ (p x) '' U ⊆ region) :
    (s.card : ℝ≥0∞) * (μ.prod ν) U ≤ (μ.prod ν) region := by
  classical
  let cell (x : G) := factorTranslate φ (p x) '' U
  have hcell (x : G) : MeasurableSet (cell x) :=
    (factorTranslationEquiv φ (fun d => (hφ d).measurable) (p x)).measurableSet_image.mpr hU
  have hnear (x : G) (hx : x ∈ s) {z : N × D} (hz : z ∈ cell x) :
      dist x (ι z.1 * κ z.2) < ρ / 2 := by
    obtain ⟨u, hu, rfl⟩ := hz
    rw [factorTranslate_projection φ ι κ hc]
    calc
      _ = dist (ι (p x).1 * κ (p x).2)
          ((ι (p x).1 * κ (p x).2) * (ι u.1 * κ u.2)) := by
        exact congrArg (fun y => dist y ((ι (p x).1 * κ (p x).2) * (ι u.1 * κ u.2)))
          (hp x hx).symm
      _ = dist (1 : G) (ι u.1 * κ u.2) := by
        simpa only [mul_one] using
          dist_mul_left (ι (p x).1 * κ (p x).2) (1 : G) (ι u.1 * κ u.2)
      _ < _ := hsmall u hu
  have hd : Set.Pairwise (↑s : Set G) (fun x y => Disjoint (cell x) (cell y)) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have h1 := hnear x hx hzx
    have h2 := hnear y hy hzy
    have ht := dist_triangle x (ι z.1 * κ z.2) y
    rw [dist_comm (ι z.1 * κ z.2) y] at ht
    linarith [hsep x hx y hy hxy]
  calc
    (s.card : ℝ≥0∞) * (μ.prod ν) U = (μ.prod ν) (⋃ x ∈ s, cell x) := by
      rw [measure_biUnion_finset hd (fun x _ => hcell x)]
      simp only [cell, factorTranslate_measure φ μ ν hφ, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := measure_mono (iUnion₂_subset hthick)

end PolycyclicRecognition

end

end OAI
