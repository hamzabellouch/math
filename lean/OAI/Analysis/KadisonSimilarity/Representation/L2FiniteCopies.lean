import OAI.Analysis.KadisonSimilarity.Representation.L2HilbertSum
import OAI.Analysis.KadisonSimilarity.Representation.OrthogonalColumns

namespace OAI

/-! # Finite Hilbert sums commute with L²

The isometry is the actual finite assembly of coordinate sections. Its
pointwise formula is retained for transporting operator matrix actions.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Insert a vector into a finite Hilbert coordinate. -/
def finiteCopyIsometry {n : ℕ} (i : Fin n) : H →ₗᵢ[ℂ] HilbertCopies H n where
  toLinearMap := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) i)).toLinearMap
  norm_map' x := PiLp.norm_single 2 (fun _ : Fin n => H) i x

@[simp] theorem finiteCopyIsometry_apply {n : ℕ} (i : Fin n) (x : H) :
    finiteCopyIsometry (H := H) i x = PiLp.single 2 i x := rfl

/-- Assemble a finite tuple of L² sections into one tuple-valued section. -/
def l2FiniteAssembly (n : ℕ) :
    HilbertCopies (Lp H 2 μ) n →L[ℂ] Lp (HilbertCopies H n) 2 μ :=
  sumColumns (fun i : Fin n => (l2MapIsometry μ (finiteCopyIsometry (H := H) i)).toContinuousLinearMap)

theorem l2FiniteAssembly_ae {n : ℕ} (f : HilbertCopies (Lp H 2 μ) n) :
    ∀ᵐ a ∂μ, ∀ i : Fin n, l2FiniteAssembly (H := H) μ n f a i = f i a := by
  have hparts : ∀ᵐ a ∂μ, ∀ i : Fin n,
      l2MapIsometry μ (finiteCopyIsometry (H := H) i) (f i) a = finiteCopyIsometry (H := H) i (f i a) :=
    eventually_countable_forall.mpr fun i => l2MapIsometry_ae μ (finiteCopyIsometry (H := H) i) (f i)
  have hsum := Lp.coeFn_finsetSum Finset.univ
    (fun i : Fin n => l2MapIsometry μ (finiteCopyIsometry (H := H) i) (f i))
  filter_upwards [hparts, hsum] with a ha hs
  intro i
  rw [l2FiniteAssembly, sumColumns_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap]
  rw [hs]
  simp only [Finset.sum_apply, ha, finiteCopyIsometry_apply]
  simp

theorem l2FiniteAssembly_norm {n : ℕ} (f : HilbertCopies (Lp H 2 μ) n) :
    ‖l2FiniteAssembly (H := H) μ n f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2FiniteAssembly, sumColumns_apply,
    norm_sum_sq_of_pairwise_orthogonal, PiLp.norm_sq_eq_of_L2]
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun t : ℝ => t ^ 2) ((l2MapIsometry μ (finiteCopyIsometry (H := H) i)).norm_map (f i))
  · intro i j hij
    rw [L2.inner_def]
    calc
      (∫ a, inner ℂ (l2MapIsometry μ (finiteCopyIsometry (H := H) i) (f i) a)
          (l2MapIsometry μ (finiteCopyIsometry (H := H) j) (f j) a) ∂μ) = ∫ _a : Ω, (0 : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [l2MapIsometry_ae μ (finiteCopyIsometry (H := H) i) (f i),
          l2MapIsometry_ae μ (finiteCopyIsometry (H := H) j) (f j)] with a hi hj
        rw [hi, hj]
        simp only [finiteCopyIsometry_apply, PiLp.inner_apply, PiLp.single_apply]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hki : k = i
        · subst k
          simp [hij]
        · simp [hki]
      _ = 0 := integral_zero _ _

def finiteCopyProjection {n : ℕ} (i : Fin n) : HilbertCopies H n →L[ℂ] H :=
  PiLp.proj 2 (fun _ : Fin n => H) i

/-- The inverse takes the actual pointwise coordinate projections. -/
def l2FiniteCoordinates (n : ℕ) :
    Lp (HilbertCopies H n) 2 μ →L[ℂ] HilbertCopies (Lp H 2 μ) n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => Lp H 2 μ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (finiteCopyProjection (H := H) i).compLpL 2 μ)

@[simp] theorem l2FiniteCoordinates_apply {n : ℕ}
    (f : Lp (HilbertCopies H n) 2 μ) (i : Fin n) :
    l2FiniteCoordinates (H := H) μ n f i = (finiteCopyProjection (H := H) i).compLpL 2 μ f := rfl

theorem l2FiniteCoordinates_ae {n : ℕ} (f : Lp (HilbertCopies H n) 2 μ) :
    ∀ᵐ a ∂μ, ∀ i : Fin n, l2FiniteCoordinates (H := H) μ n f i a = f a i :=
  eventually_countable_forall.mpr fun i =>
    (finiteCopyProjection (H := H) i).coeFn_compLpL (p := 2) (μ := μ) f

theorem l2FiniteAssembly_coordinates {n : ℕ} (f : Lp (HilbertCopies H n) 2 μ) :
    l2FiniteAssembly (H := H) μ n (l2FiniteCoordinates (H := H) μ n f) = f := by
  apply Lp.ext
  filter_upwards [l2FiniteAssembly_ae μ (l2FiniteCoordinates (H := H) μ n f),
    l2FiniteCoordinates_ae μ f] with a ha hb
  ext i
  exact (ha i).trans (hb i)

/-- The exact unitary identification of finite L² sums. -/
def l2FiniteCopiesEquiv (n : ℕ) :
    HilbertCopies (Lp H 2 μ) n ≃ₗᵢ[ℂ] Lp (HilbertCopies H n) 2 μ :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (l2FiniteAssembly (H := H) μ n).toLinearMap
      norm_map' := l2FiniteAssembly_norm μ }
    (fun f => ⟨l2FiniteCoordinates (H := H) μ n f, l2FiniteAssembly_coordinates μ f⟩)

theorem l2FiniteCopiesEquiv_ae {n : ℕ} (f : HilbertCopies (Lp H 2 μ) n) :
    ∀ᵐ a ∂μ, ∀ i : Fin n, l2FiniteCopiesEquiv (H := H) μ n f a i = f i a :=
  l2FiniteAssembly_ae μ f

end KadisonSimilarity

end

end OAI
