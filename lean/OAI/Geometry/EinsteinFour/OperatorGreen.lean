import OAI.Geometry.EinsteinFour.FlowGreen
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! Weighted integration by parts retains the derivative of a varying
matrix-slot coefficient. The Weyl Hessian calculation applies the flow Green identity twice
to the nonparallel coefficient. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (μ : Measure Ω) [IsFiniteMeasure μ]

/-- The first and second derivatives of the varying coefficient contribute
exactly the one-half correction. No coefficient is assumed parallel. -/
theorem weighted_operator_green
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hμ : ∀ t, MeasurePreserving (φ t) μ μ)
    (m dm : C(Ω, ℝ)) (f df ddf : C(Ω, E))
    (A dA ddA : C(Ω, E →L[ℝ] E))
    (hself : ∀ x u v, inner ℝ (dA x u) v = inner ℝ u (dA x v))
    (hm : ∀ t x, HasDerivAt (fun s => m (φ s x)) (dm (φ t x)) t)
    (hf : ∀ t x, HasDerivAt (fun s => f (φ s x)) (df (φ t x)) t)
    (hdf : ∀ t x, HasDerivAt (fun s => df (φ s x)) (ddf (φ t x)) t)
    (hA : ∀ t x, HasDerivAt (fun s => A (φ s x)) (dA (φ t x)) t)
    (hdA : ∀ t x, HasDerivAt (fun s => dA (φ s x)) (ddA (φ t x)) t) :
    (∫ x, m x * inner ℝ (df x) (A x (df x)) +
      dm x * inner ℝ (f x) (A x (df x)) ∂μ) =
      -(∫ x, m x * inner ℝ (f x) (A x (ddf x)) ∂μ) +
        (1 / 2 : ℝ) * (∫ x, m x * inner ℝ (f x) (ddA x (f x)) +
          dm x * inner ℝ (f x) (dA x (f x)) ∂μ) := by
  let V : C(Ω, E) := ⟨fun x => A x (df x), by fun_prop⟩
  let dV : C(Ω, E) := ⟨fun x => dA x (df x) + A x (ddf x), by fun_prop⟩
  let W : C(Ω, E) := ⟨fun x => dA x (f x), by fun_prop⟩
  let dW : C(Ω, E) := ⟨fun x => ddA x (f x) + dA x (df x), by fun_prop⟩
  have hV (t : ℝ) (x : Ω) :
      HasDerivAt (fun s => V (φ s x)) (dV (φ t x)) t :=
    (hA t x).clm_apply (hdf t x)
  have hW (t : ℝ) (x : Ω) :
      HasDerivAt (fun s => W (φ s x)) (dW (φ t x)) t :=
    (hdA t x).clm_apply (hf t x)
  have h1 := weighted_flow_green μ φ hφ hμ m dm f df V dV hm hf hV
  have h2 := weighted_flow_green μ φ hφ hμ m dm f df W dW hm hf hW
  have hK : Integrable (fun x => m x * inner ℝ (f x) (dA x (df x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ : Integrable (fun x => m x * inner ℝ (f x) (A x (ddf x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hQ : Integrable (fun x => m x * inner ℝ (f x) (ddA x (f x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (fun x => dm x * inner ℝ (f x) (dA x (f x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs (x : Ω) : inner ℝ (df x) (dA x (f x)) =
      inner ℝ (f x) (dA x (df x)) := by
    rw [real_inner_comm (dA x (f x)) (df x)]
    exact hself x (f x) (df x)
  change (∫ x, m x * inner ℝ (df x) (A x (df x)) +
    dm x * inner ℝ (f x) (A x (df x)) ∂μ) =
      -(∫ x, m x * inner ℝ (f x) (dA x (df x) + A x (ddf x)) ∂μ) at h1
  simp_rw [inner_add_right, mul_add] at h1
  rw [integral_add hK hJ] at h1
  change (∫ x, m x * inner ℝ (df x) (dA x (f x)) +
    dm x * inner ℝ (f x) (dA x (f x)) ∂μ) =
      -(∫ x, m x * inner ℝ (f x) (ddA x (f x) + dA x (df x)) ∂μ) at h2
  simp_rw [hs, inner_add_right, mul_add] at h2
  rw [integral_add hK hR, integral_add hQ hK] at h2
  rw [integral_add hQ hR]
  linarith

/-- The nonparallel coefficient identity summed over the four tangent
directions. The correction retains both its Laplacian and the weight gradient. -/
theorem weighted_four_operator_green
    (φ : Fin 4 → ℝ → Ω ≃ᵐ Ω)
    (hφ : ∀ i, Continuous (fun p : ℝ × Ω => φ i p.1 p.2))
    (hμ : ∀ i t, MeasurePreserving (φ i t) μ μ)
    (m : C(Ω, ℝ)) (dm : Fin 4 → C(Ω, ℝ))
    (f : C(Ω, E)) (df ddf : Fin 4 → C(Ω, E))
    (A : C(Ω, E →L[ℝ] E)) (dA ddA : Fin 4 → C(Ω, E →L[ℝ] E))
    (hself : ∀ i x u v, inner ℝ (dA i x u) v = inner ℝ u (dA i x v))
    (hm : ∀ i t x, HasDerivAt (fun s => m (φ i s x)) (dm i (φ i t x)) t)
    (hf : ∀ i t x, HasDerivAt (fun s => f (φ i s x)) (df i (φ i t x)) t)
    (hdf : ∀ i t x, HasDerivAt (fun s => df i (φ i s x)) (ddf i (φ i t x)) t)
    (hA : ∀ i t x, HasDerivAt (fun s => A (φ i s x)) (dA i (φ i t x)) t)
    (hdA : ∀ i t x, HasDerivAt (fun s => dA i (φ i s x)) (ddA i (φ i t x)) t) :
    (∫ x, m x * (∑ i, inner ℝ (df i x) (A x (df i x))) +
      ∑ i, dm i x * inner ℝ (f x) (A x (df i x)) ∂μ) =
      -(∫ x, m x * inner ℝ (f x) (A x (∑ i, ddf i x)) ∂μ) +
        (1 / 2 : ℝ) * (∫ x, m x * inner ℝ (f x) (∑ i, ddA i x (f x)) +
          ∑ i, dm i x * inner ℝ (f x) (dA i x (f x)) ∂μ) := by
  have hL (i : Fin 4) : Integrable (fun x =>
      m x * inner ℝ (df i x) (A x (df i x)) +
        dm i x * inner ℝ (f x) (A x (df i x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ (i : Fin 4) : Integrable
      (fun x => m x * inner ℝ (f x) (A x (ddf i x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hC (i : Fin 4) : Integrable (fun x =>
      m x * inner ℝ (f x) (ddA i x (f x)) +
        dm i x * inner ℝ (f x) (dA i x (f x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum :
      (∫ x, ∑ i, (m x * inner ℝ (df i x) (A x (df i x)) +
        dm i x * inner ℝ (f x) (A x (df i x))) ∂μ) =
      -(∫ x, ∑ i, m x * inner ℝ (f x) (A x (ddf i x)) ∂μ) +
        (1 / 2 : ℝ) * (∫ x, ∑ i, (m x * inner ℝ (f x) (ddA i x (f x)) +
          dm i x * inner ℝ (f x) (dA i x (f x))) ∂μ) := by
    rw [integral_finsetSum _ (fun i _ => hL i),
      integral_finsetSum _ (fun i _ => hJ i),
      integral_finsetSum _ (fun i _ => hC i)]
    simp_rw [weighted_operator_green μ _ (hφ _) (hμ _) m (dm _) f (df _) (ddf _)
      A (dA _) (ddA _) (hself _) (hm _) (hf _) (hdf _) (hA _) (hdA _)]
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  simpa only [Finset.sum_add_distrib, Finset.mul_sum, inner_sum, map_sum] using hsum

/-- A variable scalar tensor coefficient contributes its divergence term.
Summing this identity is the derivative-slot curvature integration step. -/
theorem weighted_scalar_coefficient_green
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hμ : ∀ t, MeasurePreserving (φ t) μ μ)
    (m dm a da : C(Ω, ℝ)) (f df g dg : C(Ω, E))
    (hm : ∀ t x, HasDerivAt (fun s => m (φ s x)) (dm (φ t x)) t)
    (ha : ∀ t x, HasDerivAt (fun s => a (φ s x)) (da (φ t x)) t)
    (hf : ∀ t x, HasDerivAt (fun s => f (φ s x)) (df (φ t x)) t)
    (hg : ∀ t x, HasDerivAt (fun s => g (φ s x)) (dg (φ t x)) t) :
    (∫ x, m x * a x * inner ℝ (f x) (dg x) +
      dm x * a x * inner ℝ (f x) (g x) ∂μ) =
      -(∫ x, m x * a x * inner ℝ (df x) (g x) ∂μ) -
        ∫ x, m x * da x * inner ℝ (f x) (g x) ∂μ := by
  let w : C(Ω, ℝ) := ⟨fun x => m x * a x, by fun_prop⟩
  let dw : C(Ω, ℝ) := ⟨fun x => dm x * a x + m x * da x, by fun_prop⟩
  have hw (t : ℝ) (x : Ω) :
      HasDerivAt (fun s => w (φ s x)) (dw (φ t x)) t := (hm t x).mul (ha t x)
  have h := weighted_flow_green μ φ hφ hμ w dw f df g dg hw hf hg
  have hA : Integrable (fun x => m x * a x * inner ℝ (f x) (dg x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (fun x => dm x * a x * inner ℝ (f x) (g x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ : Integrable (fun x => m x * a x * inner ℝ (df x) (g x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hK : Integrable (fun x => m x * da x * inner ℝ (f x) (g x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (fun x => w x * inner ℝ (df x) (g x) + dw x * inner ℝ (f x) (g x)) =
      (fun x => (m x * a x * inner ℝ (df x) (g x) +
        dm x * a x * inner ℝ (f x) (g x)) + m x * da x * inner ℝ (f x) (g x)) := by
    funext x
    dsimp [w, dw]
    ring
  have hJB : Integrable (fun x => m x * a x * inner ℝ (df x) (g x) +
      dm x * a x * inner ℝ (f x) (g x)) μ := hJ.add hB
  rw [he, integral_add hJB hK, integral_add hJ hB] at h
  change _ = -(∫ x, m x * a x * inner ℝ (f x) (dg x) ∂μ) at h
  rw [integral_add hA hB]
  linarith

end

end PositiveEinsteinFour.Averages

end OAI
