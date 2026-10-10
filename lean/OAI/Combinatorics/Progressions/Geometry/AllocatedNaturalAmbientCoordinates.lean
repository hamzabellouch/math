import OAI.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {A : Type*} [Fintype A] (layer : A → Fin m) (axis : ∀ a, Fin (n (layer a)))
variable (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨layer a, Sum.inr (axis a)⟩)

noncomputable def allocatedNaturalGridAmbientCoordinates (z : JetAmbientIndex O J → ℝ) :
    ∀ a : A, O (layer a) → ℝ :=
  fun a t => allocatedPrincipalChartRatio (G := G) B U basis (R := R) (layer a) (axis a) *
    allocatedGridAmbientCoordinates B U basis S o z ⟨⟨layer a, Sum.inr (axis a)⟩, hgrid a⟩ t

omit [Fintype A] [∀ j, Fintype (O j)] in
theorem allocatedNaturalGridAmbientCoordinates_point
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    allocatedNaturalGridAmbientCoordinates B U basis S o layer axis hgrid
        (mixedJetAmbientPoint U basis o z) =
      fun a t => ((z (layer a)).2 (axis a) t : ℝ) /
        allocatedPrincipalGridScale (G := G) B U basis (R := R) (layer a) (axis a) := by
  funext a t
  unfold allocatedNaturalGridAmbientCoordinates
  rw [allocatedGridAmbientCoordinates_point]
  change allocatedPrincipalChartRatio (G := G) B U basis (R := R) (layer a) (axis a) *
      (((z (layer a)).2 (axis a) t : ℝ) / basisAxisScale (basis (layer a)) (axis a)) = _
  exact allocatedPrincipalChartRatio_coordinate B U basis (layer a) (axis a) _

theorem allocatedNaturalGridAmbientCoordinates_lipschitz
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ C j * ‖v‖)
    (Q : ℝ≥0)
    (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B (layer a) (axis a)) : ℝ) + 1) /
      R (layer a) ≤ Q) :
    LipschitzWith (Q * ∑ j, C j * Fintype.card (J j))
      (allocatedNaturalGridAmbientCoordinates B U basis S (O := O) o layer axis hgrid) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  apply (dist_pi_le_iff (by positivity)).mpr
  intro t
  let g := allocatedGridAmbientCoordinates B U basis S (O := O) o
  let k : {k // allocatedGridAxis (I := I) U basis S.value k} :=
    ⟨⟨layer a, Sum.inr (axis a)⟩, hgrid a⟩
  have hc : |g z k t - g w k t| ≤
      ((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w := by
    have hi := (dist_le_pi_dist (g z k) (g w k) t).trans (dist_le_pi_dist (g z) (g w) k)
    exact hi.trans ((allocatedGridAmbientCoordinates_lipschitz B U basis S o C hC).dist_le_mul z w)
  change |allocatedPrincipalChartRatio (G := G) B U basis (R := R) (layer a) (axis a) * g z k t -
    allocatedPrincipalChartRatio (G := G) B U basis (R := R) (layer a) (axis a) * g w k t| ≤ _
  rw [← mul_sub, abs_mul, abs_of_pos (allocatedPrincipalChartRatio_pos B U basis hR (layer a) (axis a))]
  calc
    _ ≤ (Q : ℝ) * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) :=
      mul_le_mul ((allocatedPrincipalChartRatio_le B U basis hR (layer a) (axis a)).trans (hQ a))
        hc (abs_nonneg _) Q.coe_nonneg
    _ = _ := by rw [NNReal.coe_mul, mul_assoc]

end Erdos3.VectorPolynomial

end

end OAI
