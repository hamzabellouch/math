import OAI.Combinatorics.Progressions.Sampling.AllocatedGridlessProfileBound

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_allocated_grid_fourier_approximation
    (C : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hJ : (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ P)
    (hL : ((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} : ℝ) *
      (Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (2 * ((S.value : ℝ) ^ (layerTailDegree m + 1)) ^ 2))) *
      (∑ j, (C j : ℝ) * Fintype.card (J j)) ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ g : (JetAmbientIndex O J → UnitAddCircle) → ℝ,
      (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      (∀ w : JetAmbientIndex O J → ℝ, (∀ i, |w i| ≤ 1 / 4) →
        g (fun i => (w i : UnitAddCircle)) =
          allocatedNormalizedGridInterpolation B U b hR hσ S u rows
            (allocatedGridAmbientCoordinates B U b S o w)) ∧
      ∃ (F : Type) (inst : Fintype F), letI := inst
        ∃ (frequency : F → JetAmbientIndex O J → ℤ) (c : F → ℂ),
          (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
          (∀ a j, |(frequency a j : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
          (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
          ∀ z, ‖(g z : ℂ) -
            ∑ a, c a * ∏ j, CircleFourier.character (frequency a j • z j)‖ ≤ δ := by
  obtain ⟨g, hg, hunit, hvalue⟩ :=
    exists_allocated_ambient_grid_factor_uniform B U b hR hσ S u rows o C hC
  let L : ℝ≥0 := (Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} *
    (Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
      (2 * ((S.value : ℝ≥0) ^ (layerTailDegree m + 1)) ^ 2))) *
    (∑ j, C j * Fintype.card (J j))
  have hcomplex : LipschitzWith L (fun z => (g z : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [Complex.isometry_ofReal.dist_eq]
    exact hg.dist_le_mul z w
  have hbound : ∀ z, ‖(g z : ℂ)‖ ≤ (1 : ℝ≥0) := by
    intro z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hunit z).1]
    exact (hunit z).2
  have hLc : (L : ℝ) ≤ Real.exp P := by
    simpa only [L, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_sum,
      NNReal.coe_ofNat] using hL
  obtain ⟨F, inst, frequency, c, hcard, hfrequency, hmass, herr⟩ :=
    exists_ambient_torus_fourier_approximation (fun z => (g z : ℂ)) _ 1 hcomplex
      hbound hδ hP hJ hLc hδP
  refine ⟨g, hunit, hvalue, F, inst, frequency, c, hcard, hfrequency, ?_, herr⟩
  simpa only [NNReal.coe_one, mul_one] using hmass

end Erdos3.VectorPolynomial

end

end OAI
