import OAI.Geometry.SurfaceImmersion.Geometry.CombinedQuadraticSolverInput
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledQuadraticCancellation
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialProfileTransfer

namespace OAI

/-! Uniform cancellation of the actual perturbed quadratic modes on a local
domain.  Numeric profiles and the compact jet range determine the constants
before the map, amplitudes and scales are supplied. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

theorem uniform_local_quadratic_cancellation {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs O)
    (B F M A : ℕ → ℝ) (hB : ∀ m, 1 ≤ B m) (hF : ∀ m, 0 ≤ F m)
    (hM : ∀ m, 0 ≤ M m) (hA : ∀ m, 0 < A m)
    (C D J I : QuadraticLabel ι → ℕ → ℝ)
    (hC : ∀ l m, 0 ≤ C l m) (hJ : ∀ l m, 1 ≤ J l m)
    (hI : ∀ l m, 1 ≤ I l m) (q : ℕ) :
    ∃ Cv Ct : ℕ → ℝ, (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G)
        (φ : ι → Base → ℝ) (_hφ : ∀ i, ContDiff ℝ ∞ (φ i))
        (K : ι → Compacts Base) (H : ∀ i, SupportedField (F := Fin 4 → ℂ) (K i))
        (s : ℝ≥0) (δ τ ε : ℝ),
      0 < δ → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ tensorLoss P ≤ 1 →
      Set.MapsTo (lowJet G) U Q →
      (∀ m, WeightedBound U s (m + tensorOrder P) (B m) (lowJet G)) →
      (∀ i m, WeightedBound Set.univ s (m + tensorOrder P + 1)
        (A m * (δ * τ)) (H i)) →
      (∀ i m v, WeightedBound U s (m + tensorOrder P) (F m)
        (fun x => fderiv ℝ (φ i) x (coordinateVector v))) →
      (∀ i m v, ‖v‖ ≤ 1 → WeightedBound Set.univ s m (M m)
        (SmallModes.coordDeriv v (coordinatePhase (φ i)))) →
      (∀ l, (quadraticCompacts K l : Set Base) ⊆ U) →
      ∀ (c : ∀ l, PolynomialSolveData P ε G hG (quadraticFamilyPhase φ l)
        (quadraticCompacts K l) τ s),
      (∀ l, (c l).C = C l) → (∀ l, (c l).D = D l) → (∀ l, (c l).J = J l) →
      (∀ l m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c l).e.target,
        ‖iteratedFDerivWithin ℝ j (c l).e.symm (c l).e.target x‖ ≤ I l m) →
      ∃ V : RField 4, ContDiff ℝ ∞ V ∧
        tsupport V ⊆ ⋃ i, (modeSupport (K i) : Set SmallModes.Base) ∧
        (∀ m, WeightedBound Set.univ τ m (δ ^ 2 * Cv m) V) ∧
        (∀ m, WeightedBound Set.univ τ m
          (δ ^ 2 * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) * Ct m)
          (coordinateFullLinearized P ε G V +
            combinedNonzeroQuadratic P ε G φ (fun i => H i) τ)) := by
  classical
  choose E hE he using fun m => combined_quadratic_solver_input_bound (ι := ι)
    hU hO hQ hQO P hP m (B m) (F m) (M m) (A m) (hB m) (hF m) (hM m) (hA m)
  let b : QuadraticLabel ι → ℕ → ℝ := fun l m =>
    tensorChartBudget m (I l m) (I l (m + 1)) * E m
  have hb (l : QuadraticLabel ι) (m : ℕ) : 0 ≤ b l m :=
    mul_nonneg (tensorChartBudget_nonneg m (zero_le_one.trans (hI l m))
      (zero_le_one.trans (hI l (m + 1)))) (hE m)
  let Cv : ℕ → ℝ := fun m => ∑ l,
    PolynomialSolveData.sizeProfile P (C l) (D l) (J l) q m *
      b l (PolynomialSolveData.inputOrder (P := P) q m)
  let Ct : ℕ → ℝ := fun m => ∑ l,
    PolynomialSolveData.residualProfile P (C l) (D l) (J l) q m *
      b l (PolynomialSolveData.inputOrder (P := P) q m)
  refine ⟨Cv,Ct,?_,?_,?_⟩
  · intro m
    exact Finset.sum_nonneg (fun l _ => mul_nonneg
      (PolynomialSolveData.sizeProfile_nonneg P (C l) (D l) (J l) (hC l)
        (fun j => zero_le_one.trans (hJ l j)) q m) (hb l _))
  · intro m
    exact Finset.sum_nonneg (fun l _ => mul_nonneg
      (PolynomialSolveData.residualProfile_nonneg P (C l) (D l) (J l) (hC l)
        (fun j => zero_le_one.trans (hJ l j)) q m) (hb l _))
  · intro G hG φ hφ K H s δ τ ε hδ hτ hs hτs hs1 hε hε1 hsmall
      hGQ hGb hHb hφb hφm hKU c hc hd hj hi
    let f := fun l => combinedQuadraticTarget (c l).openU (c l).openO P
      (c l).smoothP hG φ hφ H (c l).mapsG l (c l).supportU ε τ 0
    have hf (l : QuadraticLabel ι) : f l =
        combinedQuadraticTarget hU hO P hP hG φ hφ H
          (fun _ hx => hQO (hGQ hx)) l (hKU l) ε τ 0 :=
      combinedQuadraticTarget_domain_independent (c l).openU hU (c l).openO hO
        P (c l).smoothP hP hG φ hφ H (c l).mapsG
        (fun _ hx => hQO (hGQ hx)) l (c l).supportU (hKU l) ε τ 0
    have hn (l : QuadraticLabel ι) (m : ℕ) :
        (c l).norm (f l) m ≤ δ ^ 2 * b l m := by
      rw [hf l]
      simpa only [b, mul_assoc] using he m hG φ hφ K H s δ τ ε
        hδ hτ hs hτs hs1 hε hε1 hsmall hGQ (hGb m) (fun i => hHb i m)
        (fun i => hφb i m) (fun i => hφm i m) l (hKU l) (c l) (I l) (hI l) (hi l)
    obtain ⟨V,hV,hsp,hsize,hres⟩ := scaled_polynomial_quadratic_cancellation
      P ε δ hG φ hφ K H c hτ hs hτs hs1 hε hsmall q b hn
    have hcv (m : ℕ) : (∑ l, (c l).sizeFactor q m *
        b l (PolynomialSolveData.inputOrder (P := P) q m)) = Cv m := by
      apply Finset.sum_congr rfl
      intro l _
      rw [(c l).sizeFactor_eq_sizeProfile (hc l) (hd l) (hj l)]
    have hct (m : ℕ) : (∑ l, (c l).residualFactor q m *
        b l (PolynomialSolveData.inputOrder (P := P) q m)) = Ct m := by
      apply Finset.sum_congr rfl
      intro l _
      rw [(c l).residualFactor_eq_residualProfile (hc l) (hd l) (hj l)]
    exact ⟨V,hV,hsp,(fun m => by simpa only [hcv m] using hsize m),
      (fun m => by simpa only [hct m] using hres m)⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
