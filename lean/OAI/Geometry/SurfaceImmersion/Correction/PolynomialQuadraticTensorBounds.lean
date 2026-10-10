import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticFamilyBounds
import OAI.Geometry.SurfaceImmersion.Geometry.TensorPerturbationOperator

namespace OAI

/-! The three tensor components use a common derivative order and a common
short-scale exponent, independently of the number of correction steps. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

theorem quadraticFamilyTensor_bound {n : ℕ} {ι : Type*}
    {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : ι → Base → ℝ)
      (H : ι → Base → Fin 4 → ℂ) (s τ ε C : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C →
      ContDiff ℝ ∞ G → (∀ i, ContDiff ℝ ∞ (φ i)) → (∀ i, ContDiff ℝ ∞ (H i)) →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      (∀ i, WeightedBound U s (m + tensorOrder P) C (H i)) →
      (∀ i v, WeightedBound U s (m + tensorOrder P) F
        (fun p => fderiv ℝ (φ i) p (coordinateVector v))) →
      ∀ (l : RealModes.QuadraticLabel ι), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C ^ 2 / τ ^ tensorLoss P)
          (quadraticFamilyTensor P ε G φ H τ t l) := by
  have hex (k : Fin 3) := quadraticFamilyCoefficient_bound (ι := ι)
    hU hO hQ hQO (P k) (hP k) m B F hB hF
  choose E hE he using hex
  let E₀ := ∑ k, E k
  have hE₀ : 0 ≤ E₀ := Finset.sum_nonneg (fun k _ => hE k)
  refine ⟨E₀, hE₀, ?_⟩
  intro G φ H s τ ε C hτ hs hτs hs1 hε hε1 hC hG hφ hH hGQ hGb hHb hφb l t ht
  apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
  · intro k
    exact quadraticFamilyCoefficient_smooth hO (hP k) hG hφ hH
      (fun _ hp => hQO (hGQ hp)) ε τ t l
  · intro k
    have hord : order (P k) ≤ tensorOrder P :=
      Finset.le_sup (f := fun j => order (P j)) (Finset.mem_univ k)
    have hloss : loss (P k) ≤ tensorLoss P :=
      Finset.le_sup (f := fun j => loss (P j)) (Finset.mem_univ k)
    have hb := he k G φ H s τ ε C hτ hs hτs hs1 hε hε1 hC hG hφ hH hGQ
      (hGb.mono_order (Nat.add_le_add_left hord m))
      (fun i => (hHb i).mono_order (Nat.add_le_add_left hord m))
      (fun i v => (hφb i v).mono_order (Nat.add_le_add_left hord m)) l t ht
    apply hb.mono_const
    calc
      _ ≤ E k * ε * C ^ 2 / τ ^ tensorLoss P :=
        div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (hE k) hε) (sq_nonneg C)) (pow_pos hτ _)
          (pow_le_pow_of_le_one hτ.le (hτs.trans hs1) hloss)
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hτ.le _)
        gcongr
        exact Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ k)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
