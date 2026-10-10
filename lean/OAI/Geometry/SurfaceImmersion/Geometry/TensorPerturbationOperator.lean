import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPerturbationOperator

namespace OAI

/-! Tensor-valued polynomial perturbations inherit one fixed derivative
budget and one fixed short-scale exponent from their three components. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

def tensorOrder (P : Fin 3 → Fin n → Expression) : ℕ := Finset.univ.sup (fun i => order (P i))
def tensorLoss (P : Fin 3 → Fin n → Expression) : ℕ := Finset.univ.sup (fun i => loss (P i))

def tensorConjugatedLM (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ i l, (P i l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε t : ℝ) :
    SupportedField (F := Fin 4 → ℂ) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K :=
  tupleSupportedLM K (fun i => conjugatedLM hO hU (P i) (hP i) hG hQ K hKU hφ τ ε t)

theorem tensorConjugatedLM_bound {Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQcompact : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ i l, (P i l).SmoothCoeffs O) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (m : ℕ) (B R : ℝ) (hB : 1 ≤ B) (hR : 0 ≤ R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
      (hGQ : Set.MapsTo (lowJet G) U Q) (s : ℝ≥0) (τ ε : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      (∀ v, WeightedBound U s (m + tensorOrder P) R
        (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ H : SupportedField (F := Fin 4 → ℂ) K,
        supportedWeightedSeminorm K s m
          (tensorConjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H) ≤
        D * ε / τ ^ tensorLoss P * supportedWeightedSeminorm K s (m + tensorOrder P) H := by
  classical
  have hex := fun i => conjugatedLM_bound hU hO hQcompact hQO (P i) (hP i) K hKU m B R hB hR
  choose D hD hd using hex
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => hD i), ?_⟩
  intro G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb t ht H
  have hiOrder (i : Fin 3) : order (P i) ≤ tensorOrder P :=
    Finset.le_sup (f := fun j => order (P j)) (Finset.mem_univ i)
  have hiLoss (i : Fin 3) : loss (P i) ≤ tensorLoss P :=
    Finset.le_sup (f := fun j => loss (P j)) (Finset.mem_univ i)
  calc
    _ ≤ ∑ i, supportedWeightedSeminorm K s m
        (conjugatedLM hO hU (P i) (hP i) hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H) :=
      tupleSupportedLM_bound K _ hs m H
    _ ≤ ∑ i, D i * ε / τ ^ tensorLoss P * supportedWeightedSeminorm K s (m + tensorOrder P) H := by
      apply Finset.sum_le_sum
      intro i _
      have hv := hd i G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1
        (hGb.mono_order (Nat.add_le_add_left (hiOrder i) m))
        (fun v => (hφb v).mono_order (Nat.add_le_add_left (hiOrder i) m)) t ht H
      apply hv.trans
      apply mul_le_mul
      · exact div_le_div_of_nonneg_left (mul_nonneg (hD i) hε) (pow_pos hτ _)
          (pow_le_pow_of_le_one hτ.le (hτs.trans hs1) (hiLoss i))
      · exact supportedWeightedSeminorm_mono s (Nat.add_le_add_left (hiOrder i) m) H
      · exact apply_nonneg _ _
      · exact div_nonneg (mul_nonneg (hD i) hε) (pow_nonneg hτ.le _)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.sum_mul]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
