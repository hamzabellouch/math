import OAI.NumberTheory.TotientAsymptotic.ProjectedCube
import OAI.NumberTheory.TotientAsymptotic.BandGrid
import OAI.NumberTheory.TotientAsymptotic.GridApproximation

namespace OAI

/-! A projected prime prefix has mass bounded by its own simplex volume. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def projectedPrimeGrid (x : ℝ) (K : ℕ) (Q : Finset (Fin (R x K) → ℕ)) : Finset (Fin (R x K) → ℕ) :=
  (bandGrid x K).filter (fun b =>
    ∃ p ∈ Q, primePrefixCoord p ∈ unitGridCell b)

lemma projectedPrimeTuples_subset_grid (x : ℝ) (K : ℕ) (Q : Finset (Fin (R x K) → ℕ))
    (hQ : ∀ p ∈ Q, (∀ i, (p i).Prime) ∧ primePrefixCoord p ∈ prefixBandRegion x K) :
    Q ⊆ gridPrimeTuples (projectedPrimeGrid x K Q) := by
  intro p hp
  have hbands := (hQ p hp).2
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (prefixBandRegion_covered x (K) hbands)
  obtain ⟨hb, hc⟩ := Set.mem_iUnion.mp hb
  apply Finset.mem_biUnion.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨hb, p, hp, hc⟩, ?_⟩
  apply mem_primeBoxTuples_iff.mpr
  exact ⟨(hQ p hp).1,hc⟩

lemma projectedPrimeGrid_enclosure {x : ℝ} {K : ℕ} (Q : Finset (Fin (R x K) → ℕ))
    (hQ : ∀ p ∈ Q, primePrefixCoord p ∈ prefixBandRegion x K ∧
      primePrefixCoord p ∈ enlargedSimplex (R x K) (B x) (xi x 0) (fun i => xi x (i.val+1)))
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(K : ℝ)) (hB : 0 < B x)
    (hscale : (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam) (hL : 0 < R x K) :
    gridRegion (projectedPrimeGrid x K Q) ⊆ enlargedSimplex (R x K) (B x)
      (1+simplexBoxError 4 (m x))
      (fun i => 1+simplexBoxError 4 (m x-(i.val+1))) := by
  intro v hv
  obtain ⟨b, hv⟩ := Set.mem_iUnion.mp hv
  obtain ⟨hb, hv⟩ := Set.mem_iUnion.mp hv
  obtain ⟨_, p, hp, hu⟩ := Finset.mem_filter.mp hb
  exact projected_prime_box_enclosure hs hcut hB hscale hL
    (hQ p hp).2 (fun i => ((hQ p hp).1 i).1) (unitGridCell_coordinate_distance hu hv)

lemma projected_volume_zero_prefixRegion {x : ℝ} {N : ℕ} (hB : 0 ≤ B x) (hN : 0 < N) :
    volume (prefixRegion N (B x) 0 0) = ENNReal.ofReal (G x N) := by
  rw [volume_prefixRegion_explicit N hN]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero, max_eq_left hB]
  rw [G, prod_fin_shifted N g]

theorem projectedPrimeGrid_volume_bound {x : ℝ} {K : ℕ} (Q : Finset (Fin (R x K) → ℕ))
    (hQ : ∀ p ∈ Q, primePrefixCoord p ∈ prefixBandRegion x K ∧
      primePrefixCoord p ∈ enlargedSimplex (R x K) (B x) (xi x 0) (fun i => xi x (i.val+1)))
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(K : ℝ)) (hB : 0 < B x)
    (hscale : (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam) (hL : 0 < R x K) :
    volume.real (gridRegion (projectedPrimeGrid x K Q)) ≤
      Real.exp (simplexBoxTail 4 (K))*G x (R x K) := by
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 4 (m x-r)
  have hβ : ∀ r, 1 ≤ β r := fun r => by
    dsimp [β]
    linarith [simplexBoxError_nonneg (by norm_num : (0 : ℝ) ≤ 4) (m x-r)]
  have hPm : K ≤ m x := by unfold R at hL; omega
  have hj := reverse_enlargement_jacobian hPm (simplexBoxError 4)
    (simplexBoxError_nonneg (by norm_num)) (summable_simplexBoxError_weighted 4)
  rw [← simplexBoxTail_eq_tsum] at hj
  have he : volume (gridRegion (projectedPrimeGrid x K Q)) ≤
      ENNReal.ofReal (Real.exp (simplexBoxTail 4 (K))*G x (R x K)) := by
    calc
      _ ≤ volume (enlargedSimplex (R x K) (B x) (β 0)
          (fun i => β (i.val+1))) := by
        apply measure_mono
        simpa only [β, Nat.sub_zero] using projectedPrimeGrid_enclosure Q hQ hs hcut hB hscale hL
      _ ≤ ENNReal.ofReal (∏ i : Fin (R x K), enlargementScale β i)*
          volume (prefixRegion (R x K) (B x) 0 0) :=
        volume_enlargedSimplex_product_bound (B x) β hβ
      _ ≤ ENNReal.ofReal (Real.exp (simplexBoxTail 4 (K)))*
          volume (prefixRegion (R x K) (B x) 0 0) := by
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hj) le_rfl
      _ = _ := by
        rw [projected_volume_zero_prefixRegion hB.le hL, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (G_pos hB _).le))

/-- Full prime mass, before the independent smooth-cofactor sum. -/
theorem projected_prime_mass_bound (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x : ℝ} {K : ℕ},
      0 ≤ theta x → 4 ≤ lam*(K : ℝ) → 0 < B x →
      (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam → 0 < R x K →
      ∀ Q : Finset (Fin (R x K) → ℕ),
      (∀ p ∈ Q, (∀ i, (p i).Prime) ∧ primePrefixCoord p ∈ prefixBandRegion x K ∧
        primePrefixCoord p ∈ enlargedSimplex (R x K) (B x) (xi x 0) (fun i => xi x (i.val+1))) →
      (∑ p ∈ Q, reciprocalShiftWeight p) ≤
        (1+bandPrimeError C (9/10) (K))*
          Real.exp (simplexBoxTail 4 (K))*G x (R x K) := by
  obtain ⟨C, hC, hc⟩ := banded_grid_prime_mass_error hford
  refine ⟨C, hC, ?_⟩
  intro x K hs hcut hB hscale hL Q hQ
  have hPm : K ≤ m x := by unfold R at hL; omega
  have hh := hc hs (by norm_num : (0 : ℝ)<9/10) hPm (projectedPrimeGrid x K Q) (by
    intro b hb i
    exact bandGrid_bounds (Finset.mem_filter.mp hb).1 i)
  change |gridPrimeMass (N := R x K) (projectedPrimeGrid x K Q) -
    (volume (gridRegion (N := R x K) (projectedPrimeGrid x K Q))).toReal| ≤
    (volume (gridRegion (N := R x K) (projectedPrimeGrid x K Q))).toReal *
      bandPrimeError C (9/10) (K) at hh
  have hnon : 0 ≤ 1+bandPrimeError C (9/10) (K) := by
    linarith [bandPrimeError_nonneg hC.le (by norm_num : (0 : ℝ)<9/10) (K)]
  calc
    _ ≤ gridPrimeMass (projectedPrimeGrid x K Q) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (projectedPrimeTuples_subset_grid x K Q (fun p hp => ⟨(hQ p hp).1,(hQ p hp).2.1⟩))
      intro p _ _
      exact reciprocalShiftWeight_nonneg p
    _ ≤ (1+bandPrimeError C (9/10) (K))*volume.real (gridRegion (projectedPrimeGrid x K Q)) := by
      have he := (le_abs_self _).trans hh
      change gridPrimeMass _-(volume (gridRegion _)).toReal ≤ _ at he
      change gridPrimeMass _ ≤ _*(volume (gridRegion _)).toReal
      calc
        _ ≤ (volume (gridRegion (projectedPrimeGrid x K Q))).toReal +
            (volume (gridRegion (projectedPrimeGrid x K Q))).toReal * bandPrimeError C (9/10) (K) := by
          exact (sub_le_iff_le_add.mp he).trans_eq (add_comm _ _)
        _ = _ := by ring
    _ ≤ (1+bandPrimeError C (9/10) (K))*
        (Real.exp (simplexBoxTail 4 (K))*G x (R x K)) :=
      mul_le_mul_of_nonneg_left (projectedPrimeGrid_volume_bound Q (fun p hp => (hQ p hp).2) hs hcut hB hscale hL) hnon
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
