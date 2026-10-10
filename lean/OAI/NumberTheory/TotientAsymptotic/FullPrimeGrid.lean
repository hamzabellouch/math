import OAI.NumberTheory.TotientAsymptotic.BasicCube
import OAI.NumberTheory.TotientAsymptotic.BandGrid
import OAI.NumberTheory.TotientAsymptotic.GridApproximation

namespace OAI

/-! The actual full prime tuples are controlled by one enlarged-simplex
volume, with the discrete cofactor kept separate. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def fullPrimeGrid (x : ℝ) (H : ℕ) : Finset (Fin (L x H) → ℕ) :=
  (bandGrid x (P H)).filter (fun b =>
    ∃ p ∈ fullPrimeTuples x H, primePrefixCoord p ∈ unitGridCell b)

lemma fullPrimeTuples_subset_grid (x : ℝ) (H : ℕ) :
    fullPrimeTuples x H ⊆ gridPrimeTuples (fullPrimeGrid x H) := by
  intro p hp
  obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hp
  have hbasic := mem_basicRemainderFinset.mp hη
  have hbands : primePrefixCoord η.primes ∈ prefixBandRegion x (P H) := by
    intro i
    have hi : i.val < L x H := by simpa only [R, L] using i.isLt
    have hh := (hbasic.2.1 (i.val+1)
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).2
    rw [remainderCoord_fin x η i] at hh
    exact hh
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (prefixBandRegion_covered x (P H) hbands)
  obtain ⟨hb, hc⟩ := Set.mem_iUnion.mp hb
  apply Finset.mem_biUnion.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨hb, η.primes, ?_, hc⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨η, hη, rfl⟩
  · apply mem_primeBoxTuples_iff.mpr
    refine ⟨fun i => ?_, hc⟩
    have hh := (hbasic.2.1 (i.val+1)
      (Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩)).1
    simpa [remainderPrime, i.isLt] using hh

lemma fullPrimeGrid_enclosure {x : ℝ} {H : ℕ}
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(P H : ℝ)) (hB : 0 < B x)
    (hscale : (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam) (hL : 0 < L x H) :
    gridRegion (fullPrimeGrid x H) ⊆ enlargedSimplex (L x H) (B x)
      (1+simplexBoxError 4 (m x))
      (fun i => 1+simplexBoxError 4 (m x-(i.val+1))) := by
  intro v hv
  obtain ⟨b, hv⟩ := Set.mem_iUnion.mp hv
  obtain ⟨hb, hv⟩ := Set.mem_iUnion.mp hv
  obtain ⟨_, p, hp, hu⟩ := Finset.mem_filter.mp hb
  obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hp
  exact basic_prime_box_enclosure hs hcut hB hscale hL
    (mem_basicRemainderFinset.mp hη) (unitGridCell_coordinate_distance hu hv)

lemma volume_zero_prefixRegion {x : ℝ} {N : ℕ} (hB : 0 ≤ B x) (hN : 0 < N) :
    volume (prefixRegion N (B x) 0 0) = ENNReal.ofReal (G x N) := by
  rw [volume_prefixRegion_explicit N hN]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero, max_eq_left hB]
  rw [G, prod_fin_shifted N g]

theorem fullPrimeGrid_volume_bound {x : ℝ} {H : ℕ}
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(P H : ℝ)) (hB : 0 < B x)
    (hscale : (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam) (hL : 0 < L x H) :
    volume.real (gridRegion (fullPrimeGrid x H)) ≤
      Real.exp (simplexBoxTail 4 (P H))*G x (L x H) := by
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 4 (m x-r)
  have hβ : ∀ r, 1 ≤ β r := fun r => by
    dsimp [β]
    linarith [simplexBoxError_nonneg (by norm_num : (0 : ℝ) ≤ 4) (m x-r)]
  have hPm : P H ≤ m x := by unfold L at hL; omega
  have hj := reverse_enlargement_jacobian hPm (simplexBoxError 4)
    (simplexBoxError_nonneg (by norm_num)) (summable_simplexBoxError_weighted 4)
  rw [← simplexBoxTail_eq_tsum] at hj
  have he : volume (gridRegion (fullPrimeGrid x H)) ≤
      ENNReal.ofReal (Real.exp (simplexBoxTail 4 (P H))*G x (L x H)) := by
    calc
      _ ≤ volume (enlargedSimplex (L x H) (B x) (β 0)
          (fun i => β (i.val+1))) := by
        apply measure_mono
        simpa only [β, Nat.sub_zero] using fullPrimeGrid_enclosure hs hcut hB hscale hL
      _ ≤ ENNReal.ofReal (∏ i : Fin (L x H), enlargementScale β i)*
          volume (prefixRegion (L x H) (B x) 0 0) :=
        volume_enlargedSimplex_product_bound (B x) β hβ
      _ ≤ ENNReal.ofReal (Real.exp (simplexBoxTail 4 (P H)))*
          volume (prefixRegion (L x H) (B x) 0 0) := by
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hj) le_rfl
      _ = _ := by
        rw [volume_zero_prefixRegion hB.le hL, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (G_pos hB _).le))

/-- Full prime mass, before the independent smooth-cofactor sum. -/
theorem full_prime_mass_bound (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x : ℝ} {H : ℕ},
      0 ≤ theta x → 4 ≤ lam*(P H : ℝ) → 0 < B x →
      (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam → 0 < L x H →
      (∑ p ∈ fullPrimeTuples x H, reciprocalShiftWeight p) ≤
        (1+bandPrimeError C (9/10) (P H))*
          Real.exp (simplexBoxTail 4 (P H))*G x (L x H) := by
  obtain ⟨C, hC, hc⟩ := banded_grid_prime_mass_error hford
  refine ⟨C, hC, ?_⟩
  intro x H hs hcut hB hscale hL
  have hPm : P H ≤ m x := by unfold L at hL; omega
  have hh := hc hs (by norm_num : (0 : ℝ)<9/10) hPm (fullPrimeGrid x H) (by
    intro b hb i
    exact bandGrid_bounds (Finset.mem_filter.mp hb).1 i)
  change |gridPrimeMass (N := L x H) (fullPrimeGrid x H) -
    (volume (gridRegion (N := L x H) (fullPrimeGrid x H))).toReal| ≤
    (volume (gridRegion (N := L x H) (fullPrimeGrid x H))).toReal *
      bandPrimeError C (9/10) (P H) at hh
  have hnon : 0 ≤ 1+bandPrimeError C (9/10) (P H) := by
    linarith [bandPrimeError_nonneg hC.le (by norm_num : (0 : ℝ)<9/10) (P H)]
  calc
    _ ≤ gridPrimeMass (fullPrimeGrid x H) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (fullPrimeTuples_subset_grid x H)
      intro p _ _
      exact reciprocalShiftWeight_nonneg p
    _ ≤ (1+bandPrimeError C (9/10) (P H))*volume.real (gridRegion (fullPrimeGrid x H)) := by
      have he := (le_abs_self _).trans hh
      change gridPrimeMass _-(volume (gridRegion _)).toReal ≤ _ at he
      change gridPrimeMass _ ≤ _*(volume (gridRegion _)).toReal
      calc
        _ ≤ (volume (gridRegion (fullPrimeGrid x H))).toReal +
            (volume (gridRegion (fullPrimeGrid x H))).toReal * bandPrimeError C (9/10) (P H) := by
          exact (sub_le_iff_le_add.mp he).trans_eq (add_comm _ _)
        _ = _ := by ring
    _ ≤ (1+bandPrimeError C (9/10) (P H))*
        (Real.exp (simplexBoxTail 4 (P H))*G x (L x H)) :=
      mul_le_mul_of_nonneg_left (fullPrimeGrid_volume_bound hs hcut hB hscale hL) hnon
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
