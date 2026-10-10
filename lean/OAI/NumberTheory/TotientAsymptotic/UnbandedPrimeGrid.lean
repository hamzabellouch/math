import OAI.NumberTheory.TotientAsymptotic.UnbandedCube
import OAI.NumberTheory.TotientAsymptotic.PrimeBoxGeometry

namespace OAI

/-! Prime mass in arbitrary nonnegative prefix regions. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

def tupleUnitGrid {N : ℕ} (Q : Finset (Fin N → ℕ)) : Finset (Fin N → ℕ) :=
  Q.image (fun p i => ⌊primePrefixCoord p i⌋₊+1)

lemma tupleUnitGrid_cell {N : ℕ} {p : Fin N → ℕ}
    (hp : ∀ i, 0 ≤ primePrefixCoord p i) :
    primePrefixCoord p ∈ unitGridCell (fun i => ⌊primePrefixCoord p i⌋₊+1) := by
  intro i _
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  exact ⟨Nat.floor_le (hp i), Nat.lt_floor_add_one _⟩

lemma tupleUnitGrid_cover {N : ℕ} {Q : Finset (Fin N → ℕ)}
    (hp : ∀ p ∈ Q, ∀ i, (p i).Prime ∧ 0 ≤ primePrefixCoord p i) :
    Q ⊆ gridPrimeTuples (tupleUnitGrid Q) := by
  intro p hpQ
  apply Finset.mem_biUnion.mpr
  refine ⟨(fun i => ⌊primePrefixCoord p i⌋₊+1), Finset.mem_image.mpr ⟨p,hpQ,rfl⟩, ?_⟩
  exact mem_primeBoxTuples_iff.mpr ⟨fun i => (hp p hpQ i).1,
    tupleUnitGrid_cell (fun i => (hp p hpQ i).2)⟩

lemma tupleUnitGrid_positive {N : ℕ} {Q : Finset (Fin N → ℕ)}
    {b : Fin N → ℕ} (hb : b ∈ tupleUnitGrid Q) (i : Fin N) : 1 ≤ b i := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hb
  simp only
  omega

lemma sum_exp_neg_linear_prefix {N : ℕ} {c : ℝ} (hc : 0 < c)
    (b : Fin N → ℕ) (hb : ∀ i, c*(N-i.val:ℕ) ≤ (b i:ℝ)) :
    (∑ i, Real.exp (-(b i:ℝ))) ≤ (1-Real.exp (-c))⁻¹ := by
  let q := Real.exp (-c)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := summable_geometric_of_lt_one hq0 hq1
  calc
    _ ≤ ∑ i : Fin N, q^(N-i.val-1) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [q]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hh : ((N-i.val-1:ℕ):ℝ) ≤ (N-i.val:ℕ) := by
        exact_mod_cast Nat.sub_le (N-i.val) 1
      have := mul_le_mul_of_nonneg_left hh hc.le
      linarith [hb i]
    _ = ∑ j ∈ Finset.range N, q^j := by
      apply Finset.sum_bij (fun i _ => N-i.val-1)
      · intro i _
        exact Finset.mem_range.mpr (by omega)
      · intro i _ j _ hij
        apply Fin.ext
        have := i.isLt
        have := j.isLt
        omega
      · intro j hj
        have hj := Finset.mem_range.mp hj
        exact ⟨⟨N-j-1,by omega⟩,Finset.mem_univ _,by simp only; omega⟩
      · intro i _
        rfl
    _ ≤ ∑' j : ℕ, q^j := hs.sum_le_tsum _ (fun _ _ => pow_nonneg hq0 _)
    _ = _ := tsum_geometric_of_lt_one hq0 hq1

/-- A linear lower envelope is enough for a dimension-independent prime
mass factor; no concentration or band assumption is used. -/
theorem unbanded_prime_mass_bound (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (Q : Finset (Fin N → ℕ)) (c A : ℝ),
      0 < c →
      (∀ p ∈ Q, ∀ i, (p i).Prime ∧ c*(N-i.val:ℕ) ≤ primePrefixCoord p i) →
      ((tupleUnitGrid Q).card:ℝ) ≤ A →
      (∑ p ∈ Q, reciprocalShiftWeight p) ≤ Real.exp (C*(1-Real.exp (-c))⁻¹)*A := by
  obtain ⟨C,hC,hgrid⟩ := grid_prime_mass_error_of_sum hford
  refine ⟨C,hC,?_⟩
  intro N Q c A hc hQ hA
  have hp (p) (hpQ : p ∈ Q) (i) : (p i).Prime ∧ 0 ≤ primePrefixCoord p i :=
    ⟨(hQ p hpQ i).1, (mul_nonneg hc.le (Nat.cast_nonneg _)).trans (hQ p hpQ i).2⟩
  have he (b) (hb : b ∈ tupleUnitGrid Q) :
      (∑ i, Real.exp (-(b i:ℝ))) ≤ (1-Real.exp (-c))⁻¹ := by
    apply sum_exp_neg_linear_prefix hc b
    obtain ⟨p,hpQ,rfl⟩ := Finset.mem_image.mp hb
    intro i
    exact (hQ p hpQ i).2.trans (by
      simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (primePrefixCoord p i)).le)
  have hh := (le_abs_self _).trans (hgrid (tupleUnitGrid Q) _
    (fun b hb i => tupleUnitGrid_positive hb i) he)
  calc
    _ ≤ gridPrimeMass (tupleUnitGrid Q) :=
      Finset.sum_le_sum_of_subset_of_nonneg (tupleUnitGrid_cover hp)
        (fun p _ _ => reciprocalShiftWeight_nonneg p)
    _ ≤ Real.exp (C*(1-Real.exp (-c))⁻¹)*(tupleUnitGrid Q).card := by
      nlinarith only [hh]
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le

end TotientAsymptotic

end

end OAI
