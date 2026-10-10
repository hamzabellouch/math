import OAI.NumberTheory.TotientAsymptotic.TailEncoding
import OAI.NumberTheory.TotientAsymptotic.BandPrimeError

namespace OAI

/-! Uniform prime mass for the boxes occupied by discrete witness tails. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def tailBoxIndex {H : ℕ} (η : TailDatum H) : Fin (H-P H) → ℕ :=
  fun i => ⌊tailVector η i⌋₊+1

def witnessGrid {H : ℕ} (W : Finset (TailDatum H)) : Finset (Fin (H-P H) → ℕ) :=
  W.image tailBoxIndex

lemma tailVector_mem_box {H : ℕ} {s : ℝ} {η : TailDatum H} (hη : IsWitness H s η) :
    tailVector η ∈ unitGridCell (tailBoxIndex η) := by
  intro i _
  simp only [tailBoxIndex, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  exact ⟨Nat.floor_le (tailVector_nonneg hη i), Nat.lt_floor_add_one _⟩

lemma tailPrimeVector_mem_grid {H : ℕ} {s : ℝ} (W : Finset (TailDatum H))
    (hW : ∀ η ∈ W, IsWitness H s η) {η : TailDatum H} (hη : η ∈ W) :
    tailPrimeVector η ∈ gridPrimeTuples (witnessGrid W) := by
  apply mem_gridPrimeTuples_iff.mpr
  refine ⟨tailPrimeVector_prime (hW η hη), ?_⟩
  rw [← tailVector_eq_primeCoord]
  exact Set.mem_iUnion.mpr ⟨tailBoxIndex η,
    Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨η, hη, rfl⟩, tailVector_mem_box (hW η hη)⟩⟩

lemma tailBoxIndex_lower {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : 0 ≤ s) (hη : IsWitness H s η) (i : Fin (H-P H)) :
    1 ≤ tailBoxIndex η i ∧ (9/10 : ℝ)*lam*(H-1-i.val : ℕ) ≤ tailBoxIndex η i := by
  refine ⟨by dsimp [tailBoxIndex]; omega, ?_⟩
  have hi : H-1-i.val ∈ Finset.Ico (P H) H := by
    have := i.isLt
    exact Finset.mem_Ico.mpr (by omega)
  have hb := (hη.2.2.1 _ hi).2.1
  have hα := alpha_ge_lam hs
  have hp : 1 ≤ (rho^(H-1-i.val))⁻¹ :=
    (one_le_inv₀ (pow_pos rho_pos _)).mpr (pow_le_one₀ rho_pos.le rho_lt_one.le)
  have hl : (9/10 : ℝ)*lam*(H-1-i.val : ℕ) ≤ tailVector η i := by
    apply le_trans _ hb
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα (by norm_num))
      (Nat.cast_nonneg _)).trans
      (le_mul_of_one_le_right (by have := alpha_pos s; positivity : 0 ≤ (9/10 : ℝ)*alpha s*(H-1-i.val : ℕ)) hp)
  exact hl.trans (tailVector_mem_box hη i (Set.mem_univ _)).2.le

lemma witnessGrid_exp_sum {H : ℕ} {s : ℝ} (hs : 0 ≤ s) (hPH : P H ≤ H)
    (W : Finset (TailDatum H)) (hW : ∀ η ∈ W, IsWitness H s η)
    {b : Fin (H-P H) → ℕ} (hb : b ∈ witnessGrid W) :
    (∑ i, Real.exp (-(b i : ℝ))) ≤
      (Real.exp (-(9/10 : ℝ)*lam))^(P H)/(1-Real.exp (-(9/10 : ℝ)*lam)) := by
  obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hb
  let q := Real.exp (-(9/10 : ℝ)*lam)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by dsimp [q]; rw [Real.exp_lt_one_iff]; nlinarith [lam_pos]
  have ht (i : Fin (H-P H)) : Real.exp (-(tailBoxIndex η i : ℝ)) ≤ q^(H-(i.val+1)) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hl := (tailBoxIndex_lower hs (hW η hη) i).2
    have he : H-1-i.val=H-(i.val+1) := by omega
    rw [he] at hl
    nlinarith
  apply (Finset.sum_le_sum (fun i _ => ht i)).trans
  rw [sum_reverse_geometric hPH q]
  have hg := summable_geometric_of_lt_one hq0 hq1
  calc
    _ ≤ ∑' n : ℕ, q^(P H+n) :=
      (hg.comp_injective (fun _ _ h => Nat.add_left_cancel h)).sum_le_tsum _
        (fun _ _ => pow_nonneg hq0 _)
    _ = _ := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      rfl

/-- The entire prime mass of any occupied tail box is bounded by an absolute
constant, independent of the number of tail coordinates and witnesses. -/
theorem witnessGrid_prime_mass_bound (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : ℕ} {s : ℝ}, 0 ≤ s → P H ≤ H →
      ∀ W : Finset (TailDatum H), (∀ η ∈ W, IsWitness H s η) →
      ∀ b ∈ witnessGrid W, (∏ i, unitPrimeWeight (b i)) ≤ C := by
  obtain ⟨C, hC, hc⟩ := prime_unit_box_error hford
  let q := Real.exp (-(9/10 : ℝ)*lam)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by dsimp [q]; rw [Real.exp_lt_one_iff]; nlinarith [lam_pos]
  refine ⟨Real.exp (C/(1-q)), Real.exp_pos _, ?_⟩
  intro H s hs hPH W hW b hb
  have hb1 : ∀ i, 1 ≤ b i := by
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hb
    exact fun i => (tailBoxIndex_lower hs (hW η hη) i).1
  have he := hc Finset.univ b (fun i _ => hb1 i)
  have hsum := witnessGrid_exp_sum hs hPH W hW hb
  have hsum' : (∑ i, Real.exp (-(b i : ℝ))) ≤ 1/(1-q) := by
    apply hsum.trans
    exact div_le_div_of_nonneg_right (pow_le_one₀ hq0 hq1.le) (sub_pos.mpr hq1).le
  have hh := (le_abs_self _).trans he
  have he' : (∏ i, unitPrimeWeight (b i)) ≤ Real.exp (C*∑ i, Real.exp (-(b i : ℝ))) := by
    linarith
  apply he'.trans
  apply Real.exp_le_exp.mpr
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hsum' hC.le

end TotientAsymptotic

end

end OAI
