import OAI.Probability.InvariantIsing.Cavity.CavitySiteSymmetry
import OAI.Probability.InvariantIsing.Cavity.CavitySpinSplit

namespace OAI

/-! Removing finitely many cavity sites changes the ordinary spin
overlap by at most twice their fraction of the system. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavityTotalSpinOverlap_mul_size {N : ℕ} (x : Spin N × Spin N) :
    (N : ℝ) * cavityTotalSpinOverlap x = ∑ i, spinValue (x.1 i) * spinValue (x.2 i) := by
  by_cases hN : N = 0
  · subst N
    simp [cavityTotalSpinOverlap]
  · rw [cavityTotalSpinOverlap, ← mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN), one_mul]

lemma abs_cavityTotalSpinOverlap_le {N : ℕ} (x : Spin N × Spin N) :
    |cavityTotalSpinOverlap x| ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp [cavityTotalSpinOverlap]
  · have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    unfold cavityTotalSpinOverlap
    rw [abs_mul,abs_of_pos (inv_pos.mpr hNpos)]
    calc
      _ ≤ (N:ℝ)⁻¹ * ∑ i, |spinValue (x.1 i) * spinValue (x.2 i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.mpr hNpos).le
      _ = (N:ℝ)⁻¹ * N := by simp only [abs_mul,abs_spinValue,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      _ = 1 := inv_mul_cancel₀ hNpos.ne'

lemma cavity_spin_split_overlap {N n : ℕ} (σ τ : Spin (N+n)) :
    ((N+n:ℕ):ℝ) * cavityTotalSpinOverlap (σ,τ) =
      (N:ℝ) * cavityTotalSpinOverlap ((cavitySpinSplit N n σ).1,(cavitySpinSplit N n τ).1) +
      (n:ℝ) * cavityTotalSpinOverlap ((cavitySpinSplit N n σ).2,(cavitySpinSplit N n τ).2) := by
  simp only [cavityTotalSpinOverlap_mul_size,Fin.sum_univ_add,
    cavitySpinSplit_left,cavitySpinSplit_right]

lemma cavity_spin_split_overlap_error {N n : ℕ} (hN : 0 < N) (σ τ : Spin (N+n)) :
    |cavityTotalSpinOverlap (σ,τ) -
      cavityTotalSpinOverlap ((cavitySpinSplit N n σ).1,(cavitySpinSplit N n τ).1)| ≤
      2*(n:ℝ)/(N+n) := by
  let a := cavityTotalSpinOverlap ((cavitySpinSplit N n σ).1,(cavitySpinSplit N n τ).1)
  let b := cavityTotalSpinOverlap ((cavitySpinSplit N n σ).2,(cavitySpinSplit N n τ).2)
  let c := cavityTotalSpinOverlap (σ,τ)
  have hpos : (0:ℝ) < N+n := by exact_mod_cast Nat.add_pos_left hN n
  have hs : ((N:ℝ)+n)*c = N*a+n*b := by
    simpa only [Nat.cast_add] using cavity_spin_split_overlap σ τ
  have he : c-a = (n:ℝ)*(b-a)/(N+n) := by
    apply (eq_div_iff hpos.ne').mpr
    nlinarith [hs]
  change |c-a| ≤ _
  rw [he,abs_div,abs_of_pos hpos,abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
  apply div_le_div_of_nonneg_right _ hpos.le
  have ha : |a| ≤ 1 := abs_cavityTotalSpinOverlap_le _
  have hb : |b| ≤ 1 := abs_cavityTotalSpinOverlap_le _
  have hab : |b-a| ≤ 2 := (abs_sub b a).trans (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n)]

end InvariantIsing

end

end OAI
