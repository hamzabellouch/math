import OAI.MeasureTheory.Falconer.Estimates.RegularClasses

namespace OAI

/-! # The actual excess profile used by the all-dimensional branch ledger -/

namespace Falconer
open Set
variable {d : ℕ}

noncomputable def profileExcess (m : ℝ → ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  m ((j:ℝ)/N)-((d:ℝ)/2)*(j:ℝ)/N

theorem profileExcess_zero (Q : DyadicCube d) (ρ : MeasureTheory.Measure (Space d))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) :
    profileExcess (d := d) m N 0 = 0 := by
  simp only [profileExcess,Nat.cast_zero,zero_div,mul_zero,sub_zero,hreg.zero]

theorem profileExcess_envelope (Q : DyadicCube d) (ρ : MeasureTheory.Measure (Space d))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    {j : ℕ} (hj : j ≤ N) :
    (s-(d:ℝ)/2)*(j:ℝ)/N-((d:ℝ)+4)*lam ≤ profileExcess (d := d) m N j := by
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hu : (j:ℝ)/N ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity,(div_le_one hNR).mpr (Nat.cast_le.mpr hj)⟩
  have he := hreg.envelope _ hu
  calc
    _ = (s*((j:ℝ)/N)-((d:ℝ)+4)*lam)-((d:ℝ)/2)*(j:ℝ)/N := by ring
    _ ≤ _ := sub_le_sub_right he _

theorem profileExcess_lipschitz (Q : DyadicCube d) (ρ : MeasureTheory.Measure (Space d))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    (i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    |profileExcess (d := d) m N i-profileExcess (d := d) m N j| ≤
      (d:ℝ)*|(i:ℝ)-j|/N := by
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hunit (k : ℕ) (hk : k ≤ N) : (k:ℝ)/N ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity,(div_le_one hNR).mpr (Nat.cast_le.mpr hk)⟩
  have hsorted (i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) (hij : i ≤ j) :
      |profileExcess (d := d) m N i-profileExcess (d := d) m N j| ≤
        (d:ℝ)*((j:ℝ)-i)/N := by
    have huij : (i:ℝ)/N ≤ (j:ℝ)/N :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) hNR.le
    have hmij := hreg.monotone (hunit i hi) (hunit j hj) huij
    have hdist := hreg.lipschitz.dist_le_mul ((j:ℝ)/N) (hunit j hj) ((i:ℝ)/N) (hunit i hi)
    simp only [Real.dist_eq,NNReal.coe_natCast,abs_of_nonneg (sub_nonneg.mpr hmij),
      abs_of_nonneg (sub_nonneg.mpr huij)] at hdist
    have hscale : 0 ≤ (d:ℝ)*((j:ℝ)/N-(i:ℝ)/N) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr huij)
    have he : (d:ℝ)*((j:ℝ)-i)/N = (d:ℝ)*((j:ℝ)/N-(i:ℝ)/N) := by ring
    rw [he]
    simp only [profileExcess,mul_div_assoc]
    apply abs_le.mpr
    constructor <;> nlinarith
  rcases le_total i j with hij | hji
  · rw [abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr hij))]
    convert hsorted i j hi hj hij using 1; ring
  · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hji))]
    exact hsorted j i hj hi hji

end Falconer

end OAI
