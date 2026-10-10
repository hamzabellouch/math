import OAI.NumberTheory.TotientAsymptotic.NormalBandValueCount

namespace OAI

/-! Telescoping the upper-count exponent into Ford's renewal coefficients. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def countBandWeight (j : ℕ) : ℝ := (j:ℝ)*(1-Real.log j)

lemma countBandWeight_difference (j : ℕ) :
    countBandWeight (j+1)-countBandWeight j = -a j := by
  simp only [countBandWeight,a,Nat.cast_add,Nat.cast_one]
  ring

lemma count_band_telescope (v : ℕ → ℝ) (k : ℕ) :
    v k-v 0+(∑ j ∈ Finset.range k,countBandWeight (j+2)*(v j-v (j+1))) =
      -(∑ j ∈ Finset.range k,a (j+1)*v j)+(1-countBandWeight (k+1))*v k := by
  induction k with
  | zero => simp [countBandWeight]
  | succ k ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    have hd := congrArg (fun c : ℝ => c*v k) (countBandWeight_difference (k+1))
    simp only [Nat.add_assoc] at hd
    nlinarith only [ih,hd]

def normalBandError (S : ℕ) (D : ℝ) (k : ℕ) (Y : ℕ → ℕ) : ℝ :=
  D*(∑ j ∈ Finset.range k,((j+2:ℕ):ℝ))+
    ∑ j ∈ Finset.range k,((j+2:ℕ):ℝ)*Real.log (j+2)*Real.sqrt (B S*B (Y j))

lemma normal_band_exponent_identity (S : ℕ) (D : ℝ) (k : ℕ) (Y : ℕ → ℕ)
    (hYS : Y k=S) :
    B S-B (Y 0)+normalBandExponent S D k Y =
      -(∑ j ∈ Finset.range k,a (j+1)*B (Y j))+
        (1-countBandWeight (k+1))*B S+normalBandError S D k Y := by
  have hexp : normalBandExponent S D k Y =
      (∑ j ∈ Finset.range k,countBandWeight (j+2)*(B (Y j)-B (Y (j+1))))+
      normalBandError S D k Y := by
    unfold normalBandExponent normalBandError
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      ((j+2:ℕ):ℝ)*(B (Y j)-B (Y (j+1))+D)-
        ((j+2:ℕ):ℝ)*(B (Y j)-B (Y (j+1))-Real.sqrt (B S*B (Y j)))*Real.log (j+2)),
      Finset.mul_sum,← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [countBandWeight,Nat.cast_add,Nat.cast_ofNat]
    ring
  have ht := count_band_telescope (fun j => B (Y j)) k
  rw [hYS] at ht
  rw [hexp]
  linarith only [ht]

lemma normal_band_count_scale {S z : ℕ} (hS : 2 ≤ S) (hz : 2 ≤ z)
    (D : ℝ) (k : ℕ) (Y : ℕ → ℕ) (hY0 : Y 0=z) (hYS : Y k=S) :
    Real.log S/Real.log z*Real.exp (normalBandExponent S D k Y) =
      Real.exp (-(∑ j ∈ Finset.range k,a (j+1)*B (Y j))+
        (1-countBandWeight (k+1))*B S+normalBandError S D k Y) := by
  have hlS : 0 < Real.log S := Real.log_pos (by exact_mod_cast (show 1 < S by omega))
  have hlz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  rw [← normal_band_exponent_identity S D k Y hYS,hY0,Real.exp_add,
    Real.exp_sub]
  simp only [B,Real.exp_log hlS,Real.exp_log hlz]

end TotientAsymptotic

end

end OAI
