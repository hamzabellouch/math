import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedEstimate
import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorPowers
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI

/-! Explicit absorption of the retained norm-dyad count and arbitrarily
small arithmetic losses in a fixed polynomial scale range. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_dyad_count_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℝ, 1 ≤ J →
      ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ) ≤ C*(1+Real.log J) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C := 1+Real.log 3/Real.log 2+1/Real.log 2
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro J hJ
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hfloor : (1:ℕ) ≤ ⌊3*J⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    norm_num
    linarith
  have hfloorpos : (0:ℝ) < (⌊3*J⌋₊:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hfloor)
  have hlog := Real.log_le_log hfloorpos (Nat.floor_le (by positivity : 0 ≤ 3*J))
  have hn := Real.natLog_le_logb ⌊3*J⌋₊ 2
  simp only [Real.logb,Nat.cast_ofNat] at hn
  have hjlog := Real.log_nonneg hJ
  have hh : ((Nat.log 2 ⌊3*J⌋₊:ℕ):ℝ) ≤
      (Real.log 3+Real.log J)/Real.log 2 := by
    apply hn.trans
    apply (div_le_div_iff_of_pos_right h2).mpr
    simpa only [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hJp.ne'] using hlog
  rw [Nat.cast_add,Nat.cast_one]
  have hhp : ((Nat.log 2 ⌊3*J⌋₊:ℕ):ℝ)+1 ≤
      (Real.log 3+Real.log J)/Real.log 2+1 := by linarith only [hh]
  apply hhp.trans
  dsimp [C]
  have hx := mul_nonneg (show 0 ≤ 1+Real.log 3/Real.log 2 by positivity) hjlog
  simp only [div_eq_mul_inv] at *
  nlinarith

lemma metaplectic_dyad_count_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℝ, 1 ≤ J →
      ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ) ≤ C*J^ε := by
  obtain ⟨D,hD,hd⟩ := metaplectic_dyad_count_log_bound
  obtain ⟨A,hA,ha⟩ := one_add_log_small_power hε
  refine ⟨D*A,mul_pos hD hA,?_⟩
  intro J hJ
  calc
    _ ≤ D*(1+Real.log J) := hd J hJ
    _ ≤ D*(A*J^ε) := mul_le_mul_of_nonneg_left (ha J hJ) hD.le
    _ = _ := by ring

/-- The exponent used in the coefficient estimate can be chosen before
all conductor and length parameters. -/
theorem metaplectic_retained_loss_small_power {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ Y R J : ℝ, 1 ≤ Y → 0 < R → 1 ≤ J →
      R ≤ Y^B → J ≤ Y^B →
      ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*(6*J)^(3*ε/2)*R^(2*ε) ≤ C*Y^η := by
  let ε := η/(5*(B+1))
  have hε : 0 < ε := div_pos hη (by positivity)
  obtain ⟨A,hA,ha⟩ := metaplectic_dyad_count_small_power hε
  refine ⟨ε,A*6^(3*ε/2),hε,mul_pos hA (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  intro Y R J hY hR hJ hRY hJY
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have he : B*(5*ε/2)+B*(2*ε) ≤ η := by
    have hh := (div_mul_cancel₀ η (show (5*(B+1):ℝ) ≠ 0 by positivity))
    change ε*(5*(B+1)) = η at hh
    nlinarith
  have hj : J^(5*ε/2) ≤ Y^(B*(5*ε/2)) := by
    apply (Real.rpow_le_rpow hJp.le hJY (by positivity)).trans_eq
    exact (Real.rpow_mul hYp.le _ _).symm
  have hr : R^(2*ε) ≤ Y^(B*(2*ε)) := by
    apply (Real.rpow_le_rpow hR.le hRY (by positivity)).trans_eq
    exact (Real.rpow_mul hYp.le _ _).symm
  calc
    _ ≤ (A*J^ε)*(6*J)^(3*ε/2)*R^(2*ε) := by gcongr; exact ha J hJ
    _ = (A*6^(3*ε/2))*(J^(5*ε/2)*R^(2*ε)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 6) hJp.le]
      have hx : J^ε*J^(3*ε/2) = J^(5*ε/2) := by
        rw [←Real.rpow_add hJp]
        congr 1
        ring
      rw [show A*J^ε*(6^(3*ε/2)*J^(3*ε/2))*R^(2*ε) =
        (A*6^(3*ε/2))*(J^ε*J^(3*ε/2)*R^(2*ε)) by ring,hx]
    _ ≤ (A*6^(3*ε/2))*(Y^(B*(5*ε/2))*Y^(B*(2*ε))) := by gcongr
    _ = (A*6^(3*ε/2))*Y^(B*(5*ε/2)+B*(2*ε)) := by rw [Real.rpow_add hYp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY he) (by positivity)

end CubicFirstMoment

end

end OAI
