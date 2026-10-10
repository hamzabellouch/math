import OAI.NumberTheory.TotientAsymptotic.NormalityGrid

namespace OAI

/-! Reduction of a real interval deviation to a double-logarithmic grid interval. -/
noncomputable section
namespace TotientAsymptotic

lemma normality_grid_reduction (n : ℕ) {S U T x : ℝ}
    (hS : 1 < S) (hBS : 4 ≤ B S) (hSU : S ≤ U) (hUT : U < T) (hTx : T ≤ x)
    (hbad : Real.sqrt (B S*B T)-1 ≤ |(omegaIn n U T:ℝ)-(B T-B U)|) :
    ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ ⌊B x⌋₊+1 ∧
      B S-2 ≤ (j:ℝ)-1 ∧
      Real.sqrt ((B S-2)*((j:ℝ)-1))-4  ≤ 
        |(omegaIn n (normalityGridPoint i) (normalityGridPoint j):ℝ)-((j:ℝ)-i)| := by
  have hU : 1 < U := hS.trans_le hSU
  have hT : 1 < T := hU.trans hUT
  have hx : 1 < x := hT.trans_le hTx
  have hBU : B S ≤ B U := Real.log_le_log (Real.log_pos hS)
    (Real.log_le_log (by linarith) hSU)
  have hBT : B U ≤ B T := Real.log_le_log (Real.log_pos hU)
    (Real.log_le_log (by linarith) hUT.le)
  have hBT4 : 4 ≤ B T := hBS.trans (hBU.trans hBT)
  have hBx : B T ≤ B x := Real.log_le_log (Real.log_pos hT)
    (Real.log_le_log (by linarith) hTx)
  let a := ⌊B U⌋₊
  let b := ⌊B T⌋₊
  have ha0 : 0 ≤ B U := by linarith
  have hb0 : 0 ≤ B T := by linarith
  have haL : (a:ℝ) ≤ B U := Nat.floor_le ha0
  have haR : B U < (a:ℝ)+1 := Nat.lt_floor_add_one _
  have hbL : (b:ℝ) ≤ B T := Nat.floor_le hb0
  have hbR : B T < (b:ℝ)+1 := Nat.lt_floor_add_one _
  have ha4 : 4 ≤ a := (Nat.le_floor_iff ha0).mpr (by norm_num; linarith)
  have hab : a ≤ b := Nat.floor_mono hBT
  have hbx : b ≤ ⌊B x⌋₊ := Nat.floor_mono hBx
  have hu := normalityGridPoint_bracket hU ha0
  have ht := normalityGridPoint_bracket hT hb0
  have hroot : 4 ≤ Real.sqrt (B S*B T) := by
    have hnon := Real.sqrt_nonneg (B S*B T)
    have he := Real.sq_sqrt (show 0 ≤ B S*B T by positivity)
    nlinarith
  have hroot_compare (j : ℕ) (hD0 : 0 ≤ (j:ℝ)-1) (hD : (j:ℝ)-1 ≤ B T) :
      Real.sqrt ((B S-2)*((j:ℝ)-1))  ≤  Real.sqrt (B S*B T) := by
    apply Real.sqrt_le_sqrt
    have hm := mul_le_mul_of_nonneg_left hD (show 0 ≤ B S-2 by linarith)
    nlinarith
  rcases le_abs.mp hbad with hhigh|hlow
  · refine ⟨a,b+1,by omega,by omega,by omega,?_,?_⟩
    · push_cast
      linarith
    · have hc := omegaIn_mono n hu.1 ht.2.le
      have hcR : (omegaIn n U T:ℝ) ≤ omegaIn n (normalityGridPoint a) (normalityGridPoint (b+1)) := by
        exact_mod_cast hc
      have hr := hroot_compare (b+1) (by push_cast; have hb : (0:ℝ) ≤ b := Nat.cast_nonneg _; linarith) (by push_cast; linarith)
      apply le_trans _ (le_abs_self _)
      push_cast at hr ⊢
      nlinarith
  · have hsep : a+1 < b := by
      by_contra hn
      have hn' : (b:ℝ) ≤ (a:ℝ)+1 := by exact_mod_cast (by omega : b ≤ a+1)
      have hΩ : (0:ℝ) ≤ omegaIn n U T := Nat.cast_nonneg _
      nlinarith
    refine ⟨a+1,b,by omega,hsep,by omega,?_,?_⟩
    · linarith
    · have hc := omegaIn_mono n (U₁:=normalityGridPoint (a+1)) (U₂:=U)
        (T₁:=normalityGridPoint b) (T₂:=T) hu.2.le ht.1
      have hcR : (omegaIn n (normalityGridPoint (a+1)) (normalityGridPoint b):ℝ) ≤ omegaIn n U T := by
        exact_mod_cast hc
      have hb1 : (1:ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
      have hr := hroot_compare b (by linarith) (by linarith)
      apply le_trans _ (neg_le_abs _)
      push_cast
      nlinarith

end TotientAsymptotic

end

end OAI
