import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRegularGrowth
import OAI.NumberTheory.CubicMoment.Estimates.MellinCutoffBound
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticWeightedContinuation

namespace OAI

/-! Vertical strip bounds for the actual regularized Mellin formula. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma metaplecticPoleCorrection_bound (x : ℝ) (hx : 0 < x) :
    ‖metaplecticPoleCorrection x‖ ≤ (4/3:ℝ)^(11/6:ℝ)*x^(-(1:ℝ)) := by
  by_cases hl : x ≤ 1
  · rw [metaplecticPoleCorrection_zero_low hl,norm_zero]
    positivity
  by_cases hh : 4/3 ≤ x
  · rw [metaplecticPoleCorrection_zero_high hh,norm_zero]
    positivity
  have h1 : x ∈ Ioi (1:ℝ) := lt_of_not_ge hl
  have hs0 := Real.smoothTransition.nonneg (3*(x-1))
  have hs1 := Real.smoothTransition.le_one (3*(x-1))
  have hs : ‖(normPartitionStep x:ℂ)-1‖ ≤ 1 := by
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (by simpa only [normPartitionStep] using sub_nonpos.mpr hs1)]
    dsimp [normPartitionStep]
    linarith
  have he : metaplecticPoleCorrection x =
      ((x^(5/6:ℝ):ℝ):ℂ)*((normPartitionStep x:ℂ)-1) := by
    rw [metaplecticPoleCorrection,indicator_of_mem h1]
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  calc
    _ ≤ x^(5/6:ℝ)*1 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = x^(11/6:ℝ)*x^(-(1:ℝ)) := by
      rw [←Real.rpow_add hx]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hx.le (le_of_not_ge hh) (by norm_num)) (by positivity)

theorem metaplecticWeightedRegular_height_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 2) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ ∈ Icc b 2, ∀ t v : ℝ,
      ‖metaplecticWeightedRegular r (metaplecticHeightTest t)
        ((σ:ℂ)+(v:ℂ)*Complex.I)‖ ≤ C*(1+|t|)^N := by
  obtain ⟨K,hK,hKbound⟩ := mellin_cutoff_bound hb hb2
    (show (0:ℝ) < 1/4 by norm_num) (show (0:ℝ) < 1/20000 by norm_num)
  obtain ⟨L,hL,hLbound⟩ := mellin_cutoff_bound hb hb2
    (show (0:ℝ) < 1/4 by norm_num) (show (0:ℝ) < 1 by norm_num)
  obtain ⟨C,N,hC,hR⟩ := metaplecticRegularHeight_bound hV hr hsr
  obtain ⟨M,hM,hMW⟩ := smooth_mellin_vertical_decay normPartitionWeight
    normPartitionWeight_compact normPartitionWeight_positive_support normPartitionWeight_smooth
    (5/6) 0
  let D : ℝ := ‖metaplecticCompletedResidue r‖*M*(L*(4/3:ℝ)^(11/6:ℝ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨K*C+D,N,by positivity,?_⟩
  intro σ hσ t v
  let s : ℂ := (σ:ℂ)+(v:ℂ)*Complex.I
  have hs : s.re ∈ Icc b 2 := by simpa [s] using hσ
  have hRbound : ‖mellin (metaplecticRegularScale r (metaplecticHeightTest t)) (-s)‖ ≤
      K*(C*(1+|t|)^N) :=
    hKbound _ _ (by positivity) (fun x hx hxd =>
      metaplecticRegularHeight_zero hx (by linarith) r t)
      (fun x hx => by simpa only [mul_right_comm] using hR x hx t) s hs
  have hPbound : ‖mellin metaplecticPoleCorrection (-s)‖ ≤ L*(4/3:ℝ)^(11/6:ℝ) :=
    hLbound _ _ (by positivity) (fun x _ hxd =>
      metaplecticPoleCorrection_zero_low (by linarith)) metaplecticPoleCorrection_bound s hs
  have hMbound : ‖mellin (metaplecticHeightTest t) (5/6)‖ ≤ M := by
    rw [metaplecticHeightTest_mellin]
    simpa only [pow_zero,one_mul,Complex.ofReal_div,Complex.ofReal_ofNat] using hMW t
  unfold metaplecticWeightedRegular
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have hsmall : ‖metaplecticCompletedResidue r‖*
      ‖mellin (metaplecticHeightTest t) (5/6)‖*‖mellin metaplecticPoleCorrection (-s)‖ ≤ D := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hMbound (_root_.norm_nonneg _))
      hPbound (_root_.norm_nonneg _) (by positivity)
  have hpow : 1 ≤ (1+|t|)^N := one_le_pow₀ (by linarith [abs_nonneg t])
  calc
    _ ≤ K*(C*(1+|t|)^N)+D := add_le_add hRbound hsmall
    _ ≤ K*(C*(1+|t|)^N)+D*(1+|t|)^N :=
      add_le_add le_rfl (le_mul_of_one_le_right hD hpow)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
