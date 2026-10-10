import Mathlib
import OAI.Geometry.CAT0Fillings.Constants
import OAI.Geometry.CAT0Fillings.Scaling.HighCoefficient
import OAI.Geometry.CAT0Fillings.Density.RadialBound
import OAI.Geometry.CAT0Fillings.Variational.Extremizer

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma extremal_coefficient_two (hX : IsCAT0 X)
    {T : Functional X 2} (hT : IsIntegral 2 T) (hz : boundarySucc T = 0)
    {c : ℝ} (hc : 0 < c) (hm : 0 < mass T)
    (hext : ∀ B : Functional X 2, IsIntegral 2 B → boundarySucc B = 0 →
      c*((mass T)^((3:ℝ)/2)-(mass B)^((3:ℝ)/2)) ≤ fillingVolume (T-B)) :
    c ≤ fillingCoefficient 2 := by
  obtain ⟨q⟩ := exists_chartGeometry hX hT.1 hT.2.1
  let ell := c*((3:ℝ)/2)*(mass T)^((3:ℝ)/2-1)
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hbound : 16*Real.pi*ell^2 ≤ mass T := by
    apply q.radial_coefficient_bound_two hX hm hell
    intro o r hr
    exact radial_inequality_of_extremal hX hT hz q hc.le (by norm_num) hm hext o
      ((inverseSquareCutoff_lipschitz hr).comp (LipschitzWith.dist_right o))
      (fun _ => inverseSquareCutoff_nonneg _)
      (fun _ => inverseSquareCutoff_le_one hr _)
  have hsq : ell^2 = ((9:ℝ)/4)*c^2*mass T := by
    dsimp [ell]
    rw [show (3:ℝ)/2-1 = 1/2 by norm_num,←Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt hm.le]
  rw [hsq] at hbound
  have hcoef : 36*Real.pi*c^2 ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_right hm).mp
    nlinarith
  have hC := fillingCoefficient_two_pos
  have hCsq := fillingCoefficient_two_sq
  by_contra hn
  have hh : (fillingCoefficient 2)^2 < c^2 := sq_lt_sq₀ hC.le hc.le |>.mpr (lt_of_not_ge hn)
  have hp := mul_lt_mul_of_pos_left hh (show 0 < 36*Real.pi by positivity)
  linarith

lemma fillingVolume_le_two_supercritical (hX : IsCAT0 X)
    {T : Functional X 2} (hT : IsIntegral 2 T) (hz : boundarySucc T = 0)
    {c : ℝ} (hc : fillingCoefficient 2 < c) :
    fillingVolume T ≤ c*(mass T)^((3:ℝ)/2) := by
  by_contra hnot
  have hc0 : 0 < c := fillingCoefficient_two_pos.trans hc
  let δ := (c-fillingCoefficient 2)/(c+fillingCoefficient 2)
  have hsum : 0 < c+fillingCoefficient 2 := add_pos hc0 fillingCoefficient_two_pos
  have hδ : 0 < δ := div_pos (sub_pos.mpr hc) hsum
  obtain ⟨U,hU,hUz,hm,hdef,hext⟩ := exists_filling_extremizer hX hc0
    (by norm_num : (1:ℝ) < 3/2) hδ hT hz (show 0 < fillingDeficit c (3/2) T by
      dsimp [fillingDeficit]; linarith)
  have hden : 0 < 1+δ := by linarith
  have hcoeff : c/(1+δ) = (c+fillingCoefficient 2)/2 := by
    dsimp [δ]
    field_simp [hsum.ne',hc0.ne']
    ring
  have hb := extremal_coefficient_two hX hU hUz (div_pos hc0 hden) hm hext
  rw [hcoeff] at hb
  linarith

theorem fillingVolume_le_two (hX : IsCAT0 X)
    {T : Functional X 2} (hT : IsIntegral 2 T) (hz : boundarySucc T = 0) :
    fillingVolume T ≤ fillingCoefficient 2*(mass T)^fillingPower 2 := by
  rw [fillingPower_two]
  have hlim : Tendsto (fun j : ℕ => (fillingCoefficient 2+1/((j:ℝ)+1))*(mass T)^((3:ℝ)/2))
      atTop (𝓝 (fillingCoefficient 2*(mass T)^((3:ℝ)/2))) := by
    simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0)).const_add (fillingCoefficient 2)).mul_const
        ((mass T)^((3:ℝ)/2))
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun j => fillingVolume_le_two_supercritical hX hT hz
    (lt_add_of_pos_right _ (by positivity))

end CAT0Fillings
end

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
universe u
lemma fillingVolume_le_of_coefficient {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (hX : IsCAT0 X) {k : ℕ}
    (hcoef : ∀ U : Functional X (k+2), IsIntegral (k+2) U → IsCycle U →
      ∀ c : ℝ, 0 < c → 0 < mass U →
      (∀ B : Functional X (k+2), IsIntegral (k+2) B → IsCycle B →
        c*((mass U)^(fillingPower (k+2))-(mass B)^(fillingPower (k+2))) ≤ fillingVolume (U-B)) →
      c ≤ fillingCoefficient (k+2))
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : IsCycle T) :
    fillingVolume T ≤ fillingCoefficient (k+2)*(mass T)^(fillingPower (k+2)) := by
  have hsuper (c : ℝ) (hc : fillingCoefficient (k+2) < c) :
      fillingVolume T ≤ c*(mass T)^(fillingPower (k+2)) := by
    by_contra hnot
    have hc0 := (fillingCoefficient_pos (by omega : 0 < k+2)).trans hc
    let δ := (c-fillingCoefficient (k+2))/(c+fillingCoefficient (k+2))
    have hsum : 0 < c+fillingCoefficient (k+2) := add_pos hc0 (fillingCoefficient_pos (by omega))
    have hδ : 0 < δ := div_pos (sub_pos.mpr hc) hsum
    obtain ⟨U,hU,hUz,hm,hdef,hext⟩ := exists_filling_extremizer hX hc0
      (fillingPower_gt_one (by omega : 0 < k+2)) hδ hT hz
      (show 0 < fillingDeficit c (fillingPower (k+2)) T by dsimp [fillingDeficit]; linarith)
    have hden : 0 < 1+δ := by linarith
    have hcoeff : c/(1+δ) = (c+fillingCoefficient (k+2))/2 := by
      dsimp [δ]
      field_simp [hsum.ne',hc0.ne']
      ring
    have hb := hcoef U hU hUz (c/(1+δ)) (div_pos hc0 hden) hm hext
    rw [hcoeff] at hb
    linarith
  have hlim : Tendsto (fun j : ℕ => (fillingCoefficient (k+2)+1/((j:ℝ)+1))*(mass T)^(fillingPower (k+2)))
      atTop (𝓝 (fillingCoefficient (k+2)*(mass T)^(fillingPower (k+2)))) := by
    simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0)).const_add (fillingCoefficient (k+2))).mul_const
        ((mass T)^(fillingPower (k+2)))
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun j => hsuper _ (lt_add_of_pos_right _ (by positivity))

theorem compact_filling_bound : ∀ k : ℕ,
    ∀ (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X],
      IsCAT0 X → ∀ T : Functional X (k+2), IsIntegral (k+2) T → boundarySucc T = 0 →
        fillingVolume T ≤ fillingCoefficient (k+2)*(mass T)^(fillingPower (k+2)) := by
  intro k
  induction k with
  | zero =>
    intro X _ _ _ _ _ hX T hT hz
    exact fillingVolume_le_two hX hT hz
  | succ k ih =>
    intro X _ _ _ _ _ hX T hT hz
    apply fillingVolume_le_of_coefficient hX ?_ hT hz
    intro U hU hUz c hc hm hext
    exact extremal_coefficient_high (by omega) hX hU hUz hc hm ih hext
end CAT0Fillings
end

end OAI
