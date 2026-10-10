import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.CellFieldNormalizationBarrier
import OAI.Analysis.CoulombIonization.ThomasFermi.CellDensityBoundBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

 def cellCountLeadingConstant : ℝ := 1024*cellFieldNormConstant*localCountCoverConstant
 def cellCountErrorConstant (e d : ℝ) : ℝ :=
    2*cellDensityMassConstant^2+512+
    1536*(Real.pi*smoothTransitionBound)^2*localCountCoverConstant/e^2+
    512*neumannRemainderConstant/e^2*(localCountCoverConstant^(2/3:ℝ)+localCountCoverConstant)+
    512*((2*Real.pi+1)/2)*localCountCoverConstant/e+
    cellCountLeadingConstant*Real.sqrt e/e^2+
    393216*d*cellFieldNormConstant/e^2*(1+1/e^2)

lemma cellCountLeadingConstant_pos : 0 < cellCountLeadingConstant := by
  have := cellFieldNormConstant_one_le
  have := localCountCoverConstant_one_le
  unfold cellCountLeadingConstant
  positivity
lemma cellCountErrorConstant_nonneg {e d : ℝ} (he : 0 < e) (hd : 0 ≤ d) :
    0 ≤ cellCountErrorConstant e d := by
  have := cellCountLeadingConstant_pos
  have := localCountCoverConstant_one_le
  have := cellFieldNormConstant_one_le
  have := neumannRemainderConstant_pos
  unfold cellCountErrorConstant
  positivity

lemma cell_budget_algebra {a m e D B O M d P : ℝ}
    (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (he : 0 < e) (he1 : e ≤ 1)
    (hD : D*a ≤ m^2) (hB : 0 ≤ B) (hd : 0 ≤ d) (hP : 1 ≤ P)
    (hBC : B ≤ localCountCoverConstant*P*m^2)
    (hO : O ≤ (cellFieldNormConstant*(m/a)*(Real.sqrt P+1/e^2))^2)
    (hM : M ≤ 1536*cellFieldNormConstant*m*(Real.sqrt P+1/e^2)) :
    2*cellDensityMassConstant^2*m^2+512*a*(D+
      (3/2:ℝ)*(Real.pi*smoothTransitionBound/(e*a))^2*Real.sqrt (4*e*B)+
      (e*a)⁻¹^2*neumannRemainderConstant*(B^(2/3:ℝ)+Real.sqrt B)+
      (((2*Real.pi+1)/2)/(e*a))*Real.sqrt B+
      Real.sqrt O*Real.sqrt (4*e*B)+((d/2)*(e*a)⁻¹^2)*M) ≤
    cellCountLeadingConstant*Real.sqrt e*P*m^2+
      cellCountErrorConstant e d*(P^(2/3:ℝ)+Real.sqrt P+1)*m^2 := by
  let C := localCountCoverConstant
  let F := cellFieldNormConstant
  let S := Real.pi*smoothTransitionBound
  let K := neumannRemainderConstant
  let L := (2*Real.pi+1)/2
  let u := Real.sqrt P
  let v := P^(2/3:ℝ)
  let W := v+u+1
  have hC1 : 1 ≤ C := localCountCoverConstant_one_le
  have hF1 : 1 ≤ F := cellFieldNormConstant_one_le
  have hC : 0 ≤ C := le_trans zero_le_one hC1
  have hF : 0 ≤ F := le_trans zero_le_one hF1
  have hK : 0 ≤ K := neumannRemainderConstant_pos.le
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hu : 0 ≤ u := Real.sqrt_nonneg P
  have hv : 0 ≤ v := Real.rpow_nonneg hP0 _
  have hW : 1 ≤ W := by dsimp [W]; linarith
  have huW : u ≤ W := by dsimp [W]; linarith
  have hvW : v ≤ W := by dsimp [W]; linarith
  have hu2 : u^2 = P := Real.sq_sqrt hP0
  have hse : Real.sqrt e ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num,by simpa using he1⟩
  have hrB : Real.sqrt B ≤ C*u*m := sqrt_count_scale hB hC1 hP0 hm0 hBC
  have hr4 : Real.sqrt (4*e*B) ≤ 2*Real.sqrt e*C*u*m := by
    calc _ = 2*Real.sqrt e*Real.sqrt B := by rw [Real.sqrt_mul (by positivity : 0 ≤ 4*e),Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
         _ ≤ 2*Real.sqrt e*(C*u*m) := mul_le_mul_of_nonneg_left hrB (by positivity)
         _ = _ := by ring
  have hr4' : Real.sqrt (4*e*B) ≤ 2*C*u*m := by
    calc _ ≤ 2*Real.sqrt e*C*u*m := hr4
         _ ≤ 2*1*C*u*m := by gcongr
         _ = _ := by ring
  have hB23 : B^(2/3:ℝ) ≤ C^(2/3:ℝ)*v*a*m^2 := cell_count_rpow_scale ha hm h3 hB hC hP0 hBC
  have hrootO : Real.sqrt O ≤ F*(m/a)*(u+1/e^2) := Real.sqrt_le_iff.mpr ⟨by positivity,hO⟩
  have hma : m/a ≤ m^2 := by
    have hh := mul_le_mul_of_nonneg_left (cell_reciprocal_bounds ha hm h3).1 hm0
    calc _ = m*(1/a) := by ring
         _ ≤ m*m := hh
         _ = m^2 := by ring
  have hmm : m ≤ m^2 := by nlinarith
  have heD : 512*a*D ≤ 512*W*m^2 := by
    have hh := mul_le_mul_of_nonneg_left hD (by norm_num : (0:ℝ) ≤ 512)
    have hh' := mul_le_mul_of_nonneg_right hW (show 0 ≤ 512*m^2 by positivity)
    nlinarith
  have heI : 512*a*((3/2:ℝ)*(S/(e*a))^2*Real.sqrt (4*e*B)) ≤
      (1536*S^2*C/e^2)*W*m^2 := by
    calc _ ≤ 512*a*((3/2:ℝ)*(S/(e*a))^2*(2*C*u*m)) := by gcongr
         _ = (1536*S^2*C/e^2)*u*(m/a) := by field_simp; ring
         _ ≤ (1536*S^2*C/e^2)*W*m^2 := by gcongr
  have heN : 512*a*((e*a)⁻¹^2*K*(B^(2/3:ℝ)+Real.sqrt B)) ≤
      (512*K/e^2*(C^(2/3:ℝ)+C))*W*m^2 := by
    calc _ ≤ 512*a*((e*a)⁻¹^2*K*(C^(2/3:ℝ)*v*a*m^2+C*u*m)) := by gcongr
         _ = 512*K/e^2*(C^(2/3:ℝ)*v*m^2+C*u*(m/a)) := by field_simp
         _ ≤ 512*K/e^2*(C^(2/3:ℝ)*W*m^2+C*W*m^2) := by gcongr
         _ = (512*K/e^2*(C^(2/3:ℝ)+C))*W*m^2 := by ring
  have heL : 512*a*((L/(e*a))*Real.sqrt B) ≤ (512*L*C/e)*W*m^2 := by
    calc _ ≤ 512*a*((L/(e*a))*(C*u*m)) := by gcongr
         _ = (512*L*C/e)*u*m := by field_simp
         _ ≤ (512*L*C/e)*W*m^2 := by gcongr
  have heO : 512*a*(Real.sqrt O*Real.sqrt (4*e*B)) ≤
      cellCountLeadingConstant*Real.sqrt e*P*m^2+
      (cellCountLeadingConstant*Real.sqrt e/e^2)*W*m^2 := by
    calc _ ≤ 512*a*((F*(m/a)*(u+1/e^2))*(2*Real.sqrt e*C*u*m)) := by gcongr
         _ = cellCountLeadingConstant*Real.sqrt e*P*m^2+
             (cellCountLeadingConstant*Real.sqrt e/e^2)*u*m^2 := by
               dsimp [cellCountLeadingConstant]
               change _ = 1024*F*C*Real.sqrt e*P*m^2+(1024*F*C*Real.sqrt e/e^2)*u*m^2
               rw [←hu2]
               field_simp
               ring
         _ ≤ cellCountLeadingConstant*Real.sqrt e*P*m^2+
             (cellCountLeadingConstant*Real.sqrt e/e^2)*W*m^2 := by
               have := cellCountLeadingConstant_pos
               gcongr
  have hpen : 1/e^2 ≤ (1/e^2)*W := by
    simpa using mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 1/e^2)
  have heM : 512*a*(((d/2)*(e*a)⁻¹^2)*M) ≤
      (393216*d*F/e^2*(1+1/e^2))*W*m^2 := by
    calc _ ≤ 512*a*(((d/2)*(e*a)⁻¹^2)*(1536*F*m*(u+1/e^2))) := by gcongr
         _ = 393216*d*F/e^2*(m/a)*(u+1/e^2) := by field_simp; ring
         _ ≤ 393216*d*F/e^2*m^2*(W+(1/e^2)*W) := by gcongr
         _ = (393216*d*F/e^2*(1+1/e^2))*W*m^2 := by ring
  have hecap : 2*cellDensityMassConstant^2*m^2 ≤ (2*cellDensityMassConstant^2)*W*m^2 := by
    have hh := mul_le_mul_of_nonneg_right hW (by positivity : 0 ≤ 2*cellDensityMassConstant^2*m^2)
    linarith only [hh]
  change _ ≤ cellCountLeadingConstant*Real.sqrt e*P*m^2+cellCountErrorConstant e d*W*m^2
  dsimp [cellCountErrorConstant]
  change 2*cellDensityMassConstant^2*m^2+512*a*(D+(3/2:ℝ)*(S/(e*a))^2*Real.sqrt (4*e*B)+
    (e*a)⁻¹^2*K*(B^(2/3:ℝ)+Real.sqrt B)+(L/(e*a))*Real.sqrt B+Real.sqrt O*Real.sqrt (4*e*B)+((d/2)*(e*a)⁻¹^2)*M) ≤ _
  linarith only [heD,heI,heN,heL,heO,heM,hecap]

end CoulombAtom

end

end OAI
