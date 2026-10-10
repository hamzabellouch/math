import OAI.NumberTheory.JointDickman.Amplification.AveragedConditionedRoots

namespace OAI

/-! # The conditioned root-model error survives the polynomial weight bound -/

namespace JointDickman
open Filter
open scoped Topology

noncomputable def conditionedRootError (B : ℕ) : ℝ :=
  214*(B : ℝ)^19/(auxiliaryCutoff B : ℝ)+2*(B : ℝ)^8/Real.exp B

theorem conditionedRootError_majorant {B T M : ℕ} (hB : 1 ≤ B) (hT : 0 < T) (hM : M ≤ B^2) :
    212*(B : ℝ)^19/(auxiliaryCutoff B : ℝ)+
      2*(B : ℝ)^6*(M : ℝ)/(auxiliaryCutoff B : ℝ)+
      2*((M : ℝ)^3*(B : ℝ)^2/((T : ℝ)*Real.exp B)) ≤ conditionedRootError B := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hMr : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hp : (0 : ℝ) ≤ auxiliaryCutoff B := Nat.cast_nonneg _
  have hmid : 2*(B : ℝ)^6*(M : ℝ)/(auxiliaryCutoff B : ℝ) ≤
      2*(B : ℝ)^19/(auxiliaryCutoff B : ℝ) := by
    calc
      _ ≤ 2*(B : ℝ)^6*(B : ℝ)^2/(auxiliaryCutoff B : ℝ) := by gcongr
      _ = 2*(B : ℝ)^8/(auxiliaryCutoff B : ℝ) := by ring
      _ ≤ _ := by gcongr; norm_num
  have hlast : 2*((M : ℝ)^3*(B : ℝ)^2/((T : ℝ)*Real.exp B)) ≤ 2*(B : ℝ)^8/Real.exp B := by
    calc
      _ ≤ 2*(((B : ℝ)^2)^3*(B : ℝ)^2/((T : ℝ)*Real.exp B)) := by gcongr
      _ = 2*((B : ℝ)^8/((T : ℝ)*Real.exp B)) := by ring
      _ ≤ 2*((B : ℝ)^8/(1*Real.exp B)) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (212*(B : ℝ)^19/(auxiliaryCutoff B : ℝ)+2*(B : ℝ)^19/(auxiliaryCutoff B : ℝ))+
        2*(B : ℝ)^8/Real.exp B := add_le_add (add_le_add le_rfl hmid) hlast
    _ = _ := by unfold conditionedRootError; ring

theorem conditionedRootError_weighted_tendsto :
    Tendsto (fun B : ℕ => (B : ℝ)^10*conditionedRootError B) atTop (𝓝 0) := by
  have hp := (polynomial_div_primeCutoff_tendsto_zero (k := 29) (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  have he := ((isLittleO_pow_exp_pos_mul_atTop 18 (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  have he' : Tendsto (fun B : ℕ => (B : ℝ)^18/Real.exp B) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_mul] using he
  have hp' : Tendsto (fun B : ℕ => (B : ℝ)^29/(auxiliaryCutoff B : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,auxiliaryCutoff,Nat.cast_pow] using hp
  have hh := (hp'.const_mul 214).add (he'.const_mul 2)
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [] with B
  unfold conditionedRootError
  ring

end JointDickman

end OAI
