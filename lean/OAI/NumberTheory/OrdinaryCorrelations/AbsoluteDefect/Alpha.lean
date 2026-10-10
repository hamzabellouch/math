import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.E

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryChainScales
noncomputable def alpha (H j : ℕ) : ℝ := ((2:ℝ)^H)⁻¹*(1-((2:ℝ)^(j+1))⁻¹)

lemma alpha_nonneg (H j : ℕ) : 0≤alpha H j := by
  unfold alpha
  have hh : (1:ℝ)≤2^(j+1) := one_le_pow₀ (by norm_num)
  have hi : ((2:ℝ)^(j+1))⁻¹≤1 := inv_le_one_of_one_le₀ hh
  positivity

lemma alpha_le (H j : ℕ) : alpha H j≤((2:ℝ)^H)⁻¹ := by
  unfold alpha
  have hh : 0≤((2:ℝ)^(j+1))⁻¹ := by positivity
  have hp : 0≤((2:ℝ)^H)⁻¹ := by positivity
  nlinarith

lemma alpha_succ (H j : ℕ) :
    alpha H (j+1)-alpha H j=((2:ℝ)^(H+j+2))⁻¹ := by
  unfold alpha
  rw [show H+j+2=H+(j+1)+1 by omega,show j+1+1=(j+1)+1 by rfl]
  simp only [pow_add,pow_one,mul_inv_rev]
  ring

lemma alpha_gain {B H s j M : ℕ} (hB : H+10≤B)
    (hM : E B s (j+1)≤M) :
    512*(mesh B H s (j+1):ℝ)≤((2:ℝ)^(H+j+2))⁻¹*(M:ℝ) := by
  have hE := next_gain B H s j hB
  have heg : (E B s (j+1):ℝ)=512*(mesh B H s (j+1):ℝ)*(2:ℝ)^(H+j+2) := by exact_mod_cast hE
  have hm : (E B s (j+1):ℝ)≤(M:ℝ) := by exact_mod_cast hM
  calc
    _ = ((2:ℝ)^(H+j+2))⁻¹*(E B s (j+1):ℝ) := by
      rw [heg,mul_left_comm,inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ)≠0)),mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

lemma alpha_remainder {B H s j L : ℕ} (hB : H+10≤B)
    (hL : E B s j≤L) (hL' : L≤F B s j) :
    alpha H j*((L:ℝ)+3)≤4*(mesh B H s (j+1):ℝ) := by
  have hLp : 1≤L := (E_pos B s j).trans_le hL
  have hrem : (L:ℝ)+3≤4*(F B s j:ℝ) := by
    have hln : (1:ℝ)≤L := by exact_mod_cast hLp
    have hlf : (L:ℝ)≤F B s j := by exact_mod_cast hL'
    linarith only [hln,hlf]
  have hf := previous_scale_absorption B H s j hB
  have hfr : (F B s j:ℝ)≤(mesh B H s (j+1):ℝ)*(2:ℝ)^H := by exact_mod_cast hf
  calc
    _ ≤ ((2:ℝ)^H)⁻¹*(4*(F B s j:ℝ)) := mul_le_mul (alpha_le H j) hrem
      (by positivity : (0:ℝ)≤(L:ℝ)+3) (by positivity : (0:ℝ)≤((2:ℝ)^H)⁻¹)
    _ ≤ ((2:ℝ)^H)⁻¹*(4*((mesh B H s (j+1):ℝ)*(2:ℝ)^H)) := by gcongr
    _ = _ := by
      rw [show (4:ℝ)*((mesh B H s (j+1):ℝ)*(2:ℝ)^H)=
        (4*(mesh B H s (j+1):ℝ))*(2:ℝ)^H by ring,
        mul_left_comm,inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ)≠0)),mul_one]

lemma alpha_transition {B H s j L M : ℕ} (hB : H+10≤B)
    (hL : E B s j≤L) (hL' : L≤F B s j) (hM : E B s (j+1)≤M) :
    2*alpha H j*(amplifier L M:ℝ)*(L:ℝ)-2*alpha H (j+1)*(M:ℝ)
      ≤ -1000*(mesh B H s (j+1):ℝ) := by
  have hn : (0:ℝ)≤alpha H j := alpha_nonneg H j
  have hk : (amplifier L M:ℝ)*(L:ℝ)≤(M:ℝ)+3+(L:ℝ) := by exact_mod_cast amplifier_upper L M
  have hmul := mul_le_mul_of_nonneg_left hk (show 0≤2*alpha H j by positivity)
  have had := congrArg (fun x : ℝ => x*(M:ℝ)) (alpha_succ H j)
  have hg := alpha_gain hB hM
  have hrem := alpha_remainder hB hL hL'
  nlinarith only [hmul,hg,hrem,had,Nat.cast_nonneg (α:=ℝ) (mesh B H s (j+1))]

end OrdinaryChainScales

end

end OAI
