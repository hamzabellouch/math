import Mathlib

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

def E (B s j : ℕ) : ℕ := 2^(B+j^2+(s+20)*j)
def F (B s j : ℕ) : ℕ := 2^(B+s+j^2+(s+21)*j)
def mesh (B H s j : ℕ) : ℕ := 2^(B-H-10+j^2+(s+19)*j)
def amplifier (L M : ℕ) : ℕ := (M+3)/L+1

lemma E_pos (B s j : ℕ) : 0 < E B s j := by unfold E; positivity
lemma F_pos (B s j : ℕ) : 0 < F B s j := by unfold F; positivity
lemma mesh_pos (B H s j : ℕ) : 0 < mesh B H s j := by unfold mesh; positivity
lemma E_le_F (B s j : ℕ) : E B s j ≤ F B s j := by
  apply Nat.pow_le_pow_right (by omega)
  nlinarith

lemma F_eq (B s j : ℕ) : F B s j=E B s j*2^(s+j) := by
  unfold F E
  rw [←pow_add]
  congr 1
  ring

lemma next_E (B s j : ℕ) : E B s (j+1)=F B s j*2^(j+21) := by
  unfold F E
  rw [←pow_add]
  congr 1
  ring

lemma next_F (B s j : ℕ) : F B s (j+1)=E B s j*2^(3*j+2*s+22) := by
  unfold F E
  rw [←pow_add]
  congr 1
  ring

lemma mesh_E (B H s j : ℕ) (hB : H+10 ≤ B) :
    E B s j=mesh B H s j*2^(H+j+10) := by
  unfold E mesh
  rw [←pow_add]
  congr 1
  have he : B-H-10+H+10=B := by omega
  nlinarith

lemma next_mesh_F (B H s j : ℕ) (hB : H+10 ≤ B) :
    mesh B H s (j+1)*2^H=F B s j*2^10 := by
  unfold F mesh
  rw [←pow_add,←pow_add]
  congr 1
  have he : B-H-10+H+10=B := by omega
  nlinarith

lemma mesh_mono (B H s : ℕ) : Monotone (mesh B H s) := by
  intro i j hij
  apply Nat.pow_le_pow_right (by omega)
  have hs := Nat.pow_le_pow_left hij 2
  nlinarith

lemma E_mono (B s : ℕ) : StrictMono (E B s) := by
  intro i j hij
  apply Nat.pow_lt_pow_right (by omega)
  have hs := Nat.pow_le_pow_left hij.le 2
  nlinarith

lemma F_mono (B s : ℕ) : StrictMono (F B s) := by
  intro i j hij
  apply Nat.pow_lt_pow_right (by omega)
  have hs := Nat.pow_le_pow_left hij.le 2
  nlinarith

lemma amplifier_lower {L M : ℕ} (hL : 0 < L) : M+3 < L*amplifier L M := by
  exact Nat.lt_mul_div_succ _ hL

lemma amplifier_upper (L M : ℕ) : amplifier L M*L ≤ M+3+L := by
  unfold amplifier
  rw [Nat.add_mul,one_mul]
  exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

lemma amplifier_bound {B s j L M : ℕ} (hL : E B s j ≤ L)
    (hM : M ≤ F B s (j+1)) : amplifier L M ≤ 2^(3*j+2*s+25) := by
  have hLp : 0 < L := (E_pos B s j).trans_le hL
  have hEp : 0 < E B s j := E_pos B s j
  have hpow : 1 ≤ (2:ℕ)^(3*j+2*s+22) := Nat.one_le_pow _ _ (by omega)
  have hm : M+3 ≤ L*2^(3*j+2*s+22)+3 := by
    have hh := hM.trans_eq (next_F B s j)
    nlinarith
  have hh : (M+3)/L ≤ 2^(3*j+2*s+22)+3 := by
    apply (Nat.div_le_iff_le_mul_add_pred hLp).mpr
    nlinarith
  unfold amplifier
  have he : 3*j+2*s+25=(3*j+2*s+22)+3 := by omega
  rw [he,pow_add]
  norm_num
  omega

lemma amplifier_square_absorption (B H s j K : ℕ)
    (hB : H+4*s+K+70 ≤ B) {L M : ℕ} (hL : E B s j ≤ L)
    (hM : M ≤ F B s (j+1)) :
    2^K*(amplifier L M+1)^2 ≤ mesh B H s (j+1) := by
  have hk := amplifier_bound hL hM
  have hp : 1 ≤ (2:ℕ)^(3*j+2*s+25) := Nat.one_le_pow _ _ (by omega)
  have hk' : amplifier L M+1 ≤ 2^(3*j+2*s+26) := by
    have he : 3*j+2*s+26=(3*j+2*s+25)+1 := by omega
    rw [he,pow_succ]
    omega
  calc
    _  ≤  2^K*(2^(3*j+2*s+26))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk' 2)
    _ = 2^(K+(3*j+2*s+26)*2) := by rw [←pow_mul,←pow_add]
    _  ≤  mesh B H s (j+1) := by
      unfold mesh
      apply Nat.pow_le_pow_right (by omega)
      have he : B-H-10+H+10=B := by omega
      nlinarith

lemma previous_scale_absorption (B H s j : ℕ) (hB : H+10 ≤ B) :
    F B s j ≤ mesh B H s (j+1)*2^H := by
  rw [next_mesh_F B H s j hB]
  exact Nat.le_mul_of_pos_right _ (by positivity)

lemma next_gain (B H s j : ℕ) (hB : H+10 ≤ B) :
    E B s (j+1)=512*mesh B H s (j+1)*2^(H+j+2) := by
  rw [mesh_E B H s (j+1) hB]
  have he : H+(j+1)+10=(H+j+2)+9 := by omega
  rw [he,pow_add]
  norm_num
  ring

end OrdinaryChainScales

end

end OAI
