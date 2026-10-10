import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Grid
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
open Finset OrdinaryNarrowGrid

def binQ (B H s j : ℕ) : ℕ := 2^(mesh B H s j)
def binStart (B H s j : ℕ) : ℕ := E B s j-mesh B H s j
def binWidth (B s j : ℕ) : ℕ := F B s j-E B s j
def binLog (B H s j : ℕ) (i : ℕ×ℕ) : ℕ := mesh B H s j+i.1

lemma mesh_le_E (B H s j : ℕ) (hB : H+10≤B) : mesh B H s j≤E B s j := by
  rw [mesh_E B H s j hB]
  exact Nat.le_mul_of_pos_right _ (by positivity)

lemma window_endpoints (B H s j : ℕ) (hB : H+10≤B) :
    binQ B H s j*2^(binStart B H s j)=2^(E B s j) ∧
    binQ B H s j*2^(binStart B H s j+binWidth B s j)=2^(F B s j) := by
  have he := mesh_le_E B H s j hB
  have hf := E_le_F B s j
  unfold binQ binStart binWidth
  rw [←pow_add,←pow_add]
  constructor <;> congr 1 <;> omega

lemma bin_log_range {B H s j : ℕ} (hB : H+10≤B) {i : ℕ×ℕ}
    (hi : i∈grid (binQ B H s j) (binStart B H s j) (binWidth B s j)) :
    E B s j≤binLog B H s j i ∧ binLog B H s j i<F B s j := by
  have hii := mem_Ico.mp (mem_product.mp hi).1
  have hme := mesh_le_E B H s j hB
  have hef := E_le_F B s j
  unfold binStart binWidth at hii
  unfold binLog
  omega

lemma bin_lower_bounds {B H s j : ℕ} {i : ℕ×ℕ}
    (hi : i∈grid (binQ B H s j) (binStart B H s j) (binWidth B s j)) :
    2^(binLog B H s j i)≤lower i ∧ upper i≤2^(binLog B H s j i+1) := by
  have hii := mem_Ico.mp (mem_product.mp hi).2
  constructor
  · unfold binLog lower
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hii.1
  · unfold binLog upper
    rw [pow_add,pow_add,pow_one]
    change (i.2+1)*2^i.1≤(binQ B H s j)*2^i.1*2
    have hh : i.2+1≤2*binQ B H s j := by omega
    nlinarith [Nat.mul_le_mul_right (2^i.1) hh]

lemma two_mul_le_two_pow {n : ℕ} (hn : 2≤n) : 2*n≤2^n := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show 2+(m+1)=(2+m)+1 by omega,pow_succ]
    have hh : 4≤2^(2+m) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤(2:ℕ)) (by omega : 2≤2+m)
    omega

lemma F_le_pow_mesh {B H s j : ℕ} (hB : 2*H+s+30≤B) :
    F B s j≤2^(mesh B H s j) := by
  let n := B-H-10+j^2+(s+19)*j
  have he : B-H-10+H+10=B := by omega
  have hn : 2≤n := by dsimp [n]; omega
  have hh : B+s+j^2+(s+21)*j≤2*n := by dsimp [n]; nlinarith
  apply Nat.pow_le_pow_right (by omega)
  exact hh.trans (two_mul_le_two_pow hn)

lemma bin_card_bound {B H s j : ℕ} (hB : 2*H+s+30≤B) :
    (grid (binQ B H s j) (binStart B H s j) (binWidth B s j)).card≤2^(2*mesh B H s j) := by
  rw [grid_card]
  have hf := F_le_pow_mesh hB (j:=j)
  have hw : binWidth B s j≤F B s j := Nat.sub_le _ _
  calc
    _ ≤ 2^(mesh B H s j)*2^(mesh B H s j) := Nat.mul_le_mul (hw.trans hf) le_rfl
    _ = _ := by rw [←pow_add]; congr 1; omega

end OrdinaryChainScales

end

end OAI
