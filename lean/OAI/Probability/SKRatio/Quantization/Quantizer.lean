import Mathlib
import OAI.Probability.SKRatio.Matrices.GaussianSquareTails
import OAI.Probability.SKRatio.Variational.CompactField
import OAI.Probability.SKRatio.Quantization.IntervalBins

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real Set
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

def gridCut (R : ℝ) (N : ℕ) (j : Fin (N+1)) : ℝ := -R+(2*R/N)*(j.val:ℝ)

def gridRep (R : ℝ) (N : ℕ) (j : Fin (N+2)) : ℝ := -R+(2*R/N)*((min j.val N:ℕ):ℝ)

def gridQuant (R : ℝ) (N : ℕ) (x : ℝ) : ℝ := gridRep R N (intervalBin (gridCut R N) x)

lemma gridCut_strictMono {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) :
    StrictMono (gridCut R N) := by
  intro i j hij
  have hc : (i.val:ℝ)<(j.val:ℝ) := by exact_mod_cast hij
  exact add_lt_add_right (mul_lt_mul_of_pos_left hc (by positivity : 0<2*R/(N:ℝ))) _

lemma gridCut_zero (R : ℝ) (N : ℕ) : gridCut R N 0= -R := by simp [gridCut]
lemma gridCut_last (R : ℝ) {N : ℕ} (hN : 0<N) : gridCut R N (Fin.last N)=R := by
  simp only [gridCut,Fin.val_last,div_mul_cancel₀ _ ((Nat.cast_ne_zero.mpr hN.ne' : (N:ℝ)≠0))]
  ring
lemma gridRep_zero (R : ℝ) (N : ℕ) : gridRep R N 0= -R := by simp [gridRep]
lemma gridRep_last (R : ℝ) {N : ℕ} (hN : 0<N) : gridRep R N (Fin.last (N+1))=R := by
  simp only [gridRep,Fin.val_last,min_eq_right (show N≤N+1 from by omega),div_mul_cancel₀ _ ((Nat.cast_ne_zero.mpr hN.ne' : (N:ℝ)≠0))]
  ring
lemma gridRep_middle (R : ℝ) {N : ℕ} (j : Fin (N+2)) (hj : j.val<N+1) :
    gridRep R N j=gridCut R N ⟨j.val,hj⟩ := by
  simp only [gridRep,gridCut,min_eq_left (show j.val≤N from by omega)]

lemma gridRep_abs_le {R : ℝ} (hR : 0≤R) {N : ℕ} (hN : 0<N) (j : Fin (N+2)) :
    |gridRep R N j|≤R := by
  have h0 : (0:ℝ)≤(min j.val N:ℕ) := Nat.cast_nonneg _
  have h1 : ((min j.val N:ℕ):ℝ)≤(N:ℝ) := by exact_mod_cast min_le_right j.val N
  have hδ : 0≤2*R/(N:ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left h1 hδ
  rw [div_mul_cancel₀ _ ((Nat.cast_ne_zero.mpr hN.ne' : (N:ℝ)≠0))] at hh
  unfold gridRep
  exact abs_le.mpr ⟨by nlinarith [mul_nonneg hδ h0],by linarith⟩

lemma gridQuant_left {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) {x : ℝ} (hx : x≤-R) :
    gridQuant R N x= -R := by
  unfold gridQuant
  have he : intervalBin (gridCut R N) x=0 := (intervalBin_eq_zero (by omega)
    (gridCut_strictMono hR hN) x).mpr (by simpa [gridCut] using hx)
  rw [he,gridRep_zero]

lemma gridQuant_right {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) {x : ℝ} (hx : R<x) :
    gridQuant R N x=R := by
  unfold gridQuant
  have he : intervalBin (gridCut R N) x=Fin.last (N+1) := (intervalBin_eq_last (by omega)
    (gridCut_strictMono hR hN) x).mpr (by simpa only [Nat.add_sub_cancel,gridCut,div_mul_cancel₀ _ ((Nat.cast_ne_zero.mpr hN.ne' : (N:ℝ)≠0)),show -R+2*R=R by ring] using hx)
  rw [he,gridRep_last R hN]

lemma gridQuant_middle {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) {x : ℝ}
    (hxL : -R<x) (hxU : x≤R) : |x-gridQuant R N x|≤2*R/N := by
  let j := intervalBin (gridCut R N) x
  have hj0 : j≠0 := fun hh => not_le.mpr hxL (by
    simpa only [gridCut,Fin.val_mk,Nat.cast_zero,mul_zero,add_zero] using
      (intervalBin_eq_zero (by omega) (gridCut_strictMono hR hN) x).mp hh)
  have hjLast : j≠Fin.last (N+1) := fun hh => not_lt.mpr hxU (by
    simpa only [Nat.add_sub_cancel,gridCut,Fin.val_mk,div_mul_cancel₀ _ ((Nat.cast_ne_zero.mpr hN.ne' : (N:ℝ)≠0)),
      show -R+2*R=R by ring] using
      (intervalBin_eq_last (by omega) (gridCut_strictMono hR hN) x).mp hh)
  have hj0' : 0<j.val := by have hh : j.val≠0 := fun he => hj0 (Fin.ext he); omega
  have hjN : j.val<N+1 := by
    have hb := j.isLt
    have hh : j.val≠N+1 := fun he => hjLast (Fin.ext he)
    omega
  have hbounds := (intervalBin_eq_middle (gridCut_strictMono hR hN) x j hj0' hjN).mp rfl
  change |x-gridRep R N j|≤_
  rw [gridRep_middle R j hjN]
  simp only [gridCut] at hbounds ⊢
  have hcast : ((j.val-1:ℕ):ℝ)=(j.val:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  rw [hcast] at hbounds
  rw [abs_of_nonpos (sub_nonpos.mpr hbounds.2)]
  linarith only [hbounds.1]

lemma gridQuant_square_error {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) (x : ℝ) :
    (x-gridQuant R N x)^2≤(2*R/N)^2 + squareTail R x := by
  by_cases hxL : x≤-R
  · rw [gridQuant_left hR hN hxL]
    by_cases he : x= -R
    · simp only [he,sub_self,zero_pow (by decide : (2:ℕ)≠0)]
      exact add_nonneg (sq_nonneg _) (squareTail_nonneg _ _)
    · have hlt : x < -R := lt_of_le_of_ne hxL he
      have hx : R < |x| := by rw [abs_of_neg (by linarith)]; linarith
      rw [squareTail,ite_eq_left hx]
      nlinarith [sq_nonneg (2*R/(N:ℝ))]
  · by_cases hxU : x≤R
    · have hb := gridQuant_middle hR hN (lt_of_not_ge hxL) hxU
      have hs : (x-gridQuant R N x)^2≤(2*R/N)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤2*R/(N:ℝ))).mpr hb
      linarith [squareTail_nonneg R x]
    · have hx := lt_of_not_ge hxU
      rw [gridQuant_right hR hN hx,squareTail,ite_eq_left (by rw [abs_of_pos (hR.trans hx)]; exact hx)]
      nlinarith [sq_nonneg (2*R/(N:ℝ))]

lemma measurable_gridQuant {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N) :
    Measurable (gridQuant R N) :=
  (measurable_of_countable (gridRep R N)).comp (measurable_intervalBin (by omega) (gridCut_strictMono hR hN))

lemma gridQuant_compact_error {δ R : ℝ} (_ : 0<δ) (hR : 0<R) {N : ℕ} (hN : 0<N)
    (hmesh : 2*R/(N:ℝ)<δ)
    (htail : ∀ x : ℝ, R≤|x| → |tanh x-tanh (if 0≤x then R else -R)|<δ) (x : ℝ) :
    dist (compactWeight x) (compactWeight (gridQuant R N x))<δ := by
  change |w x-w (gridQuant R N x)|<δ
  rw [w,w,sub_sub_sub_cancel_left,abs_sub_comm]
  change |tanh x-tanh (gridQuant R N x)|<δ
  by_cases hxL : x≤-R
  · rw [gridQuant_left hR hN hxL]
    have hh := htail x (by rw [abs_of_neg (by linarith)]; linarith)
    simpa only [ite_eq_right (show ¬0≤x by linarith)] using hh
  · by_cases hxU : x≤R
    · exact ((Calculus.tanh_lipschitz_abs _ _).trans
        (gridQuant_middle hR hN (lt_of_not_ge hxL) hxU)).trans_lt hmesh
    · have hx := lt_of_not_ge hxU
      rw [gridQuant_right hR hN hx]
      have hh := htail x (by rw [abs_of_pos (hR.trans hx)]; exact hx.le)
      simpa only [ite_eq_left (hR.trans hx).le] using hh

end SKRatio.Bins

end

end OAI
