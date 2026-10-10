import Mathlib
import OAI.Probability.BinarySweep.Conditional.MainEasyCases
import OAI.Probability.BinarySweep.YoungTheory.YoungDimensionLower
import OAI.Probability.BinarySweep.GridBounds.DenseClosing
import OAI.Probability.BinarySweep.SparseBounds.SparseNumerics
import OAI.Probability.BinarySweep.YoungTheory.YoungTranspose

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps.Young
open Irrep Signed

def minTail (μ : YoungDiagram) : ℕ := min (Fintype.card (Cell μ)-μ.rowLen 0)
  (Fintype.card (Cell μ)-μ.colLen 0)

lemma diagramF_le_rowTail (μ : YoungDiagram) (s : ℕ) (hs : 0 < s)
    (hM : Fintype.card (Cell μ) ≤ s) :
    diagramF μ  ≤  (Fintype.card (Cell μ)-μ.rowLen 0:ℕ)*Real.log s := by
  have hD : (0:ℝ) < Module.finrank ℂ (SpechtSpace μ) := by
    rw [←hilbertSpecht_finrank]
    exact_mod_cast irreducible_finrank_pos (hilbertSpecht μ)
  have hb := (specht_finrank_le_power μ).trans (Nat.pow_le_pow_left hM _)
  have hl := (Real.log_le_log_iff hD (pow_pos (Nat.cast_pos.mpr hs) _)).mpr
    (show (Module.finrank ℂ (SpechtSpace μ):ℝ) ≤
    (s:ℝ)^(Fintype.card (Cell μ)-μ.rowLen 0) by exact_mod_cast hb)
  rw [Real.log_pow] at hl
  exact hl

lemma diagramF_transpose (μ : YoungDiagram) : diagramF μ.transpose=diagramF μ := by
  unfold diagramF
  rw [←specht_finrank_transpose]

lemma minTail_orientation (μ : YoungDiagram) :
    Fintype.card (Tail μ)=minTail μ ∨ Fintype.card (Tail μ.transpose)=minTail μ := by
  have hc := Fintype.card_congr (transposeCells μ)
  rw [card_tail,card_tail,YoungDiagram.rowLen_transpose,←hc]
  exact (le_total (Fintype.card (Cell μ)-μ.rowLen 0) (Fintype.card (Cell μ)-μ.colLen 0)).elim
    (fun h => Or.inl (min_eq_left h).symm) (fun h => Or.inr (min_eq_right h).symm)

lemma diagramF_le_minTail (μ : YoungDiagram) (s : ℕ) (hs : 0 < s)
    (hM : Fintype.card (Cell μ) ≤ s) : diagramF μ ≤ (minTail μ:ℝ)*Real.log s := by
  rcases minTail_orientation μ with ht | ht
  · simpa only [←card_tail,ht] using diagramF_le_rowTail μ s hs hM
  · have hc : Fintype.card (Cell μ.transpose) ≤ s :=
      (Fintype.card_congr (transposeCells μ)).symm.trans_le hM
    simpa only [diagramF_transpose,←card_tail,ht] using diagramF_le_rowTail μ.transpose s hs hc

lemma minTail_le_diagramF (μ : YoungDiagram) :
    (minTail μ:ℝ) ≤ (2/Real.log 2)*diagramF μ := by
  have hl := log_dimension_lower_min_tail μ
  have htwo := Real.log_pos (by norm_num : (1:ℝ) < 2)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ htwo).mpr
  change Real.log 2/2*(minTail μ:ℝ) ≤ diagramF μ at hl
  nlinarith

end BinaryCoordinateSweeps.Young
namespace BinaryCoordinateSweeps
open Young Irrep Signed

lemma const_mul_rpow_eventually (C u v : ℝ) (huv : u < v) : ∀ᶠ s : ℕ in atTop,
    C*(s:ℝ)^u ≤ (s:ℝ)^v := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr huv)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop C,eventually_ge_atTop (1:ℕ)] with s hs hs1
  have hp : (0:ℝ) < s := by exact_mod_cast hs1
  calc
    _  ≤  (s:ℝ)^(v-u)*(s:ℝ)^u := mul_le_mul_of_nonneg_right hs (Real.rpow_pos_of_pos hp _).le
    _ = _ := by rw [←Real.rpow_add hp]; congr 1; ring

lemma sparse_reduction_eventually : ∀ᶠ s : ℕ in atTop,
    ∀ b r h : ℕ, ∀bits : Fin b → ℕ, gridSize bits=s → 1 ≤ b →
    (∀j,r ≤ bits j) → 400000000 ≤ (r:ℝ)*Real.log 2 →
    ∀H : PathFamily bits h, ∀μ : YoungDiagram, ∀_e : Cell μ ≃ FreeSlot H 0,
    diagramF μ < (s:ℝ)^(399/400:ℝ) →
    ¬((1+cExponent s)*diagramF μ ≤ eExponent s*h*Real.log s-pathCost H) →
    1 ≤ minTail μ ∧ h ≤ 100000*minTail μ ∧
      ((minTail μ+h:ℕ):ℝ) ≤ (s:ℝ)^(1599/1600:ℝ) := by
  filter_upwards [const_mul_rpow_eventually (80000+2/Real.log 2) (399/400) (1599/1600)
    (by norm_num)] with s hs
  intro b r h bits he hb hd hr H μ e hF hnot
  have ha := grid_parameter_allowance hb hd hr H
  rw [he] at ha
  have hLF := grid_log_lower hd
  rw [he] at hLF
  have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hL : 1 ≤ Real.log s := by nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg b)]
  have hF0 := diagramF_nonneg μ
  have hM : Fintype.card (Cell μ) ≤ s := by
    rw [Fintype.card_congr e,card_freeSlot,he]
    exact Nat.sub_le _ _
  have hp : 0 < s := he ▸ gridSize_pos bits
  have hupper := diagramF_le_minTail μ s hp hM
  have hlow := minTail_le_diagramF μ
  have hallow0 : 0 ≤ eExponent s*h*Real.log s-pathCost H := by
    apply le_trans _ ha.2.2
    unfold e0
    positivity
  have hc : cExponent s ≤ 1 := by have := ha.1; unfold c0 at this; linarith
  have hn := lt_of_not_ge hnot
  have hhL : (h:ℝ)*Real.log s < 80000*diagramF μ := by
    have hh := ha.2.2
    unfold e0 at hh
    nlinarith [mul_le_mul_of_nonneg_right hc hF0]
  have hkpos : 0 < minTail μ := by
    by_contra hk
    have hk0 : minTail μ=0 := by omega
    rw [hk0,Nat.cast_zero,zero_mul] at hupper
    have : diagramF μ=0 := le_antisymm hupper hF0
    rw [this,mul_zero] at hn
    linarith
  have hhk : h ≤ 100000*minTail μ := by
    have hr' : (h:ℝ) ≤ 100000*(minTail μ:ℝ) := by
      have hh' := hhL.trans_le (mul_le_mul_of_nonneg_left hupper (by norm_num))
      have : (h:ℝ) < 80000*minTail μ := by nlinarith
      nlinarith [show (0:ℝ) ≤ minTail μ by positivity]
    exact_mod_cast hr'
  refine ⟨hkpos,hhk,?_⟩
  have hhF : (h:ℝ) ≤ 80000*diagramF μ := by nlinarith
  have hsum : ((minTail μ+h:ℕ):ℝ) ≤ (80000+2/Real.log 2)*diagramF μ := by
    push_cast
    nlinarith
  refine hsum.trans ((mul_le_mul_of_nonneg_left hF.le ?_).trans hs)
  have := Real.log_pos (by norm_num : (1:ℝ) < 2)
  positivity

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Sparse

lemma outside_card_mul_axis {b : ℕ} (bits : Fin b → ℕ) (j : Fin b) :
    Fintype.card (GridOutside bits j)*2^bits j=gridSize bits := by
  have he := Fintype.card_congr (Equiv.piSplitAt j (fun i => Slot (bits i)))
  change Fintype.card (GridSlot bits)=Fintype.card (Slot (bits j) × GridOutside bits j) at he
  have hs : Fintype.card (Slot (bits j))=2^bits j := by simp [Slot]
  have hg : Fintype.card (GridSlot bits)=gridSize bits := by simp [GridSlot,gridSize,Slot]
  simpa only [Fintype.card_prod,hs,hg,mul_comm] using he.symm

lemma outside_inv_axis_ratio {b : ℕ} (bits : Fin b → ℕ) (j : Fin b) :
    (1:ℝ)/Fintype.card (GridOutside bits j)=(2^bits j:ℕ)/(gridSize bits:ℝ) := by
  have hp : (0:ℝ)<(2^bits j:ℕ) := by positivity
  have he : (Fintype.card (GridOutside bits j):ℝ)*(2^bits j:ℕ)=gridSize bits := by
    exact_mod_cast outside_card_mul_axis bits j
  rw [←he]
  field_simp

lemma many_axis_size_bound {b r : ℕ} {bits : Fin b → ℕ}
    (hb : 16000≤b) (hd : ∀j, r≤bits j ∧ bits j≤2*r) (j : Fin b) :
    ((2^bits j:ℕ):ℝ)≤Real.exp (Real.log (gridSize bits)/8000) := by
  have hbR : (16000:ℝ)≤b := by exact_mod_cast hb
  have hr : 0≤(r:ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hl := grid_log_lower (fun j => (hd j).1)
  have ha := mul_le_mul_of_nonneg_right hbR hr
  have hj := mul_le_mul_of_nonneg_right (show (bits j:ℝ)≤2*r by exact_mod_cast (hd j).2)
    (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  have hp : (0:ℝ)<((2^bits j:ℕ):ℝ) := by positivity
  rw [←Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  linarith

lemma many_collision_base_eventually : ∀ᶠ s : ℕ in atTop,
    ∀ b r h k : ℕ, ∀ bits : Fin b → ℕ, gridSize bits=s → 16000≤b →
    (∀j, r≤bits j ∧ bits j≤2*r) → 1≤(r:ℝ)*Real.log 2 →
    ((k+h:ℕ):ℝ)≤(s:ℝ)^(1599/1600:ℝ) →
    ((k+h:ℕ):ℝ)*(∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j))≤
      Real.exp (-Real.log s/4000) := by
  filter_upwards [log_le_small_rpow_eventually (by norm_num : (0:ℝ)<1/4000)] with s hs
  intro b r h k bits he hb hd hr hk
  have sp : (0:ℝ)<s := by rw [←he]; exact_mod_cast gridSize_pos bits
  have hl := grid_log_lower (fun j => (hd j).1)
  rw [he] at hl
  have hbL : (b:ℝ)≤Real.log s := by nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg b)]
  have hbE : (b:ℝ)≤Real.exp (Real.log s/4000) := by
    refine (hbL.trans hs).trans_eq ?_
    rw [Real.rpow_def_of_pos sp]
    congr 1
    ring
  have hsum : (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j))≤
      (b:ℝ)*Real.exp (Real.log s/8000)/(s:ℝ) := by
    calc
      _ ≤ ∑_j : Fin b, Real.exp (Real.log s/8000)/(s:ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [outside_inv_axis_ratio,he]
        exact div_le_div_of_nonneg_right (by simpa only [he] using many_axis_size_bound hb hd j) sp.le
      _ = _ := by simp; ring
  have hkE : ((k+h:ℕ):ℝ)≤Real.exp ((1599/1600:ℝ)*Real.log s) := by
    simpa only [Real.rpow_def_of_pos sp,mul_comm] using hk
  calc
    _ ≤ Real.exp ((1599/1600:ℝ)*Real.log s)*
        (Real.exp (Real.log s/4000)*Real.exp (Real.log s/8000)/(s:ℝ)) := by
      apply mul_le_mul hkE
      · exact hsum.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbE (Real.exp_pos _).le) sp.le)
      · positivity
      · positivity
    _ = _ := by
      rw [←Real.exp_log sp,←Real.exp_add,←Real.exp_sub,←Real.exp_add]
      simp only [Real.log_exp]
      congr 1
      ring

end BinaryCoordinateSweeps

end

end OAI
